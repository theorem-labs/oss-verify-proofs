(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 408 of its 431 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a9_s1_k.v, with its module paths and module names changed; 231 of its 293 lines of code are new or changed and 369 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): the five PROGRAM call sites of segment
   B7 of reac_segconf_parse_file's walk (the header branch, HDR 0x883b4 -> TAIL / SEG, and the cuts HREF, REFTL, CLR;
   the B7 segment lane of the image-B G3 walk owner, 2026-10-30). VERIFY rule 1j-bis: one closed lemma per call site, showing that the
   site supplies the callee contract's premises besides afn_pre:
     refuse (lib/B/Prog/refuse_c.v) at image B's numbers (lit := seg_litA_rc, gotw := gotwA = 0xa3e98,
       guard := guardA = 0x5ff838, SegInstB.v): b7_refuse_call, from the one rule b7_refuse_site_ok:
         b7_refuse_site_885f8  F_notclosed / F_after / F_outside / F_unknown, args = [AS x], x in buf
         b7_refuse_site_887d8  F_toolong (a4 = 15) / F_bound (a4 = 32), args = [AS name; AI k]
         b7_refuse_site_88c98  F_noname, args = []
     trim (lib/B/Prog/trim_c.v): b7_trim_call, from b7_trim_site_ok:
         b7_trim_site_884e8    a0 = s7 + 1 = lp + 1, the string slice 1 ci (pf_tline s o)
         b7_trim_site_8878c    a0 = s3 + 7 = body + 7, the string skipn 7 body
   ADAPTED from the image-A G3 walk owner's image-A A7 segment lane lib/A/Prog/pf_a7_s.v (commit 980fbe9c6015): the
   shared rules (b7_refuse_site_ok, b7_trim_site_ok and the facts they use) are A's text over image B's pf_pieces.v;
   the site lemmas are image B's sites (B has three refuse sites where A has four: plan section 7, "B7 differs in
   its joins"). Where each premise comes from: pf_a7_s.v's head comment holds word for word (buf is F + 0x40,
   512 bytes, 8-aligned; the block c and the class-5 frame are disjoint, YCbq.sep_block_frame; lineno = ln + 1 is
   bounded by reader_pre's 65535; every format is in PARSE_FILE_LITS; sa_ssp is pf_obj's at the site's state;
   sa_room and the event bound from the journal and pf_cx).
   Section hypotheses: none. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B7_f pf_seg_B7_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* a list of the five formats, decided by trying each position *)
Ltac b7_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* rounding up to the next multiple of 8 stays below an 8-aligned bound *)
Lemma b7_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
  intros x M H1 H2.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
  lia.
Qed.

(* reader_pre's text bound (length s <= 65535)%nat, in Z; the nat literal is too large for lia to read *)
Lemma b7_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
  intros m H. apply Nat2Z.inj_le in H.
  assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
  rewrite E in H. exact H.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* what a refuse site of A7 puts in the variadic registers a3 .. a7: each %s argument a C string in buf, each
   integer argument below 2 ^ 31 (refuse_pre's sa_va_args, in the shape A7's sites have it) *)
Fixpoint b7_va (v : pfv) (pos : Z) (rd : reader) (rs : list word) (xs : list arg) : Prop :=
  match xs, rs with
  | [], _ => True
  | AS s :: xs', r :: rs' =>
      (exists q, r = w64 q /\ sa_str rd q s /\ pf_inb (b7_buf v pos) q s) /\ b7_va v pos rd rs' xs'
  | AI z :: xs', r :: rs' => (0 <= z < 2 ^ 31 /\ bv_unsigned r = z) /\ b7_va v pos rd rs' xs'
  | _ :: _, [] => False
  end.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** What each callee's contract asks besides afn_pre *)
(* refuse_contract at image A's numbers, at a call with a0 = c, a1 = lineno = ln + 1, a2 = f's literal,
   c holding cf *)
Definition b7_refuse_call (v : pfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memc : word -> option byte) (regs : bvmap 5 word) (cf : rconf) (ln : Z) (f : list Z) (args : list arg)
  : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 (p_c v) /\ 0 <= p_c v < 2 ^ 64 /\
  getr regs 11 = w64 (ln + 1) /\ 0 <= ln + 1 < 2 ^ 64 /\
  getr regs 12 = w64 (seg_litA_rc f) /\ 0 <= seg_litA_rc f < 2 ^ 64 /\
  refuse_pre SEGS B seg_litA_rc gotwA guardA lyc Sc regs (rdW Wc memc) (p_c v) (ln + 1) (seg_litA_rc f)
    [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] cf (ln + 1) f args /\
  sa_room Sc /\ st_nev Sc + EV_refuse <= EV_MAX.
(* trim_contract at a call with a0 = p, the C string s at p *)
Definition b7_trim_call (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (regs : bvmap 5 word) (p : Z) (s : list Z) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\
  trim_pre SEGS B lyc Sc Wc memc regs p s /\
  st_nev Sc + EV_trim <= EV_MAX.

(** ** The facts every site shares *)
(* where buf lies: inside the class-5 frame, below the allocator's ceiling, its end 8-aligned *)
Lemma b7_buf_rng : forall v pos lyc Sc Wc memc mdc, b7_st B v pos lyc Sc Wc memc mdc ->
  4096 < b7_buf v pos /\ b7_buf v pos + 512 <= alloc_ceiling /\ (b7_buf v pos + 512) mod 8 = 0 /\
  pf_F v pos <= b7_buf v pos /\ b7_buf v pos + 512 <= pf_F v pos + 2048.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  destruct (b7_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D.
  unfold b7_buf, PF_O_BUF.
  split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* the frame's room for refuse's class-0 frame, and the events: the journal from parse_file's entry *)
Lemma b7_room_ev : forall v pos lyc Sc Wc memc mdc, b7_st B v pos lyc Sc Wc memc mdc ->
  sa_room Sc /\ st_nev Sc <= EV_MAX.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  pose proof H as [HCX HJ _ _ _ _].
  pose proof HCX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HROOM & HEV).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfr & Hnev & _).
  unfold sa_room_n in HROOM. unfold EV_reac_segconf_parse_file in HEV.
  split; [|lia].
  unfold sa_room. rewrite Hfr, length_app. cbn [length]. lia.
Qed.

(* a %s argument in buf is apart from the three ranges refuse_pre forbids *)
Lemma b7_apart : forall v pos lyc Sc Wc memc mdc (k : nat) sp q s,
  b7_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat -> pf_inb (b7_buf v pos) q s ->
  sa_apart_all q (seg_spec.cstr_span q s)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)].
Proof.
  intros v pos lyc Sc Wc memc mdc k sp q s H Hk [HI1 HI2].
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  destruct HSTK as (_ & _ & Hceil & _).
  destruct (b7_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & Hb8 & HFb & HbF).
  pose proof (b7_round8 (q + Z.of_nat (length s) + 1) (b7_buf v pos + 512) ltac:(lia) Hb8) as HR.
  assert (HSP : q + seg_spec.cstr_span q s <= b7_buf v pos + 512) by (unfold seg_spec.cstr_span; lia).
  (* the block c and the class-5 frame do not meet *)
  pose proof HOBJ as (_ & _ & _ & _ & (b & m & Hin & Hb & Hm) & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hin
    (b7_fin B v pos lyc Sc Wc memc mdc H)) as Hsep.
  pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hm; lia)) as [_ Hrq].
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite b7_fb5 in Hsep.
  replace (frame_addr lyc 5 pos) with (pf_F v pos) in Hsep by (unfold pf_F; rewrite HLY; reflexivity).
  assert (HAP : q + seg_spec.cstr_span q s <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= q)
    by (destruct Hsep as [Hs|Hs]; [right|left]; lia).
  rewrite HLY.
  unfold sa_apart_all, seg_spec.refusal_addr, seg_spec.RC_REFUSAL, seg_spec.RC_REFUSAL_LEN,
    seg_spec.RC_REFUSED, seg_spec.SEG_C_SIZE in *.
  apply Forall_cons; [cbn [fst snd]; lia|].
  apply Forall_cons; [cbn [fst snd]; lia|].
  apply Forall_cons; [cbn [fst snd]; lia|].
  apply Forall_nil.
Qed.

(* the variadic registers of an A7 site give sa_va_args and refuse_va_locs (the frame arm) *)
Lemma b7_va_ok : forall v pos lyc Sc Wc memc mdc (k : nat) sp rs xs,
  b7_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat ->
  b7_va v pos (rdW Wc memc) rs xs ->
  sa_va_args (rdW Wc memc)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)] rs xs /\
  refuse_va_locs (fun q n => sa_heap B lyc Sc q n \/ sa_fframe lyc Sc q n) rs xs.
Proof.
  intros v pos lyc Sc Wc memc mdc k sp rs xs H Hk.
  revert rs. induction xs as [|x xs IH]; intros rs HV.
  - destruct rs; split; exact I.
  - destruct rs as [|r rs]; [destruct x; cbn in HV; contradiction|].
    destruct x as [s|z]; cbn [b7_va] in HV; destruct HV as [Hx HV]; destruct (IH rs HV) as [IH1 IH2].
    + destruct Hx as (q & -> & HS & HI).
      pose proof HI as [HI1 HI2].
      destruct (b7_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & _).
      pose proof alloc_ceiling_lt as HC.
      assert (EQ : bv_unsigned (w64 q) = q).
      { unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
      cbn [sa_va_args refuse_va_locs sa_va_arg]. rewrite EQ.
      split; [split; [|exact IH1] | split; [|exact IH2]].
      * split; [lia|]. split; [exact HS|].
        split; [apply (Nat.le_trans _ 512%nat); [lia | apply Nat.leb_le; vm_compute; reflexivity]|].
        split; [exact (b7_addr_buf B v pos lyc Sc Wc memc mdc q (Z.of_nat (length s) + 1) H HI1
                  ltac:(lia) ltac:(lia))|].
        exact (b7_apart v pos lyc Sc Wc memc mdc k sp q s H Hk HI).
      * right. exact (b7_fframe_buf B v pos lyc Sc Wc memc mdc q (Z.of_nat (length s) + 1) H HI1
          ltac:(lia) ltac:(lia)).
    + cbn [sa_va_args refuse_va_locs sa_va_arg].
      split; [split; [exact Hx | exact IH1] | exact IH2].
Qed.

(** ** refuse: the rule the four sites share *)
Lemma b7_refuse_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n f args,
  b7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  In f seg_spec.REFUSE_FORMATS -> In f PARSE_FILE_LITS ->
  seg_spec.conv_kinds f = map seg_spec.arg_is_s args ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  b7_va v pos (rdW Wc memc) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args ->
  b7_refuse_call v lyc Sc Wc memc regs cf ln f args.
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n f args H HRC HCNT HMID HFRM HINF HINL HKND R10 R11 R12 HVA.
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HCX as (_ & _ & _ & HcB & _ & _ & _ & _ & (fe & HPRE) & _ & _).
  destruct HPRE as ((C0 & C16 & _ & _ & _ & _ & _ & _ & _ & _ & LS & _) & _).
  pose proof HOBJ as (_ & _ & _ & Ac & Hc & _ & LITS & HROD & SSP).
  pose proof HJ as (HAR & _).
  destruct HMID as (_ & _ & Hle & _ & Hlnd & Hlno).
  pose proof (LITS f HINL) as HLF.
  pose proof HLF as (Hfp & _ & Hpin & _).
  pose proof (Hpin lyc Sc Wc memc mdc HAR) as (_ & Hfp63 & _).
  pose proof HRC as (bs & _ & (_ & _ & _ & _ & HK8 & _)).
  destruct (b7_room_ev v pos lyc Sc Wc memc mdc H) as [HROOM HEV].
  destruct (b7_va_ok v pos lyc Sc Wc memc mdc (length (rc_refusal cf)) (spZ regs) _ args H HK8 HVA)
    as [HVA1 HVA2].
  pose proof (b7_le65535 _ LS) as LSZ.
  assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
  unfold b7_refuse_call.
  split; [exact HROD|]. split; [exact R10|]. split; [exact HcB|].
  split; [exact R11|]. split; [lia|]. split; [exact R12|]. split; [lia|].
  split; [|split; [exact HROOM | unfold EV_refuse; lia]].
  unfold refuse_pre.
  split; [exact C0|]. split; [exact C16|]. split; [exact HRC|]. split; [exact Hc|]. split; [exact Ac|].
  split; [destruct HCNT as [HC1 _]; lia|].
  split; [exact HLN|]. split; [reflexivity|].
  split; [exact HINF|]. split; [exact HKND|].
  split; [lia|]. split; [reflexivity|]. split; [exact HLF|].
  split; [exact HVA1|]. split; [exact HVA2|].
  split; [exact HFRM|]. split; [exact SSP|].
  intros x Hx. apply LITS. unfold PARSE_FILE_LITS. apply in_or_app. right. exact Hx.
Qed.

(** ** refuse: the three sites of B7 (VERIFY rule 1j-bis) *)
(* 0x885f8 (CREF, the shared header call): refuse(c, lineno, f, x) for f one of F_notclosed (a2 at 0x884a4),
   F_after (0x883f0), F_outside (B9, 0x885e8) through HREF 0x885ec (a3 = s7 at 0x885f4), and F_unknown (0x8850c,
   a3 = s3 = the body at 0x88518, `j 0x885f8` at 0x8851c); the string x at a3 in buf *)
Lemma b7_refuse_site_885f8 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n f xp x,
  b7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  f = F_notclosed \/ f = F_after \/ f = F_outside \/ f = F_unknown ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  getr regs 13 = w64 xp ->
  sa_str (rdW Wc memc) xp x -> pf_inb (b7_buf v pos) xp x ->
  b7_refuse_call v lyc Sc Wc memc regs cf ln f [AS x].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n f xp x H HRC HCNT HMID HFRM HF R10 R11 R12 R13 HS HI.
  apply (b7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n f _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 |].
  - unfold seg_spec.REFUSE_FORMATS. destruct HF as [-> | [-> | [-> | ->]]]; b7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. destruct HF as [-> | [-> | [-> | ->]]]; b7_in.
  - cbn [map seg_spec.arg_is_s]. destruct HF as [-> | [-> | [-> | ->]]]; reflexivity.
  - cbn [b7_va]. split; [|exact I]. exists xp. split; [exact R13|]. split; [exact HS | exact HI].
Qed.

(* 0x887d8 (REFTL): refuse(c, lineno, F_toolong, name, 15) (a2 at 0x887c4, a4 = 15 at 0x887c8) or
   refuse(c, lineno, F_bound, name, 32) (B8a, 0x88d58-0x88d64); a3 = s7 = the name at 0x887d4 *)
Lemma b7_refuse_site_887d8 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n f k np name,
  b7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  (f = F_toolong /\ k = 15) \/ (f = F_bound /\ k = 32) ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  getr regs 13 = w64 np -> getr regs 14 = w64 k ->
  sa_str (rdW Wc memc) np name -> pf_inb (b7_buf v pos) np name ->
  b7_refuse_call v lyc Sc Wc memc regs cf ln f [AS name; AI k].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n f k np name H HRC HCNT HMID HFRM HF R10 R11 R12 R13 R14 HS HI.
  assert (Hk : 0 <= k < 2 ^ 31) by (destruct HF as [[_ ->] | [_ ->]]; lia).
  apply (b7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n f _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 |].
  - unfold seg_spec.REFUSE_FORMATS. destruct HF as [[-> _] | [-> _]]; b7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. destruct HF as [[-> _] | [-> _]]; b7_in.
  - cbn [map seg_spec.arg_is_s]. destruct HF as [[-> _] | [-> _]]; reflexivity.
  - cbn [b7_va]. split; [exists np; split; [exact R13|]; split; [exact HS | exact HI]|].
    split; [|exact I]. split; [exact Hk|]. rewrite R14. unfold w64. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* 0x88c98 (noname): refuse(c, lineno, F_noname) (a2 at 0x88c8c), no variadic argument *)
Lemma b7_refuse_site_88c98 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n,
  b7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc F_noname) ->
  b7_refuse_call v lyc Sc Wc memc regs cf ln F_noname [].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n H HRC HCNT HMID HFRM R10 R11 R12.
  apply (b7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n F_noname _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 | exact I].
  - unfold seg_spec.REFUSE_FORMATS. b7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. b7_in.
  - reflexivity.
Qed.

(** ** trim: the rule the two sites share *)
Lemma b7_trim_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) p s,
  b7_st B v pos lyc Sc Wc memc mdc ->
  getr regs 10 = w64 p -> sa_str (rdW Wc memc) p s -> pf_inb (b7_buf v pos) p s ->
  b7_trim_call lyc Sc Wc memc regs p s.
Proof.
  intros v pos lyc Sc Wc memc mdc regs p s H R10 HS [HI1 HI2].
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  destruct (b7_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & _).
  destruct (b7_room_ev v pos lyc Sc Wc memc mdc H) as [_ HEV].
  pose proof alloc_ceiling_lt as HC.
  pose proof (b7_addr_buf B v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H HI1 ltac:(lia) ltac:(lia))
    as HA.
  pose proof HA as (_ & _ & _ & HRA & _).
  unfold b7_trim_call.
  split; [exact HROD|]. split; [exact R10|]. split; [lia|].
  split; [|unfold EV_trim; lia].
  unfold trim_pre.
  split; [lia|]. split; [exact HS|]. split; [exact HA|].
  split; [|lia].
  left. split; [|exact HRA].
  exact (b7_fframe_buf B v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H HI1 ltac:(lia) ltac:(lia)).
Qed.

(** ** trim: the two sites of B7 (VERIFY rule 1j-bis) *)
(* 0x884e8: trim(line + 1) after `*close = 0` (0x884dc): the line's bytes 1 .. ci, at lp + 1 in buf
   (0x884e4 `addi a0,s7,1`) *)
Lemma b7_trim_site_884e8 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) o lp ci,
  b7_st B v pos lyc Sc Wc memc mdc ->
  pf_inb (b7_buf v pos) lp (pf_tline (p_s v) o) -> hd0 (pf_tline (p_s v) o) = LBR ->
  getr regs 10 = w64 (lp + 1) ->
  sa_str (rdW Wc memc) (lp + 1) (slice 1 ci (pf_tline (p_s v) o)) ->
  b7_trim_call lyc Sc Wc memc regs (lp + 1) (slice 1 ci (pf_tline (p_s v) o)).
Proof.
  intros v pos lyc Sc Wc memc mdc regs o lp ci H [HI1 HI2] HL R10 HS.
  apply (b7_trim_site_ok v pos lyc Sc Wc memc mdc regs _ _ H R10 HS).
  destruct (pf_tline (p_s v) o) as [|x l]; [cbn in HL; discriminate|].
  unfold pf_inb. split; [lia|].
  unfold slice. rewrite length_firstn, length_skipn. cbn [length] in HI2 |- *. lia.
Qed.

(* 0x8878c: trim(body + 7) after the keyword and its blank (a0 = s3 + 7 from 0x8876c): the body's bytes from 7 on,
   at bp + 7 in buf *)
Lemma b7_trim_site_8878c : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) o ci bp,
  b7_st B v pos lyc Sc Wc memc mdc ->
  pf_inb (b7_buf v pos) bp (b7_body (pf_tline (p_s v) o) ci) ->
  strncasecmp (b7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  getr regs 10 = w64 (bp + 7) ->
  sa_str (rdW Wc memc) (bp + 7) (skipn 7 (b7_body (pf_tline (p_s v) o) ci)) ->
  b7_trim_call lyc Sc Wc memc regs (bp + 7) (skipn 7 (b7_body (pf_tline (p_s v) o) ci)).
Proof.
  intros v pos lyc Sc Wc memc mdc regs o ci bp H [HI1 HI2] HK R10 HS.
  apply (b7_trim_site_ok v pos lyc Sc Wc memc mdc regs _ _ H R10 HS).
  pose proof (b7_kw_len7 _ (b7_body_nul (pf_tline (p_s v) o) ci) HK) as H7.
  unfold pf_inb. rewrite length_skipn. lia.
Qed.

End e.
End f.
End d.
