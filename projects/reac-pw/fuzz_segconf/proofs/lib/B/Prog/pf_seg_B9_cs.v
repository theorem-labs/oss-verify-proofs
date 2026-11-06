(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the boundary states and segment statements of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86530), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (the CL_*_stmtX statements: from a point of the function to its return, under the entry's context) and A/ACf5.v (rtcx, rt_base: the entry's facts bundled once). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths, module names, addresses and numbers changed; 469 of its 518 lines of code are new or changed and 289 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_defs.v, with its module paths and module names changed; 408 of its 431 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a9_s1_k.v, with its module paths and module names changed; 231 of its 293 lines of code are new or changed and 369 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the PROGRAM call
   sites of segment B9 of reac_segconf_parse_file's walk (the key branch, KEY 0x883f8 -> ...; KREF 0x889a0 -> TAIL;
   a B9 sub-lane of the image-B G3 walk owner, 2026-10-30). proves no function (kind: segment lemma of
   reac_segconf_parse_file's walk: call-site premises of segment B9, image B). ADAPTED from the image-A G3 walk owner's image-A
   file lib/A/Prog/pf_a7_s.v (commit a78dafc7ecfa, the image-A A7 segment lane), with a7_ renamed b9_, over
   image B's pf_pieces.v and pf_seg_B9_c.v's b9_st, and specialized to B9's program calls (VERIFY rule 1j-bis,
   one closed lemma per call site, showing that the site supplies the callee
   contract's premises). Each lemma below is stated over a state of the segment that satisfies b9_st, plus the
   registers and the argument data of its site, and concludes everything the callee's contract asks besides afn_pre
   (which the call rule cl_callSF builds from the journal):
     refuse (lib/B/Prog/refuse_c.v) at image B's numbers (lit := seg_litA_rc, gotw := gotwA = 0xa3e98,
       guard := guardA = 0x5ff838, RLO_A 0xa1c60, RHI_A 0xa3f08; SegInstB.v): b9_refuse_call -- arodata_okP, the
       three argument registers with their ranges, refuse_pre, sa_room, the event bound.
         b9_refuse_site_kref  KREF 0x889a0 (pf_pieces.v INV_KREF / pf_kref): a0 = c (slot 0xc8), a1 = s6 =
                              ln + 1, a2 = f's literal (F_knock 0x21980 at 0x8898c, F_nokey 0x21a40 at 0x885cc,
                              F_badignore from B12), a3 = slot 0x40 = cur_name (F + 0x20, holding nm by pf_nm),
                              a4 = val (slot 0x70) or the key (s7), a C string in buf; args = [AS nm; AS x].
       from the one rule b9_refuse_site_ok.
     trim (lib/B/Prog/trim_c.v): b9_trim_call -- arodata_okP, a0 with its range, trim_pre, the event bound.
         b9_trim_site_ok      any C string s at p in buf with a0 = p: B9's trim(line) at 0x88424 (a0 = s7, after
                              `sb zero,0(s8)` at 0x8841c) and trim(eq + 1) at 0x88434.
   No instruction is walked here.

   WHERE EACH PREMISE COMES FROM.
   - A string a site passes lies in parse_file's buf[512] (pf_inb) or is cur_name (pf_nm: at most 15 bytes and its
     NUL in the 16 bytes at F + 0x20): its bytes and NUL are addressable with their shadow mapped
     (pf_seg_B9_c.v b9_addr_buf / b9_addr_cn: pf_shb's cells 8..71 / 4..5 are 0 under PF_SC_LINE), and it lies in
     the LIVE class-5 side-stack frame (b9_fframe_buf / b9_fframe_cn), which is refuse_va_locs' frame arm and
     trim_pre's sa_dst frame arm.
   - refuse_pre's sa_va_args keeps each %s argument's read span (seg_spec.cstr_span: up to the next 8-byte
     boundary) apart from [ly_stk_lo ly, sp), the slot refusal[n] and c->refused. buf and cur_name both end
     8-aligned (F mod 32 = 0; buf = F + 0x40, 512 bytes; cur_name = F + 0x20, 16 bytes), so the span stays inside
     the object and so inside the frame (b9_apart_frame); the frame is below alloc_ceiling <= ly_stk_lo ly (the
     journal's astk_ok at parse_file's entry layout, which is the cut's); the slot (n <= 8 by rconf_enc) and
     c->refused lie in the block c, and the block c and the class-5 frame are disjoint (YCbq.sep_block_frame, from
     AR_laws' al_sep).
   - c: c <> 0 and 16-aligned from reader_pre (pf_cx), sa_heap / sa_addr of the block and c's registers' range from
     pf_obj / pf_cx; c holds cf (the cut's pf_st); rc_refused cf + 1 < 2 ^ 32 from pf_cnt cf 0.
   - the line: lineno = ln + 1 (s6) is pf_lctx's line count at the next line, at most the text's length, which
     reader_pre bounds by 65535.
   - the format: In f REFUSE_FORMATS, In f PARSE_FILE_LITS and its conversion kinds by computation (b9_kref_kinds:
     F_knock, F_nokey and F_badignore each read two strings, F_knock's second as %.24s); sa_lit and refuse's own
     literals (REFUSE_LITS, the tail of PARSE_FILE_LITS) from pf_obj; the format's address below 2 ^ 63 from its
     sa_pinned at the cut's AR state.
   - printf's machine: sa_frm0 is the walk's (a premise); sa_ssp rd gotwA guardA is pf_obj's last conjunct AT THE
     SITE'S OWN STATE, so no Section hypothesis is taken here.
   - sa_room Sc and the event bound: the journal's frames clause (frames Sc = [(5, pos)] ++ frames S) and events
     clause (st_nev Sc <= st_nev S + 0) with pf_cx's sa_room_n 2 S and its event bound.
   POSITIONAL NAMES carried from the A file, checked against image B: refuse_pre's and trim_pre's conjunct order and
   reader_pre's 11th conjunct (length s <= 65535) in B's refuse_c.v / trim_c.v / reac_segconf_parse_file_c.v (the
   derived copies, same text); the format literals by seg_litA_rc (SegInstB.v), no address is named in a statement.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B9_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* a list of formats, decided by trying each position *)
Ltac b9_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* rounding up to the next multiple of 8 stays below an 8-aligned bound *)
Lemma b9_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
  intros x M H1 H2.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
  lia.
Qed.

(* reader_pre's text bound (length s <= 65535)%nat, in Z; the nat literal is too large for lia to read *)
Lemma b9_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
Proof.
  intros m H. apply Nat2Z.inj_le in H.
  assert (E : Z.of_nat 65535%nat = 65535) by (vm_compute; reflexivity).
  rewrite E in H. exact H.
Qed.

(* the three formats of the shared key refusal KREF each read two strings (by computation): F_knock
   "[segment %s] knock ... (it says '%.24s')", F_nokey "[segment %s] has no key '%s' ...", F_badignore
   "[segment %s] ignore = '%s' is not yes|no" *)
Lemma b9_kref_kinds :
  seg_spec.conv_kinds F_knock = [true; true] /\ seg_spec.conv_kinds F_nokey = [true; true] /\
  seg_spec.conv_kinds F_badignore = [true; true].
Proof. vm_compute. repeat split; reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* what a refuse site of B9 puts in the variadic registers a3 .. a7: each %s argument a C string in buf, or
   cur_name holding it (pf_nm, KREF's a3 = slot 0x40); each integer argument below 2 ^ 31 (refuse_pre's
   sa_va_args, in the shape B9's sites have it) *)
Fixpoint b9_va (v : pfv) (pos : Z) (rd : reader) (rs : list word) (xs : list arg) : Prop :=
  match xs, rs with
  | [], _ => True
  | AS s :: xs', r :: rs' =>
      ((exists q, r = w64 q /\ sa_str rd q s /\ pf_inb (b9_bufp v pos) q s) \/
       (r = w64 (b9_cnp v pos) /\ pf_nm rd (b9_cnp v pos) s)) /\ b9_va v pos rd rs' xs'
  | AI z :: xs', r :: rs' => (0 <= z < 2 ^ 31 /\ bv_unsigned r = z) /\ b9_va v pos rd rs' xs'
  | _ :: _, [] => False
  end.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** What each callee's contract asks besides afn_pre *)
(* refuse_contract at image B's numbers, at a call with a0 = c, a1 = lineno = ln + 1, a2 = f's literal, c holding
   cf *)
Definition b9_refuse_call (v : pfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
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
Definition b9_trim_call (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (regs : bvmap 5 word) (p : Z) (s : list Z) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\
  trim_pre SEGS B lyc Sc Wc memc regs p s /\
  st_nev Sc + EV_trim <= EV_MAX.

(** ** The facts every site shares *)
(* where buf lies: inside the class-5 frame, below the allocator's ceiling, its end 8-aligned *)
Lemma b9_buf_rng : forall v pos lyc Sc Wc memc mdc, b9_st B v pos lyc Sc Wc memc mdc ->
  4096 < b9_bufp v pos /\ b9_bufp v pos + 512 <= alloc_ceiling /\ (b9_bufp v pos + 512) mod 8 = 0 /\
  pf_F v pos <= b9_bufp v pos /\ b9_bufp v pos + 512 <= pf_F v pos + 2048.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  destruct (b9_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D.
  unfold b9_bufp, PF_O_BUF.
  split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* where cur_name lies: inside the class-5 frame, below the allocator's ceiling, its end 8-aligned *)
Lemma b9_cn_rng : forall v pos lyc Sc Wc memc mdc, b9_st B v pos lyc Sc Wc memc mdc ->
  4096 < b9_cnp v pos /\ b9_cnp v pos + 16 <= alloc_ceiling /\ (b9_cnp v pos + 16) mod 8 = 0 /\
  pf_F v pos <= b9_cnp v pos /\ b9_cnp v pos + 16 <= pf_F v pos + 2048.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  destruct (b9_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D.
  unfold b9_cnp, PF_O_CN.
  split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* the frame's room for refuse's class-0 frame, and the events: the journal from parse_file's entry *)
Lemma b9_room_ev : forall v pos lyc Sc Wc memc mdc, b9_st B v pos lyc Sc Wc memc mdc ->
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

(* a %s argument inside the class-5 frame whose span ends at or below an 8-aligned bound M inside the frame is
   apart from the three ranges refuse_pre forbids *)
Lemma b9_apart_frame : forall v pos lyc Sc Wc memc mdc (k : nat) sp q s M,
  b9_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat ->
  pf_F v pos <= q -> q + Z.of_nat (length s) + 1 <= M -> M mod 8 = 0 -> M <= pf_F v pos + 2048 ->
  sa_apart_all q (seg_spec.cstr_span q s)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)].
Proof.
  intros v pos lyc Sc Wc memc mdc k sp q s M H Hk HqF HqM HM8 HMF.
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  destruct HSTK as (_ & _ & Hceil & _).
  destruct (b9_frame_rng B v pos lyc Sc Wc memc mdc H) as (HF0 & HF1 & _ & _).
  pose proof (b9_round8 (q + Z.of_nat (length s) + 1) M HqM HM8) as HR.
  assert (HSP : q + seg_spec.cstr_span q s <= M) by (unfold seg_spec.cstr_span; lia).
  (* the block c and the class-5 frame do not meet *)
  pose proof HOBJ as (_ & _ & _ & _ & (b & m & Hin & Hb & Hm) & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hin
    (b9_fin B v pos lyc Sc Wc memc mdc H)) as Hsep.
  pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hm; lia)) as [_ Hrq].
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite b9_fb5 in Hsep.
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

(* a %s argument in buf is apart from the three ranges refuse_pre forbids *)
Lemma b9_apart : forall v pos lyc Sc Wc memc mdc (k : nat) sp q s,
  b9_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat -> pf_inb (b9_bufp v pos) q s ->
  sa_apart_all q (seg_spec.cstr_span q s)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)].
Proof.
  intros v pos lyc Sc Wc memc mdc k sp q s H Hk [HI1 HI2].
  destruct (b9_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & Hb8 & HFb & HbF).
  apply (b9_apart_frame v pos lyc Sc Wc memc mdc k sp q s (b9_bufp v pos + 512) H Hk); lia.
Qed.

(* cur_name's string (at most 15 bytes) is apart from the three ranges refuse_pre forbids *)
Lemma b9_apart_cn : forall v pos lyc Sc Wc memc mdc (k : nat) sp s,
  b9_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat -> (length s < 16)%nat ->
  sa_apart_all (b9_cnp v pos) (seg_spec.cstr_span (b9_cnp v pos) s)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)].
Proof.
  intros v pos lyc Sc Wc memc mdc k sp s H Hk Hl.
  destruct (b9_cn_rng v pos lyc Sc Wc memc mdc H) as (Hc0 & Hc1 & Hc8 & HFc & HcF).
  apply (b9_apart_frame v pos lyc Sc Wc memc mdc k sp (b9_cnp v pos) s (b9_cnp v pos + 16) H Hk); lia.
Qed.

(* the variadic registers of a B9 site give sa_va_args and refuse_va_locs (the frame arm) *)
Lemma b9_va_ok : forall v pos lyc Sc Wc memc mdc (k : nat) sp rs xs,
  b9_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat ->
  b9_va v pos (rdW Wc memc) rs xs ->
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
    destruct x as [s|z]; cbn [b9_va] in HV; destruct HV as [Hx HV]; destruct (IH rs HV) as [IH1 IH2].
    + pose proof alloc_ceiling_lt as HC.
      destruct Hx as [(q & -> & HS & HI) | (-> & HN)].
      * (* a string in buf *)
        pose proof HI as [HI1 HI2].
        destruct (b9_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & _).
        assert (EQ : bv_unsigned (w64 q) = q).
        { unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
        cbn [sa_va_args refuse_va_locs sa_va_arg]. rewrite EQ.
        split; [split; [|exact IH1] | split; [|exact IH2]].
        -- split; [lia|]. split; [exact HS|].
           split; [apply (Nat.le_trans _ 512%nat); [lia | apply Nat.leb_le; vm_compute; reflexivity]|].
           split; [exact (b9_addr_buf B v pos lyc Sc Wc memc mdc q (Z.of_nat (length s) + 1) H HI1
                     ltac:(lia) ltac:(lia))|].
           exact (b9_apart v pos lyc Sc Wc memc mdc k sp q s H Hk HI).
        -- right. exact (b9_fframe_buf B v pos lyc Sc Wc memc mdc q (Z.of_nat (length s) + 1) H HI1
             ltac:(lia) ltac:(lia)).
      * (* cur_name, holding s *)
        destruct (b9_nm_str_st B v pos lyc Sc Wc memc mdc s H HN) as [HS Hl].
        destruct (b9_cn_rng v pos lyc Sc Wc memc mdc H) as (Hc0 & Hc1 & _).
        assert (EQ : bv_unsigned (w64 (b9_cnp v pos)) = b9_cnp v pos).
        { unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
        cbn [sa_va_args refuse_va_locs sa_va_arg]. rewrite EQ.
        split; [split; [|exact IH1] | split; [|exact IH2]].
        -- split; [lia|]. split; [exact HS|].
           split; [apply (Nat.le_trans _ 16%nat); [lia | apply Nat.leb_le; vm_compute; reflexivity]|].
           split; [exact (b9_addr_cn B v pos lyc Sc Wc memc mdc (b9_cnp v pos) (Z.of_nat (length s) + 1) H
                     ltac:(lia) ltac:(lia) ltac:(lia))|].
           exact (b9_apart_cn v pos lyc Sc Wc memc mdc k sp s H Hk Hl).
        -- right. exact (b9_fframe_cn B v pos lyc Sc Wc memc mdc (b9_cnp v pos) (Z.of_nat (length s) + 1) H
             ltac:(lia) ltac:(lia) ltac:(lia)).
    + cbn [sa_va_args refuse_va_locs sa_va_arg].
      split; [split; [exact Hx | exact IH1] | exact IH2].
Qed.

(** ** refuse: the rule B9's site shares with the A template's sites *)
Lemma b9_refuse_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n f args,
  b9_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  In f seg_spec.REFUSE_FORMATS -> In f PARSE_FILE_LITS ->
  seg_spec.conv_kinds f = map seg_spec.arg_is_s args ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  b9_va v pos (rdW Wc memc) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args ->
  b9_refuse_call v lyc Sc Wc memc regs cf ln f args.
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
  destruct (b9_room_ev v pos lyc Sc Wc memc mdc H) as [HROOM HEV].
  destruct (b9_va_ok v pos lyc Sc Wc memc mdc (length (rc_refusal cf)) (spZ regs) _ args H HK8 HVA)
    as [HVA1 HVA2].
  pose proof (b9_le65535 _ LS) as LSZ.
  assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
  unfold b9_refuse_call.
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

(** ** refuse: B9's site KREF 0x889a0 (VERIFY rule 1j-bis) *)
(* refuse(c, lineno, f, cur_name, x) at KREF (pf_pieces.v INV_KREF, pf_kref): F_knock (0x88988-0x8899c, x = val
   from slot 0x70), F_nokey (0x885c8-0x885e0, x = the key s7), F_badignore (B12, 0x888a4-0x888b8, x = val);
   a3 = slot 0x40 = cur_name holding nm, a4 = xp the C string x in buf *)
Lemma b9_refuse_site_kref : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n f nm xp x,
  b9_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  f = F_knock \/ f = F_nokey \/ f = F_badignore ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  getr regs 13 = w64 (pf_F v pos + PF_O_CN) -> pf_nm (rdW Wc memc) (pf_F v pos + PF_O_CN) nm ->
  getr regs 14 = w64 xp -> sa_str (rdW Wc memc) xp x -> pf_inb (pf_F v pos + PF_O_BUF) xp x ->
  b9_refuse_call v lyc Sc Wc memc regs cf ln f [AS nm; AS x].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n f nm xp x H HRC HCNT HMID HFRM HF R10 R11 R12 R13 HN R14 HS HI.
  apply (b9_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n f _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 |].
  - unfold seg_spec.REFUSE_FORMATS. destruct HF as [-> | [-> | ->]]; b9_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. destruct HF as [-> | [-> | ->]]; b9_in.
  - destruct b9_kref_kinds as (K1 & K2 & K3).
    cbn [map seg_spec.arg_is_s]. destruct HF as [-> | [-> | ->]]; [exact K1 | exact K2 | exact K3].
  - cbn [b9_va].
    split; [right; split; [exact R13 | exact HN]|].
    split; [|exact I].
    left. exists xp. split; [exact R14|]. split; [exact HS | exact HI].
Qed.

(** ** trim: B9's two sites (VERIFY rule 1j-bis) *)
(* trim(line) at 0x88424 (a0 = s7 = the line cut at '=', after `sb zero,0(s8)` 0x8841c) and trim(eq + 1) at
   0x88434 (a0 = s8 + 1, 0x88430): each a C string s at p in buf with a0 = p *)
Lemma b9_trim_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) p s,
  b9_st B v pos lyc Sc Wc memc mdc ->
  getr regs 10 = w64 p -> sa_str (rdW Wc memc) p s -> pf_inb (pf_F v pos + PF_O_BUF) p s ->
  b9_trim_call lyc Sc Wc memc regs p s.
Proof.
  intros v pos lyc Sc Wc memc mdc regs p s H R10 HS HI.
  change (pf_inb (b9_bufp v pos) p s) in HI. destruct HI as [HI1 HI2].
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  destruct (b9_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & _).
  destruct (b9_room_ev v pos lyc Sc Wc memc mdc H) as [_ HEV].
  pose proof alloc_ceiling_lt as HC.
  pose proof (b9_addr_buf B v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H HI1 ltac:(lia) ltac:(lia))
    as HA.
  pose proof HA as (_ & _ & _ & HRA & _).
  unfold b9_trim_call.
  split; [exact HROD|]. split; [exact R10|]. split; [lia|].
  split; [|unfold EV_trim; lia].
  unfold trim_pre.
  split; [lia|]. split; [exact HS|]. split; [exact HA|].
  split; [|lia].
  left. split; [|exact HRA].
  exact (b9_fframe_buf B v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H HI1 ltac:(lia) ltac:(lia)).
Qed.

End e.
End f.
End d.
