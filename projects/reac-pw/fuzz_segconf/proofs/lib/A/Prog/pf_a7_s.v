(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the six PROGRAM call sites of segment A7 of
   reac_segconf_parse_file's walk (the header branch, HDR 0x87f6c -> TAIL / SEG; segment A7's proof,
   2026-10-30). The stream's rule that every call site is shown by its own lemma: one closed lemma per call site,
   showing that the site supplies the callee contract's premises. Each lemma below is stated over a state of
   the segment that satisfies pf_a7_d.v's a7_st, plus the registers and the argument data of its site, and
   concludes everything the callee's contract asks besides afn_pre (which the call rule cl_callSF builds from
   the journal):
     refuse (lib/A/Prog/refuse_c.v) at image A's numbers (lit := seg_litA_rc, gotw := gotwA,
       guard := guardA, SegInstA.v): a7_refuse_call -- arodata_okP, the three argument registers with their
       ranges, refuse_pre, sa_room, the event bound.
         a7_refuse_site_88060  F_notclosed (a2 formed at 0x8804c) or F_after (0x87f98), a3 = lp = s7,
                               args = [AS (pf_tline s o)], the trimmed line in buf
         a7_refuse_site_880f8  F_unknown, a3 = s3 = the body, args = [AS body]; a7_refuse_site_880f8_body
                               is the same site with the body a free list (the cut INV_UNK's form)
         a7_refuse_site_8835c  F_toolong, a3 = s9 = the name, a4 = 15, args = [AS name; AI 15]
         a7_refuse_site_88794  F_noname, no variadic argument, args = []
       all four from the one rule a7_refuse_site_ok (they differ only in f and the arguments).
     trim (lib/A/Prog/trim_c.v): a7_trim_call -- arodata_okP, a0 with its range, trim_pre, the event bound.
         a7_trim_site_880c4    a0 = s7 + 1 = lp + 1, the string slice 1 ci (pf_tline s o) that the store
                               `sb zero, 0(close)` at 0x880bc made in buf
         a7_trim_site_88310    a0 = s3 + 7 = body + 7, the string skipn 7 body in buf
       both from a7_trim_site_ok.
   No instruction is walked here.

   WHERE EACH PREMISE COMES FROM.
   - Every string a site passes lies in parse_file's buf[512] (pf_inb): its bytes and NUL are addressable with
     their shadow mapped (pf_a7_d.v a7_addr_buf: buf's 64 shadow cells are 0 while buf is in scope), and it lies
     in the LIVE class-5 side-stack frame (a7_fframe_buf), which is refuse_va_locs' frame arm and trim_pre's
     sa_dst frame arm.
   - refuse_pre's sa_va_args keeps each %s argument's read span (seg_spec.cstr_span: up to the next 8-byte
     boundary) apart from [ly_stk_lo ly, sp), the slot refusal[n] and c->refused. buf ends 8-aligned
     (F mod 32 = 0, buf = F + 0x40, 512 bytes), so the span stays in buf; buf is below
     alloc_ceiling <= ly_stk_lo ly (the journal's astk_ok at parse_file's entry layout, which is the cut's);
     the slot (n <= 8 by rconf_enc) and c->refused lie in the block c, and the block c and the class-5 frame are
     disjoint (YCbq.sep_block_frame, from AR_laws' al_sep).
   - c: c <> 0 and 16-aligned from reader_pre (pf_cx), sa_heap / sa_addr of the block and c's registers' range
     from pf_obj / pf_cx; c holds cf (the cut's pf_st); rc_refused cf + 1 < 2 ^ 32 from pf_cnt cf 0.
   - the line: lineno = ln + 1 (the cut's s10) is pf_lctx's line count at the next line, at most the text's
     length, which reader_pre bounds by 65535.
   - the format: In f REFUSE_FORMATS, its conversion kinds and In f PARSE_FILE_LITS by computation (all five
     of A7's formats are in PARSE_FILE_LITS, reac_segconf_parse_file_c.v:125-129); sa_lit and refuse's own
     literals (REFUSE_LITS, the tail of PARSE_FILE_LITS) from pf_obj; the format's address below 2 ^ 63 from its
     sa_pinned at the cut's AR state.
   - printf's machine: sa_frm0 is the walk's (a premise); sa_ssp rd gotwA guardA is pf_obj's last conjunct AT
     THE SITE'S OWN STATE, so no Section hypothesis is taken here (the image-A owner's route-A hypothesis SSPX is
     where the walk re-gives a7_st after a call, not at the site).
   - sa_room Sc and the event bound: the journal's frames clause (frames Sc = [(5, pos)] ++ frames S) and
     events clause (st_nev Sc <= st_nev S + 0) with pf_cx's sa_room_n 2 S and its event bound.
   Section hypotheses: none. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a7_f pf_a7_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* a list of the five formats, decided by trying each position *)
Ltac a7_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* rounding up to the next multiple of 8 stays below an 8-aligned bound *)
Lemma a7_round8 : forall x M, x <= M -> M mod 8 = 0 -> x + (- x) mod 8 <= M.
Proof.
  intros x M H1 H2.
  pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod M 8 ltac:(lia)) as D2.
  lia.
Qed.

(* reader_pre's text bound (length s <= 65535)%nat, in Z; the nat literal is too large for lia to read *)
Lemma a7_le65535 : forall m : nat, (m <= 65535)%nat -> Z.of_nat m <= 65535.
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
Fixpoint a7_va (v : pfv) (pos : Z) (rd : reader) (rs : list word) (xs : list arg) : Prop :=
  match xs, rs with
  | [], _ => True
  | AS s :: xs', r :: rs' =>
      (exists q, r = w64 q /\ sa_str rd q s /\ pf_inb (a7_buf v pos) q s) /\ a7_va v pos rd rs' xs'
  | AI z :: xs', r :: rs' => (0 <= z < 2 ^ 31 /\ bv_unsigned r = z) /\ a7_va v pos rd rs' xs'
  | _ :: _, [] => False
  end.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** What each callee's contract asks besides afn_pre *)
(* refuse_contract at image A's numbers, at a call with a0 = c, a1 = lineno = ln + 1, a2 = f's literal,
   c holding cf *)
Definition a7_refuse_call (v : pfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
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
Definition a7_trim_call (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte)
  (regs : bvmap 5 word) (p : Z) (s : list Z) : Prop :=
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memc) /\
  getr regs 10 = w64 p /\ 0 <= p < 2 ^ 64 /\
  trim_pre SEGS B lyc Sc Wc memc regs p s /\
  st_nev Sc + EV_trim <= EV_MAX.

(** ** The facts every site shares *)
(* where buf lies: inside the class-5 frame, below the allocator's ceiling, its end 8-aligned *)
Lemma a7_buf_rng : forall v pos lyc Sc Wc memc mdc, a7_st B v pos lyc Sc Wc memc mdc ->
  4096 < a7_buf v pos /\ a7_buf v pos + 512 <= alloc_ceiling /\ (a7_buf v pos + 512) mod 8 = 0 /\
  pf_F v pos <= a7_buf v pos /\ a7_buf v pos + 512 <= pf_F v pos + 2048.
Proof.
  intros v pos lyc Sc Wc memc mdc H.
  destruct (a7_frame_rng B v pos lyc Sc Wc memc mdc H) as (H1 & H2 & _ & H4).
  pose proof (Z.div_mod (pf_F v pos) 32 ltac:(lia)) as D.
  unfold a7_buf, PF_O_BUF.
  split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* the frame's room for refuse's class-0 frame, and the events: the journal from parse_file's entry *)
Lemma a7_room_ev : forall v pos lyc Sc Wc memc mdc, a7_st B v pos lyc Sc Wc memc mdc ->
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
Lemma a7_apart : forall v pos lyc Sc Wc memc mdc (k : nat) sp q s,
  a7_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat -> pf_inb (a7_buf v pos) q s ->
  sa_apart_all q (seg_spec.cstr_span q s)
    [(ly_stk_lo lyc, sp);
     (seg_spec.refusal_addr (p_c v) k, seg_spec.refusal_addr (p_c v) k + seg_spec.RC_REFUSAL_LEN);
     (p_c v + seg_spec.RC_REFUSED, p_c v + seg_spec.RC_REFUSED + 4)].
Proof.
  intros v pos lyc Sc Wc memc mdc k sp q s H Hk [HI1 HI2].
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  destruct HSTK as (_ & _ & Hceil & _).
  destruct (a7_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & Hb8 & HFb & HbF).
  pose proof (a7_round8 (q + Z.of_nat (length s) + 1) (a7_buf v pos + 512) ltac:(lia) Hb8) as HR.
  assert (HSP : q + seg_spec.cstr_span q s <= a7_buf v pos + 512) by (unfold seg_spec.cstr_span; lia).
  (* the block c and the class-5 frame do not meet *)
  pose proof HOBJ as (_ & _ & _ & _ & (b & m & Hin & Hb & Hm) & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hin
    (a7_fin B v pos lyc Sc Wc memc mdc H)) as Hsep.
  pose proof (req_size_pos m ltac:(unfold seg_spec.SEG_C_SIZE in Hm; lia)) as [_ Hrq].
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite a7_fb5 in Hsep.
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
Lemma a7_va_ok : forall v pos lyc Sc Wc memc mdc (k : nat) sp rs xs,
  a7_st B v pos lyc Sc Wc memc mdc -> (k <= 8)%nat ->
  a7_va v pos (rdW Wc memc) rs xs ->
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
    destruct x as [s|z]; cbn [a7_va] in HV; destruct HV as [Hx HV]; destruct (IH rs HV) as [IH1 IH2].
    + destruct Hx as (q & -> & HS & HI).
      pose proof HI as [HI1 HI2].
      destruct (a7_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & _).
      pose proof alloc_ceiling_lt as HC.
      assert (EQ : bv_unsigned (w64 q) = q).
      { unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. }
      cbn [sa_va_args refuse_va_locs sa_va_arg]. rewrite EQ.
      split; [split; [|exact IH1] | split; [|exact IH2]].
      * split; [lia|]. split; [exact HS|].
        split; [apply (Nat.le_trans _ 512%nat); [lia | apply Nat.leb_le; vm_compute; reflexivity]|].
        split; [exact (a7_addr_buf B v pos lyc Sc Wc memc mdc q (Z.of_nat (length s) + 1) H HI1
                  ltac:(lia) ltac:(lia))|].
        exact (a7_apart v pos lyc Sc Wc memc mdc k sp q s H Hk HI).
      * right. exact (a7_fframe_buf B v pos lyc Sc Wc memc mdc q (Z.of_nat (length s) + 1) H HI1
          ltac:(lia) ltac:(lia)).
    + cbn [sa_va_args refuse_va_locs sa_va_arg].
      split; [split; [exact Hx | exact IH1] | exact IH2].
Qed.

(** ** refuse: the rule the four sites share *)
Lemma a7_refuse_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n f args,
  a7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  In f seg_spec.REFUSE_FORMATS -> In f PARSE_FILE_LITS ->
  seg_spec.conv_kinds f = map seg_spec.arg_is_s args ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  a7_va v pos (rdW Wc memc) [getr regs 13; getr regs 14; getr regs 15; getr regs 16; getr regs 17] args ->
  a7_refuse_call v lyc Sc Wc memc regs cf ln f args.
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
  destruct (a7_room_ev v pos lyc Sc Wc memc mdc H) as [HROOM HEV].
  destruct (a7_va_ok v pos lyc Sc Wc memc mdc (length (rc_refusal cf)) (spZ regs) _ args H HK8 HVA)
    as [HVA1 HVA2].
  pose proof (a7_le65535 _ LS) as LSZ.
  assert (HLN : 0 <= ln + 1 < 2 ^ 31) by lia.
  unfold a7_refuse_call.
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

(** ** refuse: the four sites (VERIFY rule 1j-bis) *)
(* 0x88060: refuse(c, lineno, F_notclosed / F_after, line), the trimmed line at lp = s7 in buf *)
Lemma a7_refuse_site_88060 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n lp f,
  a7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  f = F_notclosed \/ f = F_after ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc f) ->
  getr regs 13 = w64 lp ->
  sa_str (rdW Wc memc) lp (pf_tline (p_s v) o) -> pf_inb (a7_buf v pos) lp (pf_tline (p_s v) o) ->
  a7_refuse_call v lyc Sc Wc memc regs cf ln f [AS (pf_tline (p_s v) o)].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n lp f H HRC HCNT HMID HFRM HF R10 R11 R12 R13 HS HI.
  apply (a7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n f _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 |].
  - unfold seg_spec.REFUSE_FORMATS. destruct HF as [-> | ->]; a7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. destruct HF as [-> | ->]; a7_in.
  - cbn [map seg_spec.arg_is_s]. destruct HF as [-> | ->]; reflexivity.
  - cbn [a7_va]. split; [|exact I]. exists lp. split; [exact R13|]. split; [exact HS | exact HI].
Qed.

(* 0x880f8: refuse(c, lineno, F_unknown, body), the body at s3 in buf. The cut INV_UNK (pf_a7_m.v) holds the
   body as a free list: its two entries, the keyword test at 0x880e0 and the blank test at 0x8830c, agree
   only on sa_str / pf_inb of it. *)
Lemma a7_refuse_site_880f8_body : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n bp body,
  a7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc F_unknown) ->
  getr regs 13 = w64 bp ->
  sa_str (rdW Wc memc) bp body -> pf_inb (a7_buf v pos) bp body ->
  a7_refuse_call v lyc Sc Wc memc regs cf ln F_unknown [AS body].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n bp body H HRC HCNT HMID HFRM R10 R11 R12 R13 HS HI.
  apply (a7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n F_unknown _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 |].
  - unfold seg_spec.REFUSE_FORMATS. a7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. a7_in.
  - cbn [map seg_spec.arg_is_s]. reflexivity.
  - cbn [a7_va]. split; [|exact I]. exists bp. split; [exact R13|]. split; [exact HS | exact HI].
Qed.

(* the same site with the body as the header step names it, a7_body (pf_tline s o) ci *)
Lemma a7_refuse_site_880f8 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n ci bp,
  a7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc F_unknown) ->
  getr regs 13 = w64 bp ->
  sa_str (rdW Wc memc) bp (a7_body (pf_tline (p_s v) o) ci) ->
  pf_inb (a7_buf v pos) bp (a7_body (pf_tline (p_s v) o) ci) ->
  a7_refuse_call v lyc Sc Wc memc regs cf ln F_unknown [AS (a7_body (pf_tline (p_s v) o) ci)].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n ci bp.
  exact (a7_refuse_site_880f8_body v pos lyc Sc Wc memc mdc regs cf o ln d n bp _).
Qed.

(* 0x8835c: refuse(c, lineno, F_toolong, name, 15), the name at s9 in buf, a4 = 15 (0x8834c) *)
Lemma a7_refuse_site_8835c : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n ci np,
  a7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc F_toolong) ->
  getr regs 13 = w64 np -> getr regs 14 = w64 15 ->
  sa_str (rdW Wc memc) np (a7_name (a7_body (pf_tline (p_s v) o) ci)) ->
  pf_inb (a7_buf v pos) np (a7_name (a7_body (pf_tline (p_s v) o) ci)) ->
  a7_refuse_call v lyc Sc Wc memc regs cf ln F_toolong [AS (a7_name (a7_body (pf_tline (p_s v) o) ci)); AI 15].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n ci np H HRC HCNT HMID HFRM R10 R11 R12 R13 R14 HS HI.
  apply (a7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n F_toolong _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 |].
  - unfold seg_spec.REFUSE_FORMATS. a7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. a7_in.
  - cbn [map seg_spec.arg_is_s]. reflexivity.
  - cbn [a7_va]. split; [exists np; split; [exact R13|]; split; [exact HS | exact HI]|].
    split; [|exact I]. split; [lia|]. rewrite R14. unfold w64. rewrite Z_to_bv_unsigned.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

(* 0x88794: refuse(c, lineno, F_noname), no variadic argument *)
Lemma a7_refuse_site_88794 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) cf o ln d n,
  a7_st B v pos lyc Sc Wc memc mdc ->
  sa_rconf (rdW Wc memc) (p_c v) cf -> pf_cnt cf 0 -> pf_mid v o ln d n -> sa_frm0 ->
  getr regs 10 = w64 (p_c v) -> getr regs 11 = w64 (ln + 1) -> getr regs 12 = w64 (seg_litA_rc F_noname) ->
  a7_refuse_call v lyc Sc Wc memc regs cf ln F_noname [].
Proof.
  intros v pos lyc Sc Wc memc mdc regs cf o ln d n H HRC HCNT HMID HFRM R10 R11 R12.
  apply (a7_refuse_site_ok v pos lyc Sc Wc memc mdc regs cf o ln d n F_noname _ H HRC HCNT HMID HFRM);
    [| | | exact R10 | exact R11 | exact R12 | exact I].
  - unfold seg_spec.REFUSE_FORMATS. a7_in.
  - unfold PARSE_FILE_LITS. apply in_or_app. left. a7_in.
  - reflexivity.
Qed.

(** ** trim: the rule the two sites share *)
Lemma a7_trim_site_ok : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) p s,
  a7_st B v pos lyc Sc Wc memc mdc ->
  getr regs 10 = w64 p -> sa_str (rdW Wc memc) p s -> pf_inb (a7_buf v pos) p s ->
  a7_trim_call lyc Sc Wc memc regs p s.
Proof.
  intros v pos lyc Sc Wc memc mdc regs p s H R10 HS [HI1 HI2].
  pose proof H as [HCX HJ HLY HPERM HOBJ HFSH].
  pose proof HOBJ as (_ & _ & _ & _ & _ & _ & _ & HROD & _).
  destruct (a7_buf_rng v pos lyc Sc Wc memc mdc H) as (Hb0 & Hb1 & _).
  destruct (a7_room_ev v pos lyc Sc Wc memc mdc H) as [_ HEV].
  pose proof alloc_ceiling_lt as HC.
  pose proof (a7_addr_buf B v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H HI1 ltac:(lia) ltac:(lia))
    as HA.
  pose proof HA as (_ & _ & _ & HRA & _).
  unfold a7_trim_call.
  split; [exact HROD|]. split; [exact R10|]. split; [lia|].
  split; [|unfold EV_trim; lia].
  unfold trim_pre.
  split; [lia|]. split; [exact HS|]. split; [exact HA|].
  split; [|lia].
  left. split; [|exact HRA].
  exact (a7_fframe_buf B v pos lyc Sc Wc memc mdc p (Z.of_nat (length s) + 1) H HI1 ltac:(lia) ltac:(lia)).
Qed.

(** ** trim: the two sites (VERIFY rule 1j-bis) *)
(* 0x880c4: trim(line + 1) after `*close = 0` (0x880bc): the line's bytes 1 .. ci, at lp + 1 in buf *)
Lemma a7_trim_site_880c4 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) o lp ci,
  a7_st B v pos lyc Sc Wc memc mdc ->
  pf_inb (a7_buf v pos) lp (pf_tline (p_s v) o) -> hd0 (pf_tline (p_s v) o) = LBR ->
  getr regs 10 = w64 (lp + 1) ->
  sa_str (rdW Wc memc) (lp + 1) (slice 1 ci (pf_tline (p_s v) o)) ->
  a7_trim_call lyc Sc Wc memc regs (lp + 1) (slice 1 ci (pf_tline (p_s v) o)).
Proof.
  intros v pos lyc Sc Wc memc mdc regs o lp ci H [HI1 HI2] HL R10 HS.
  apply (a7_trim_site_ok v pos lyc Sc Wc memc mdc regs _ _ H R10 HS).
  destruct (pf_tline (p_s v) o) as [|x l]; [cbn in HL; discriminate|].
  unfold pf_inb. split; [lia|].
  unfold slice. rewrite length_firstn, length_skipn. cbn [length] in HI2 |- *. lia.
Qed.

(* 0x88310: trim(body + 7) after the keyword and its blank: the body's bytes from 7 on, at bp + 7 in buf *)
Lemma a7_trim_site_88310 : forall v pos lyc Sc Wc memc mdc (regs : bvmap 5 word) o ci bp,
  a7_st B v pos lyc Sc Wc memc mdc ->
  pf_inb (a7_buf v pos) bp (a7_body (pf_tline (p_s v) o) ci) ->
  strncasecmp (a7_body (pf_tline (p_s v) o) ci) S_segment 7 = 0 ->
  getr regs 10 = w64 (bp + 7) ->
  sa_str (rdW Wc memc) (bp + 7) (skipn 7 (a7_body (pf_tline (p_s v) o) ci)) ->
  a7_trim_call lyc Sc Wc memc regs (bp + 7) (skipn 7 (a7_body (pf_tline (p_s v) o) ci)).
Proof.
  intros v pos lyc Sc Wc memc mdc regs o ci bp H [HI1 HI2] HK R10 HS.
  apply (a7_trim_site_ok v pos lyc Sc Wc memc mdc regs _ _ H R10 HS).
  pose proof (a7_kw_len7 _ (a7_body_nul (pf_tline (p_s v) o) ci) HK) as H7.
  unfold pf_inb. rewrite length_skipn. lia.
Qed.

End e.
End f.
End d.
