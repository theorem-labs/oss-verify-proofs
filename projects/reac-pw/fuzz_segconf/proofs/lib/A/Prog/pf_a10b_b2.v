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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 199 of its 241 lines of code are new or changed and 411 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A: concrete helper lemmas of piece PA10_B of segment A10b of
   reac_segconf_parse_file's walk (lib/A/Prog/pf_a10b_b.v; the five bcmp calls 0x88460 .. 0x884c8 at sp = s1).
   No instruction is walked here. Written 2026-10-30.
   P1 (b_base_keep, b_st_keep, b_val_keep, b_low_keep): a cut's facts survive a step whose reader changes only
     inside the bcmp window [s1 - 2 ESTACK, s1). That window lies inside [sp0 - STK, s1), A5's write set's first
     arm, so the reader is kept off pf_a5_k.a5_Wrx (b2_hk) and pf_a5_k's a5_keep_* carry the frame's facts; the
     objects at and below the frame are below alloc_ceiling (b2_low). The heap blocks' shadow is re-derived from
     AR at the new state (pf_a6_k's a6_heap_addr), never carried.
   P2 (b_bcmp_pre): every premise of YCbq.aj_bcmp_at for x = low, y = the role word's literal.
   No Section hypothesis: SSPX and VRO are not used (a5_keep_ssp / a5_keep_rod0 carry sa_ssp and arodata_okP). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaFx PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
SegPgBase SegABase SegGlob SegInstA SegObj refuse_c reac_segconf_parse_file_c pf_pieces pf_a10b_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_a5_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a6_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

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

(* ---- helpers ---- *)
(* a present byte of a byte list / a C string *)
Lemma b2_bytes_some : forall (rd : reader) a bs x, sa_bytes rd a bs -> a <= x < a + Z.of_nat (length bs) ->
  rd x <> None.
Proof.
intros rd a bs x H Hx. specialize (H (Z.to_nat (x - a)) ltac:(lia)).
rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia. rewrite H. discriminate.
Qed.
Lemma b2_zs_some : forall (rd : reader) a l x, sa_zs rd a l -> a <= x < a + Z.of_nat (length l) -> rd x <> None.
Proof.
intros rd a l x H Hx. specialize (H (Z.to_nat (x - a)) ltac:(lia)).
rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia. rewrite H. discriminate.
Qed.
(* a C string below alloc_ceiling, kept by a reader that agrees below alloc_ceiling *)
Lemma b2_str_low : forall (rd rd' : reader) p s, (forall a, 0 <= a < alloc_ceiling -> rd' a = rd a) ->
  0 <= p -> p + Z.of_nat (length s) + 8 <= alloc_ceiling -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s KL H0 H1 ((Hz & Hn) & Ht).
split; [split; [|exact Hn]|].
- intros i Hi. pose proof Hi as Hl. rewrite length_app in Hl. cbn [length] in Hl.
  rewrite KL by lia. exact (Hz i Hi).
- intros x Hx. pose proof (Z.mod_pos_bound (p + Z.of_nat (length s)) 8 ltac:(lia)).
  rewrite KL by lia. exact (Ht x Hx).
Qed.
(* the five role words are literals of parse_file's module, at most 6 bytes long *)
Lemma b2_words : forall w, In w m_file_c.MF_ROLE_WORDS -> In w PARSE_FILE_LITS /\ (length w <= 6)%nat.
Proof.
intros w Hw. unfold m_file_c.MF_ROLE_WORDS in Hw.
destruct Hw as [<- | [<- | [<- | [<- | [<- | []]]]]];
  (split; [unfold PARSE_FILE_LITS; apply in_or_app; left; cbn [In];
           repeat first [left; reflexivity | right]
          | apply Nat.leb_le; vm_compute; reflexivity]).
Qed.
(* the bcmp window [s1 - 2 ESTACK, s1) lies in [sp0 - STK, s1) and above alloc_ceiling *)
Lemma b2_hk : forall v pos (rd rd' : reader), a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rd' a = rd a) ->
  forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos sl shw a -> rd' a = rd a.
Proof.
intros v pos rd rd' G K sl shw a Ha Hn.
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof STK_values as (_ & _ & _ & SPF & _).
apply K; [exact Ha|]. intros Hw. apply Hn. unfold a5_Wrx. left. rewrite SPF. unfold ESTACK in Hw. lia.
Qed.
Lemma b2_low : forall v pos (rd rd' : reader), a5_G v pos ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rd' a = rd a) ->
  forall a, 0 <= a < alloc_ceiling -> rd' a = rd a.
Proof.
intros v pos rd rd' G K a Ha.
pose proof G as (G1 & G2 & G3 & G4 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
rewrite SPF in G1. apply K; [lia | unfold ESTACK; lia].
Qed.
(* pf_obj across a step kept off a5_Wrx, with AR at the new state: pf_a5_k's keeps, the blocks' shadow re-derived *)
Lemma b2_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc memc' mdc',
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  AR SEGS B lyc Sc Wc memc' mdc' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx v pos true true a -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_obj B v lyc Sc (rdW Wc memc) -> pf_obj B v lyc Sc (rdW Wc memc').
Proof.
intros v pos lyc Sc Wc memc mdc memc' mdc' G HAR Hin Hly HAR' HK (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
split; [exact (a5_keep_hstr B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly HK _ _ T3 T1)|].
split; [exact (pf_a6_k.a6_heap_addr B _ _ _ _ _ _ _ HAR' T3 ltac:(unfold pf_len; lia))|]. split; [exact T3|].
split; [exact (pf_a6_k.a6_heap_addr B _ _ _ _ _ _ _ HAR' C2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|]. split; [exact C2|].
split; [exact (a5_keep_cat B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly HK CA)|].
split; [intros x Hx; exact (a5_keep_lit B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly HK _ _ (LI x Hx))|].
split; [exact (a5_keep_rod0 B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly HK RO)
       | exact (a5_keep_ssp B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly HK SS)].
Qed.

(* ---- P1: the cut's facts survive a step that changes the reader only in [s1 - 2 ESTACK, s1) ---- *)
Lemma b_base_keep : forall v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  pf_rg rX' [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (22, SHADOW_OFF)] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_base B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros v pos lyc Sc Wc rX memc mdc rX' memc' mdc' sc HB HJ' HRG K.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof (proj1 HJ') as HAR'.
pose proof (b2_hk v pos (rdW Wc memc) (rdW Wc memc') G K) as HK.
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HFI as (_ & _ & HS0 & HP0 & HSV & HFL & HFRM & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HS0|]. split; [exact HP0|].
  split; [exact (a5_keep_saved v pos _ _ _ G (HK true true) HSV)|].
  split; [exact (a5_keep_flag v pos _ _ _ G (HK true true) HFL)|].
  split; [exact HFRM | exact HRG]. }
split; [exact (b2_keep_obj v pos lyc Sc Wc memc mdc memc' mdc' G HAR Hin Hly HAR' (HK true true) HOBJ)|].
split; [exact (a5_keep_sl v pos _ _ true G (HK true true) HSL)
       | exact (a5_keep_fsh v pos _ _ true sc G (HK true false) HFSH)].
Qed.
Lemma b_st_keep : forall v pos lyc Sc Wc rX memc mdc memc' sc cf cur nm k,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_st v pos (rdW Wc memc) cf cur nm k -> pf_st v pos (rdW Wc memc') cf cur nm k.
Proof.
intros v pos lyc Sc Wc rX memc mdc memc' sc cf cur nm k HB K Hst.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
pose proof HB as (_ & _ & (_ & _ & _ & _ & C2 & _) & _).
exact (a5_keep_st B v pos lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly
  (b2_hk v pos (rdW Wc memc) (rdW Wc memc') G K true true) cf cur nm k C2 Hst).
Qed.
Lemma b_val_keep : forall v pos lyc Sc Wc rX memc mdc memc' sc vp val,
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  pf_inb (pf_F v pos + PF_O_BUF) vp val ->
  sa_str (rdW Wc memc) vp val -> sa_str (rdW Wc memc') vp val.
Proof.
intros v pos lyc Sc Wc rX memc mdc memc' sc vp val HB K Hinb Hs.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & _).
destruct Hinb as [Hb1 Hb2]. unfold PF_O_BUF in *.
exact (b2_str_low _ _ vp val (b2_low v pos _ _ G K) ltac:(lia) ltac:(lia) Hs).
Qed.
Lemma b_low_keep : forall v pos lyc Sc Wc rX memc mdc memc' sc (LB : list byte),
  pf_base B v pos lyc Sc Wc rX memc mdc sc ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v) -> rdW Wc memc' a = rdW Wc memc a) ->
  length LB = 64%nat ->
  sa_bytes (rdW Wc memc) (pf_F v pos + PF_O_LOW) LB -> sa_bytes (rdW Wc memc') (pf_F v pos + PF_O_LOW) LB.
Proof.
intros v pos lyc Sc Wc rX memc mdc memc' sc LB HB K HL HLB i Hi.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof G as (_ & _ & _ & _ & _ & G6 & G7 & _).
rewrite (b2_low v pos _ _ G K); [exact (HLB i Hi)|]. unfold PF_O_LOW. lia.
Qed.

(* ---- P2: the premises of YCbq.aj_bcmp_at at a bcmp call of A10b ---- *)
Lemma b_bcmp_pre : forall v pos lyc Sc Wc rX memc mdc (LB : list byte) (regsT : bvmap 5 word) (w : list Z),
  pf_base B v pos lyc Sc Wc rX memc mdc PF_SC_LOW ->
  length LB = 64%nat -> sa_bytes (rdW Wc memc) (pf_F v pos + PF_O_LOW) LB ->
  In w m_file_c.MF_ROLE_WORDS -> spZ regsT = pf_s1 v ->
  0 <= pf_F v pos + PF_O_LOW /\ pf_F v pos + PF_O_LOW + Z.of_nat (S (length w)) <= 2 ^ 63 /\
  0 <= seg_litA_rc w /\ seg_litA_rc w + Z.of_nat (S (length w)) <= 2 ^ 63 /\
  (pf_s1 v - pf_sp0 v) mod 16 = 0 /\ pf_s1 v - pf_sp0 v <= 0 /\
  2 * ESTACK - (pf_s1 v - pf_sp0 v) <= STK_reac_segconf_parse_file /\
  src_ok SEGS Wc regsT memc (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w))) /\
  src_ok SEGS Wc regsT memc (seg_litA_rc w) (Z.of_nat (S (length w))) /\
  (forall a, pf_F v pos + PF_O_LOW <= a < pf_F v pos + PF_O_LOW + Z.of_nat (S (length w)) ->
     ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v)) /\
  (forall a, seg_litA_rc w <= a < seg_litA_rc w + Z.of_nat (S (length w)) ->
     ~ (pf_s1 v - 2 * ESTACK <= a < pf_s1 v)) /\
  amem_range (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w))) /\
  amem_range (seg_litA_rc w) (Z.of_nat (S (length w))) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w))) /\
  (0 < Z.of_nat (S (length w)) -> shadow_hull_vis (rdW Wc memc) (pf_F v pos + PF_O_LOW) (Z.of_nat (S (length w)))) /\
  range_addressable (rdW Wc memc) SHADOW_OFF (seg_litA_rc w) (Z.of_nat (S (length w))) /\
  (0 < Z.of_nat (S (length w)) -> shadow_hull_vis (rdW Wc memc) (seg_litA_rc w) (Z.of_nat (S (length w)))) /\
  sa_str (rdW Wc memc) (seg_litA_rc w) w.
Proof.
intros v pos lyc Sc Wc rX memc mdc LB regsT w HB HL HLB Hw Hsp.
pose proof (a5_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _).
subst lyc.
destruct (b2_words w Hw) as (HwL & Hw6).
destruct HB as (_ & _ & HOBJ & _ & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & LI & _).
destruct (LI w HwL) as (Hy0 & Hys & Hyp & _ & Hyi).
destruct (Hyp (p_ly v) Sc Wc memc mdc HAR) as (P0 & P1 & P2 & P3 & P4).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). pose proof asan_consts as (C1 & _).
rewrite SPF in G1.
assert (HF8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in G8; [|lia]. destruct G8 as [k Hk]. rewrite Hk. replace (k * 32) with ((4 * k) * 8) by lia.
  apply Z_mod_mult. }
assert (Hs16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ assert (H16 : pf_s1 v mod 16 = 0).
  { apply Z.mod_divide in G5; [|lia]. destruct G5 as [k Hk]. rewrite Hk.
    replace (k * 32) with ((2 * k) * 16) by lia. apply Z_mod_mult. }
  rewrite Zminus_mod, H16, G3. reflexivity. }
assert (Hyimg : forall a, seg_litA_rc w <= a < seg_litA_rc w + (Z.of_nat (length w) + 1) -> a < kImgEnd)
  by (intros a Ha; exact (proj2 (pa_img_range a (proj1 (Hyi a Ha))))).
assert (HSH80 : rdW Wc memc (pf_SH v pos + 80) = Some 0) by (rewrite (HFSH 80 ltac:(lia)); reflexivity).
replace (Z.of_nat (S (length w))) with (Z.of_nat (length w) + 1) by lia.
unfold PF_O_LOW in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact P1|].
split; [exact Hs16|]. split; [lia|]. split; [rewrite SPF; unfold ESTACK; lia|].
split.
{ unfold src_ok. intros a Ha. split.
  - apply (b2_bytes_some _ _ LB a HLB). rewrite HL. change (Z.of_nat 64) with 64. lia.
  - rewrite Hsp. unfold ESTACK. lia. }
split.
{ unfold src_ok. intros a Ha. split.
  - destruct Hys as ((Hz & _) & _). apply (b2_zs_some _ _ _ _ Hz). rewrite length_app. cbn [length]. lia.
  - rewrite Hsp. pose proof (Hyimg a Ha). unfold kImgEnd, ESTACK in *. lia. }
split; [intros a Ha; unfold ESTACK; lia|].
split; [intros a Ha; pose proof (Hyimg a Ha); unfold kImgEnd, ESTACK in *; lia|].
split; [apply (amem_range_sub_app (pf_F v pos) 2048); [exact G9 | lia | lia | lia | lia]|].
split; [exact P2|].
split.
{ intros z Hz. exists 0. split; [|left; reflexivity].
  replace z with (pf_F v pos + (z - pf_F v pos)) by lia.
  rewrite (shadow_of_addr_aligned_off SHADOW_OFF (pf_F v pos) (z - pf_F v pos) HF8).
  replace ((z - pf_F v pos) / 8) with 80 by (apply Z.div_unique with (r := z - pf_F v pos - 640); lia).
  exact HSH80. }
split.
{ intros Hn0.
  exact (shadow_hull_vis_of_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos (pf_F v pos + 640)
    (Z.of_nat (length w) + 1) HAR Hin
    ltac:(change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); lia)
    ltac:(change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); change (fs_frame_bytes 5) with 2048; lia) Hn0). }
split; [exact P3|]. split; [exact P4 | exact Hys].
Qed.

End e.
End f.
End d.
