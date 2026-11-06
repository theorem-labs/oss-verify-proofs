(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 413 of its 483 lines of code are new or changed and 4983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a2.v, with its module names changed; 165 of its 260 lines of code are new or changed and 388 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_j.v; 564 of its 643 lines of code are new or changed and 181 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the store piece of segment A10b of reac_segconf_parse_file's
   walk, pa10_s_ok : PA10_S B (lib/A/Prog/pf_a10b_k.v: HA_JOIN n -> H_ROLEV n). Part of segment A10b's proof, by
   the G3 walk owner, 2026-10-30. proves no function (kind: segment lemma); the walk's rule-24 record is the
   unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md (reuse verdict
   none: written new).

   THE CODE (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s in records/segp/dis/ at that commit), ROLEV
   0x88840 .. the snprintf call 0x88888, 20
   instructions, checks 31 and 32, one call:
     0x88840 addi a0,s4,0x10; srli a1,a0,3; add a1,a1,s6; lb a1,0(a1); bnez a1,0x88a70   check 31 (store4 role)
     0x88854 sw s3,0x10(s4)                                                              role = r
     0x88858 addi a0,s4,0x14; srli a1,a0,3; add a1,a1,s6; lb a1,0(a1); bnez a1,0x88a80   check 32 (store4 role_set)
     0x8886c addi a0,zero,1; sw a0,0x14(s4)                                              role_set = 1
     0x88874 addi a0,s4,0xa0; auipc/addi a2 = A_OBJ 35 = "%s"; addi a1,zero,0x60; ld a3,0x58(s1)
     0x88888 jal snprintf(&c->seg[gi].role_file, 96, "%s", c->reading)   -- returns to 0x8888c = JOIN
   The partial-granule arms 0x88a70 / 0x88a80 and the error calls 0x88d28 / 0x88d2c are dead: the token
   executor reads both shadow bytes as the literal 0 from one shadow entry over c->seg[gi] (p10_SH), which
   pf_obj's sa_addr of the block c gives.

   THE PROOF. A seed at ROLEV (p10_seed: every register its own atom; slot 0x58 = c + RC_READING read-only on
   s1's atom 9; the two words role / role_set writable on s4's atom 20; Bx = s6's atom 22), one run of the
   TOKEN executor (two checks, no shadow write) to the call, then the snprintf step of segment A8b's
   lib/A/Prog/pf_a8b_t.v (pfa8b_aj_snprintf_atSF with pfa8b_FR_s_regs, FR_cmd at "%s" with one string
   argument). PaFx.aj_art_blk_atF does NOT fit this call: it asks every byte of the destination's heap block
   to be in the footprint seg_spec.RC_PARSE_W c, which does not cover c's whole 16616 bytes. The snprintf post
   (RtPFCmd.v:341-342) keeps EVERY byte outside the destination [d, d + sn_len) and the scratch window, so the
   cut's facts are carried by that keep clause and the run's frame_of over this piece's write set p10_W (the
   stack below s1, seg[gi]'s role / role_set words, seg[gi].role_file): no SSPX, no VRO. The block's new
   bytes give sa_rconf of the updated record by pf_a10b_f.a10b_rconf_role, and H_JOIN at the FP state the
   wrapper returned closes the piece.
   Section hypotheses: ASNPRINTF (row 4, RtFormat.asnprintf_realizes at the listing's snprintf trampoline,
   gotwA, guardA) and OBJ (SegObj.seg_val_objs, for the format's object atom A_OBJ 35). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a10b_k pf_a10b_f pf_a5_k
pf_a6_k pf_a8b_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
Ltac p10_in := cbn [In app]; repeat first [left; reflexivity | right].
Ltac p10_lia :=
  unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.RS_ROLE, seg_spec.RS_ROLE_SET, seg_spec.RS_ROLE_FILE,
    seg_spec.SEG_C_SIZE, seg_spec.RC_READING, seg_spec.RC_N, kLowShadowBeg, kHighMemBeg, kLowMemEnd,
    kHighShadowEnd, SHADOW_OFF, CMD_SNP_K, ESTACK, CMD_IMG_LO, CMD_IMG_HI, kImgEnd in *; lia.
Lemma p10_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
(* a field the run wrote, read through the reader *)
Lemma p10_sa_val : forall segs H mem a n v, val_mem segs (mrestrict H mem) a n v -> sa_val (aview segs H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
apply a10f_unsigned_small. apply a10f_le_byte_range.
Qed.
(* a visible byte stays visible when every present byte stays present *)
Lemma p10_vis_pres : forall segs H (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, aview segs H m a <> None -> aview segs H m' a <> None.
Proof.
intros segs H m m' HP a Hv. unfold aview, mbyte, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Eh; [exact Hv|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (HP a (conj Eh (ex_intro _ b Em))) as (_ & b' & Hb'). rewrite Hb'. discriminate.
- destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hv].
Qed.
(* c->reading, the C string the snprintf prints, out of sa_rconf (seg_spec.rconf_enc's reading field) *)
Lemma p10_reading : forall (rd : reader) c cf, sa_rconf rd c cf ->
  sa_zs rd (c + seg_spec.RC_READING) (rc_reading cf ++ [0]) /\ ~ In 0 (rc_reading cf) /\
  (length (rc_reading cf) < 96)%nat.
Proof.
intros rd c cf (bs & Hb & Henc).
destruct Henc as (L & _ & _ & _ & _ & _ & _ & _ & _ & Hrd & _).
destruct Hrd as (Hfl & Hl & Hn & Hpre).
split; [|split; [exact Hn | exact Hl]].
intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
unfold seg_spec.SEG_C_SIZE in L. unfold seg_spec.fldz in *.
rewrite <- Hpre. rewrite a10f_nth_firstn by lia.
rewrite a10f_nth_zs by (rewrite Hfl; lia).
rewrite a10f_nth_fld by (change (Z.to_nat 96) with 96%nat; lia).
assert (ER : Z.of_nat (Z.to_nat seg_spec.RC_READING) = 16512) by (unfold seg_spec.RC_READING; reflexivity).
replace (c + seg_spec.RC_READING + Z.of_nat i) with (c + Z.of_nat (Z.to_nat seg_spec.RC_READING + i))
  by (rewrite Nat2Z.inj_add, ER; unfold seg_spec.RC_READING; lia).
apply Hb. lia.
Qed.
Lemma p10_afact : forall E m v lo hi al,
  ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

(* ---------- the seed's symbolic state at ROLEV ---------- *)
(* the allocator's highest ceiling (YCbq.v asan_consts): every heap address of the piece is below it *)
Definition P10_CEIL : Z := 140737479966720.
(* slot 0x58 = c + RC_READING (pf_pieces.PF_SL), read-only on s1's atom 9; role and role_set of c->seg[gi],
   writable on s4's atom 20 *)
Definition p10_regions : smem :=
  [YP09.mkRegion (Some 9%nat) 0x58 0x60 0 0 [YP09.mkChunk 0x58 (CVal 8 (SOff 24 0x4080))];
   YP09.mkRegion (Some 20%nat) 0x10 0x18 0x10 0x18 []].
Definition p10_facts : facts := mkFacts [(20%nat, mkAF 4096 P10_CEIL 2); (22%nat, mkAF SB SB 0)] [] [].
Definition p10_ss : sstate := mkSS PF_ROLEV sr_atoms p10_regions None p10_facts.
(* the shadow base the code adds is s6 itself (pf_fi: s6 = SHADOW_OFF) *)
Definition p10_Bx : sv := SOff 22 0.
(* one shadow entry over c->seg[gi]: both checks' bytes lie in it *)
Definition p10_SH : list shent := [mkSHE 20 0 356].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* row 4 of the interceptor owner's interface, at the listing's snprintf trampoline (pf_pieces.v:672-673) *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_snprintf) gotwA guardA.
(* the listing's object atoms (SegObj.v): the format "%s" is A_OBJ 35 *)
Hypothesis OBJ : seg_val_objs (PI := PI).
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

(* ---------- the bytes this piece writes, and the geometry it runs on ---------- *)
(* the stack below s1 (the wrapper's window), seg[gi]'s role / role_set words, seg[gi].role_file *)
Definition p10_W (v : pfv) (gi : nat) (a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v) \/
  (seg_spec.rseg_addr (p_c v) gi + 0x10 <= a < seg_spec.rseg_addr (p_c v) gi + 0x18) \/
  (seg_spec.rseg_addr (p_c v) gi + 0xa0 <= a < seg_spec.rseg_addr (p_c v) gi + 0x100).
Definition p10_kept (v : pfv) (gi : nat) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ p10_W v gi a -> rd' a = rd a) /\
  (forall a, rd a <> None -> rd' a <> None).
(* a5_G (pf_a5_k.v) and the block c: below the allocator's ceiling, an application range, off the image and
   off the class-5 frame *)
Definition p10_G (v : pfv) (pos : Z) (gi : nat) : Prop :=
  a5_G v pos /\ (gi < 32)%nat /\
  4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ p_c v mod 16 = 0 /\
  (p_c v + seg_spec.SEG_C_SIZE <= kLowShadowBeg \/ kHighMemBeg <= p_c v) /\
  (p_c v + seg_spec.SEG_C_SIZE <= 0x10000 \/ kImgEnd <= p_c v) /\
  (pf_F v pos + 2048 <= p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos).

Lemma p10_geo : forall v pos lyc Sc Wc memc mdc rd cf gi,
  a5_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> lyc = p_ly v ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE -> p_c v mod 16 = 0 ->
  sa_rconf rd (p_c v) cf -> (gi < length (rc_seg cf))%nat -> p10_G v pos gi.
Proof.
intros v pos lyc Sc Wc memc mdc rd cf gi G HAR Hin Hly (b & m & Hb & H1 & H2) H16 (bs & _ & Henc) Hgi.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos m (proj1 Hm)) as [_ Hreq].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hb) as Hoff. unfold off_img in Hoff.
destruct Henc as (_ & Hl32 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold p10_G. split; [exact G|].
unfold kLowShadowBeg, kHighMemBeg, kImgEnd, seg_spec.SEG_C_SIZE in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H16|].
split; [lia|]. split; [lia|]. lia.
Qed.

(* the four kinds of address this piece never writes *)
Lemma p10_nw : forall v pos gi a, p10_G v pos gi ->
  (0 <= a < alloc_ceiling /\ (a < p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= a)) \/
  (kLowMemEnd <= a < kHighShadowEnd) \/ (pf_s1 v <= a < 2 ^ 64) \/
  (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE /\
   ~ (seg_spec.rseg_addr (p_c v) gi + 0x10 <= a < seg_spec.rseg_addr (p_c v) gi + 0x18) /\
   ~ (seg_spec.rseg_addr (p_c v) gi + 0xa0 <= a < seg_spec.rseg_addr (p_c v) gi + 0x100)) ->
  0 <= a < 2 ^ 64 /\ ~ p10_W v gi a.
Proof.
intros v pos gi a (G & Hgi & C1 & C2 & C3 & C4 & C5 & C6) Ha.
pose proof G as (S1 & S2 & S3 & S4 & S5 & _).
pose proof asan_consts as (AC & _). pose proof STK_values as (_ & _ & _ & SPF & _).
unfold p10_W. rewrite SPF.
unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE, seg_spec.SEG_C_SIZE, kLowMemEnd, kHighShadowEnd, kLowShadowBeg,
  kHighMemBeg in *.
lia.
Qed.

(* ---------- reader facts carried by a step that writes only p10_W
   (the shape of pf_a5_k.v's a5_keep_* and pf_a10b_j.v's, at this piece's write set) ---------- *)
Section r.
Variables (v : pfv) (pos : Z) (gi : nat) (rd rd' : reader).
Hypothesis G : p10_G v pos gi.
Hypothesis K : p10_kept v gi rd rd'.
Lemma p10_k_low : forall x, 0 <= x < alloc_ceiling -> (x < p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= x) ->
  rd' x = rd x.
Proof. intros x H1 H2. destruct (p10_nw v pos gi x G (or_introl (conj H1 H2))) as (H3 & H4). exact (proj1 K x H3 H4). Qed.
Lemma p10_k_band : forall x, kLowMemEnd <= x < kHighShadowEnd -> rd' x = rd x.
Proof.
intros x H1. destruct (p10_nw v pos gi x G (or_intror (or_introl H1))) as (H3 & H4). exact (proj1 K x H3 H4).
Qed.
Lemma p10_k_hi : forall x, pf_s1 v <= x < 2 ^ 64 -> rd' x = rd x.
Proof.
intros x H1. destruct (p10_nw v pos gi x G (or_intror (or_intror (or_introl H1)))) as (H3 & H4).
exact (proj1 K x H3 H4).
Qed.
Lemma p10_k_cf : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE ->
  ~ (seg_spec.rseg_addr (p_c v) gi + 0x10 <= x < seg_spec.rseg_addr (p_c v) gi + 0x18) ->
  ~ (seg_spec.rseg_addr (p_c v) gi + 0xa0 <= x < seg_spec.rseg_addr (p_c v) gi + 0x100) -> rd' x = rd x.
Proof.
intros x H1 H2 H3.
destruct (p10_nw v pos gi x G (or_intror (or_intror (or_intror (conj H1 (conj H2 H3)))))) as (H4 & H5).
exact (proj1 K x H4 H5).
Qed.
Lemma p10_k_img : forall x, 0x10000 <= x < kImgEnd -> rd' x = rd x.
Proof.
intros x Hx. pose proof G as (_ & _ & C1 & C2 & _ & _ & C5 & _). pose proof asan_consts as (AC & _).
apply p10_k_low; unfold kImgEnd, seg_spec.SEG_C_SIZE in *; lia.
Qed.
Lemma p10_k_frame : forall x, pf_F v pos <= x < pf_F v pos + 2048 -> rd' x = rd x.
Proof.
intros x Hx. pose proof G as ((_ & _ & _ & _ & _ & F1 & F2 & _) & _ & _ & _ & _ & _ & _ & C6).
apply p10_k_low; unfold seg_spec.SEG_C_SIZE in *; lia.
Qed.
Lemma p10_k_shadow : forall x, 0 <= x < alloc_ceiling -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof.
intros x Hx. pose proof asan_consts as (AC & _). apply p10_k_band.
assert (Q1 : x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in Q1.
assert (Q2 : 0 <= x / 8) by (apply Z.div_pos; lia).
unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF. lia.
Qed.
Lemma p10_k_tail : forall e, sa_tail rd e -> sa_tail rd' e.
Proof. intros e H x Hx. exact (proj2 K x (H x Hx)). Qed.
Lemma p10_k_hull : forall q n, shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof. intros q n H s Hs. exact (proj2 K s (H s Hs)). Qed.
Lemma p10_k_str : forall p s, (forall x, p <= x <= p + Z.of_nat (length s) -> rd' x = rd x) ->
  sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Hk ((Hz & Hn) & Ht). split; [split; [|exact Hn] | exact (p10_k_tail _ Ht)].
intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
rewrite Hk by lia. exact (Hz i Hi).
Qed.
Lemma p10_k_addr : forall q n, 0 <= q -> q + n <= alloc_ceiling -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n H0 H1 (A0 & A1 & A2 & A3 & A4). split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- intros x Hx. destruct (A3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite p10_k_shadow by lia. exact Hs.
- intros Hn. exact (p10_k_hull _ _ (A4 Hn)).
Qed.
Lemma p10_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (p10_k_str a s); [|exact Hs]. intros x Hx. apply p10_k_img.
exact (pa_img_range x (proj1 (Hi x ltac:(lia)))).
Qed.
Lemma p10_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (p10_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (rdword_ext rd rd'); [exact Htp|].
intros k Hk. apply p10_k_img.
exact (pa_img_range _ (proj1 (Hi (pin_spec.row_addr cat i + k)
  ltac:(unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES; lia)))).
Qed.
Lemma p10_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (p10_k_img a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma p10_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
split; [rewrite (rdword_ext rd rd'); [exact G1 | intros k Hk; apply p10_k_img; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (rdword_ext rd rd'); [exact G2 | intros k Hk; apply p10_k_img; unfold guardA, kImgEnd; lia].
Qed.
(* the caller's objects: the text is a heap string apart from the block c (reader_pre's sa_disj) *)
Lemma p10_k_obj : forall lyc Sc,
  (forall x, p_t v <= x < p_t v + pf_len v -> 0 <= x < alloc_ceiling /\ (x < p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= x)) ->
  0 <= p_t v -> p_t v + pf_len v <= alloc_ceiling ->
  pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros lyc Sc Ht Ht0 Ht1 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
pose proof G as (_ & _ & C1 & C2 & _).
split.
{ apply (p10_k_str _ _); [|exact H1]. intros x Hx.
  destruct (Ht x ltac:(unfold pf_len; lia)) as [Ha Hb]. exact (p10_k_low x Ha Hb). }
split; [exact (p10_k_addr _ _ Ht0 Ht1 H2)|]. split; [exact H3|].
split; [exact (p10_k_addr (p_c v) seg_spec.SEG_C_SIZE ltac:(lia) C2 H4)|]. split; [exact H5|].
split; [exact (p10_k_cat _ H6)|].
split; [intros x Hx; exact (p10_k_lit _ _ (H7 x Hx))|].
split; [exact (p10_k_rod H8) | exact (p10_k_ssp H9)].
Qed.
Lemma p10_k_saved : forall regs, pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros regs H j q Hj. pose proof G as ((S1 & S2 & S3 & S4 & _) & _).
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
rewrite (rdword_ext rd rd'); [exact (H j q Hj)|]. intros k Hk. apply p10_k_hi. lia.
Qed.
Lemma p10_k_flag : forall x, rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some x ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some x.
Proof.
intros x H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. apply p10_k_frame. lia.
Qed.
Lemma p10_k_sl : pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
assert (Ho : 0x20 <= fst ov <= 0xb8).
{ unfold PF_SL in Hov. cbn [In] in Hov. repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
pose proof G as ((S1 & S2 & S3 & S4 & _) & _).
rewrite (rdword_ext rd rd'); [exact (H ov Hov)|]. intros k Hk. apply p10_k_hi. lia.
Qed.
Lemma p10_k_nm : forall nm, pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros nm (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. pose proof Hi as Hi'. rewrite Hl in Hi'. unfold PF_O_CN in *.
rewrite p10_k_frame by lia. exact (Hb i Hi).
Qed.
Lemma p10_k_fsh : forall sc, pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros sc H i Hi. pose proof G as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F6 & F7) & _).
rewrite p10_k_band; [exact (H i Hi) | lia].
Qed.
End r.

(* ---------- the seed at ROLEV ---------- *)
Lemma p10_seed : forall v pos gi (Wc : world SEGS) (rX : bvmap 5 word) memc,
  p10_G v pos gi ->
  (forall a, p_c v <= a < p_c v + seg_spec.SEG_C_SIZE -> apresent (w_H Wc) memc a) ->
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) -> getr rX (Z_to_bv 5 20) = w64 (seg_spec.rseg_addr (p_c v) gi) ->
  getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 24) = w64 (p_c v) ->
  rdword (rdW Wc memc) (pf_s1 v + 0x58) = Some (p_c v + seg_spec.RC_READING) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) p10_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_ROLEV)) memc (seg_rom SEGS))).
Proof.
intros v pos gi Wc rX memc HG Hpres R9 R20 R22 R24 W58.
pose proof HG as ((S1 & S2 & S3 & S4 & S5 & _) & Hgi & C1 & C2 & C3 & _).
pose proof asan_consts as (AC & _). pose proof STK_values as (_ & _ & _ & SPF & _).
set (E := Eimg (Ereg rX [])).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = getr rX q)
  by (intros k q Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = Z_to_bv 64 (seg_spec.rseg_addr (p_c v) gi))
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; reflexivity).
assert (U20 : bv_unsigned (ew E 20) = seg_spec.rseg_addr (p_c v) gi)
  by (rewrite E20; apply unsigned_lit_small; p10_lia).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), R22; reflexivity).
assert (U24 : bv_unsigned (ew E 24) = p_c v)
  by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), R24; unfold w64; apply unsigned_lit_small; p10_lia).
rewrite restrict_mkst_fx. unfold p10_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold p10_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x58 8 (SOff 24 0x4080) (p_c v + seg_spec.RC_READING)).
    * cbn [sv_denot]. rewrite U24. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). p10_lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W58).
  + rewrite U20. split; [p10_lia|]. split; [p10_lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. p10_lia.
- unfold p10_regions. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U20. repeat split; p10_lia.
- unfold facts_ok, p10_facts. cbn [f_atoms f_conds f_alias]. split; [|split; exact I].
  cbn [atoms_ok]. split; [|split; [|exact I]].
  + apply (p10_afact E 20 (seg_spec.rseg_addr (p_c v) gi)); [exact E20 | p10_lia | unfold P10_CEIL; p10_lia | | lia].
    change (2 ^ 2) with 4. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE.
    pose proof (Z.div_mod (p_c v) 16 ltac:(lia)) as D. rewrite C3, Z.add_0_r in D. rewrite D.
    replace (16 * (p_c v / 16) + 356 * Z.of_nat gi) with ((4 * (p_c v / 16) + 89 * Z.of_nat gi) * 4) by lia.
    apply Z_mod_mult.
  + apply (p10_afact E 22 SHADOW_OFF);
      [exact E22 | unfold SHADOW_OFF; lia | unfold SB, SHADOW_OFF; lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia].
Qed.

(* a register of the state after the run, as its symbolic value *)
Ltac p10_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?q = _ =>
 lazymatch type of HS with
 | st_ok _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg _ Hh E ss ms q HS);
  let w := eval vm_compute in (sr_get (ss_regs ss) q) in change (sr_get (ss_regs ss) q) with w
 end end.

(* ---------- the piece: ROLEV -> JOIN ---------- *)
Lemma p10s_rolev : forall n, HA_JOIN B n -> H_ROLEV (fx := fx) B n.
Proof.
intros n HJN v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val r HI.
destruct HI as (HBASE & HMID & HST & HRIP & Hr04 & HRG).
rewrite (a10b_step_some cf gi nm (ln + 1) val r HRIP).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LOW HBASE) as (HAR & Hly & Hin & G5 & _ & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LOW HBASE) as HFIRG.
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (HJ & _ & HSc & HPERM & HSAV & HFLAG & HFRM & _).
pose proof HST as (HRC & HCUR & HNM & HCNT).
cbn [pf_cur_ok] in HCUR.
pose proof (a6_cx B v HCX) as (Cpos & C16 & Hslen & DJ & _).
pose proof HOBJ as (OT1 & OT2 & OT3 & OC1 & OC2 & _).
pose proof (p10_geo v pos lyc Sc Wc memc mdc (rdW Wc memc) cf gi G5 HAR Hin Hly OC2 C16 HRC HCUR) as HGEO.
pose proof HGEO as (_ & Hgi32 & Hc4096 & Hcceil & _ & Hcapp & Hcimg & Hcfr).
pose proof G5 as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
pose proof asan_consts as (AC & _). pose proof STK_values as (_ & _ & _ & SPF & _).
pose proof HMID as (Ho & _).
(* the block c and the text's block *)
pose proof OC2 as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR Hbc) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _ & Hbm).
pose proof (req_size_pos mc (proj1 Hbm)) as [_ Hreq].
pose proof OT3 as (bt & mt & Hbt & Ht1a & Ht2a).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Hbt4 & Hbtc & _ & _ & _ & Hbtm).
pose proof (req_size_pos mt (proj1 Hbtm)) as [_ Hreqt].
assert (HCS : Z.of_nat (length (p_s v)) + 1 <= seg_spec.cstr_span (p_t v) (p_s v)).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
unfold sa_disj in DJ.
assert (Ht0 : 0 <= p_t v) by (unfold pf_len in *; lia).
assert (Ht1 : p_t v + pf_len v <= alloc_ceiling) by (unfold pf_len in *; lia).
assert (Htxt : forall x, p_t v <= x < p_t v + pf_len v ->
  0 <= x < alloc_ceiling /\ (x < p_c v \/ p_c v + seg_spec.SEG_C_SIZE <= x))
  by (intros x Hx; unfold pf_len in *; lia).
(* the registers of the cut *)
unfold PF_RM in HRG.
assert (R2 : getr rX (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 2 _ HFIRG); unfold a5_FI; p10_in).
assert (R3 : getr rX (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (a5_rg_get rX _ 3 _ HFIRG); unfold a5_FI; p10_in).
assert (R4 : getr rX (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (a5_rg_get rX _ 4 _ HFIRG); unfold a5_FI; p10_in).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 9 _ HFIRG); unfold a5_FI; p10_in).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF) by (apply (a5_rg_get rX _ 22 _ HFIRG); unfold a5_FI; p10_in).
assert (R19 : getr rX (Z_to_bv 5 19) = w64 r) by (apply (a5_rg_get rX _ 19 _ HRG); p10_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 (seg_spec.rseg_addr (p_c v) gi)) by (apply (a5_rg_get rX _ 20 _ HRG); p10_in).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 (p_c v)) by (apply (a5_rg_get rX _ 24 _ HRG); p10_in).
pose proof (proj1 (Forall_forall _ _) HSL (0x58, p_c v + seg_spec.RC_READING) ltac:(unfold PF_SL; p10_in)) as W58.
cbn [fst snd] in W58.
(* the seed *)
pose proof (p10_seed v pos gi Wc rX memc HGEO (fun a Ha => proj1 (Hbpres a ltac:(p10_lia))) R9 R20 R22 R24 W58) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (q : bv 5), Z.of_nat k = bv_unsigned q -> ew E k = getr rX q)
  by (intros k q Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E19 : ew E 19 = Z_to_bv 64 r) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl), R19; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 (seg_spec.rseg_addr (p_c v) gi))
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; reflexivity).
assert (U20 : bv_unsigned (ew E 20) = seg_spec.rseg_addr (p_c v) gi)
  by (rewrite E20; apply unsigned_lit_small; p10_lia).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), R22; reflexivity).
assert (U24 : bv_unsigned (ew E 24) = p_c v)
  by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), R24; unfold w64; apply unsigned_lit_small; p10_lia).
assert (UB : U E p10_Bx = SHADOW_OFF) by (unfold p10_Bx; apply U_atom; [exact E22 | unfold SHADOW_OFF; lia]).
assert (UR20 : U E (SOff 20 0) = seg_spec.rseg_addr (p_c v) gi) by (apply U_atom; [exact E20 | p10_lia]).
pose proof OC1 as (_ & _ & _ & HRAc & _).
assert (SHOK : sh_ok SEGS p10_Bx p10_SH E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, p10_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E p10_Bx 20 (p_c v) seg_spec.SEG_C_SIZE
    (seg_spec.rseg_addr (p_c v) gi) 0 356 HRAc UB UR20); [p10_lia | p10_lia |].
  intros x Hx. cbn [Z.min Z.max] in Hx. p10_lia. }
unfold cfg_at. change (w64 (BASE + PF_ROLEV)) with (Z_to_bv 64 (BASE + PF_ROLEV)).
(* 0x88840 .. 0x88888: checks 31 and 32 (both shadow bytes the literal 0), the two stores, the call's arguments,
   the jal to the snprintf trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U20 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [unfold seg_spec.RC_PARSE_W; left; reflexivity|].
    cbn [fst snd]. p10_lia.
  - exists bc, mc. split; [exact Hbc | p10_lia]. }
cbn [ms_mem mkst] in HFr, HG, HF.
try (set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
(* what the run kept, and what it wrote *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (seg_spec.rseg_addr (p_c v) gi + 0x10 <= a < seg_spec.rseg_addr (p_c v) gi + 0x18) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs:=SEGS) E (ss_mem p10_ss) (w_H Wc) memc (ms_mem ms)
    (fun a => seg_spec.rseg_addr (p_c v) gi + 0x10 <= a < seg_spec.rseg_addr (p_c v) gi + 0x18) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U20 in Hrr; lia |]).
  destruct Hin'. }
assert (M1 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth (segs := SEGS) Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity))
    as HR1 end.
cbn [ms_mem restrict] in HR1.
pose proof (field_of_region_any (segs := SEGS) E _ 20 (seg_spec.rseg_addr (p_c v) gi) _ _ _ _ _ 16 4 (SOff 19 0) HR1 U20
  ltac:(p10_in) ltac:(cbn; lia)) as V16.
rewrite p10_den_atom0, E19, unsigned_lit_small in V16 by lia.
rewrite Z.mod_small in V16 by (cbn; lia).
pose proof (p10_sa_val _ _ _ _ _ _ V16) as SV16.
pose proof (field_of_region_any (segs := SEGS) E _ 20 (seg_spec.rseg_addr (p_c v) gi) _ _ _ _ _ 20 4 (SLit 1) HR1 U20
  ltac:(p10_in) ltac:(cbn; lia)) as V20.
cbn [sv_denot] in V20. rewrite unsigned_lit_small in V20 by lia. rewrite Z.mod_small in V20 by (cbn; lia).
pose proof (p10_sa_val _ _ _ _ _ _ V20) as SV20.
(* the registers at the call *)
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_JOIN)) by (p10_rreg HS; exact (codeptr_val E _ HEI)).
assert (Q10 : getr (ms_regs ms) 10 = w64 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE))
  by (p10_rreg HS; cbn [sv_denot]; rewrite U20; reflexivity).
assert (Q11 : getr (ms_regs ms) 11 = w64 96) by (p10_rreg HS; reflexivity).
assert (Q12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_s)).
{ p10_rreg HS. rewrite p10_den_atom0, (img_env_atomP E 276 HEI ltac:(unfold A_TEXT, A_LIM; lia)).
  change 276%nat with (A_OBJ 35). rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64. f_equal; try (vm_compute; reflexivity). }
assert (Q13 : getr (ms_regs ms) 13 = w64 (p_c v + seg_spec.RC_READING))
  by (p10_rreg HS; cbn [sv_denot]; rewrite U24; reflexivity).
assert (QK : forall q, In q [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 q) = getr rX (Z_to_bv 5 q)).
{ intros q Hq. cbn [In] in Hq.
  repeat (destruct Hq as [<- | Hq]; [p10_rreg HS; rewrite p10_den_atom0; apply EE; reflexivity |]). destruct Hq. }
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v))
  by (p10_rreg HS; rewrite p10_den_atom0, (EE 2%nat (Z_to_bv 5 2) eq_refl); exact R2).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (p10_rreg HS; rewrite p10_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl); exact R3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (p10_rreg HS; rewrite p10_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl); exact R4).
pmkst HS.
(* the facts the call reads, at the call's memory *)
assert (KP1 : p10_kept v gi (rdW Wc memc) (rdW Wc (ms_mem ms))).
{ split; [|exact M1]. intros a Ha Hn. apply K1; [exact Ha|]. intros Hw. apply Hn. unfold p10_W. right; left. exact Hw. }
pose proof (p10_k_obj v pos gi _ _ HGEO KP1 lyc Sc Htxt Ht0 Ht1 HOBJ) as OBJ1.
pose proof OBJ1 as (_ & _ & _ & _ & _ & _ & OLIT1 & OROD1 & OSSP1).
pose proof (proj1 HJ) as HART.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HART Hbc) as (_ & _ & _ & _ & HbpresT & _).
pose proof (p10_reading _ _ _ HRC) as (HZR & HNZ & HLT).
assert (HSN : sn_len (96 - 1) (rc_reading cf) = Z.of_nat (length (rc_reading cf)) + 1).
{ unfold sn_len, sn_bytes. change (Z.to_nat (96 - 1)) with 95%nat. rewrite firstn_all2 by lia.
  rewrite length_app. cbn [length]. lia. }
assert (HSB : sn_bytes (96 - 1) (rc_reading cf) = rc_reading cf ++ [0]).
{ unfold sn_bytes. change (Z.to_nat (96 - 1)) with 95%nat. rewrite firstn_all2 by lia. reflexivity. }
assert (HZR1 : sa_zs (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_READING) (rc_reading cf ++ [0])).
{ intros i Hi. pose proof Hi as Hi'. rewrite length_app in Hi'. cbn [length] in Hi'.
  rewrite (p10_k_cf v pos gi _ _ HGEO KP1 (p_c v + seg_spec.RC_READING + Z.of_nat i)); [exact (HZR i Hi)| p10_lia | p10_lia | p10_lia]. }
assert (HTL1 : sa_tail (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_READING + Z.of_nat (length (rc_reading cf)))).
{ intros x Hx. pose proof (Z.mod_pos_bound (p_c v + seg_spec.RC_READING + Z.of_nat (length (rc_reading cf))) 8 ltac:(lia)).
  apply (aview_some_of_apresent SEGS). exact (proj1 (HbpresT x ltac:(p10_lia))). }
assert (HSTRw : sa_str (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_READING) (rc_reading cf))
  by exact (conj (conj HZR1 HNZ) HTL1).
assert (HADDRw : sa_addr (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_READING) (Z.of_nat (length (rc_reading cf)) + 1)).
{ apply (a6_heap_addr B lyc Sc Wc (ms_mem ms) _ _ _ HART); [|lia]. exists bc, mc. split; [exact Hbc | p10_lia]. }
assert (HinFs : In F_s PARSE_FILE_LITS) by (unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity).
destruct (OLIT1 F_s HinFs) as (Hfa & HfS & Hfp & _ & _).
assert (HfA3 : sa_addr (rdW Wc (ms_mem ms)) (seg_litA_rc F_s) 3).
{ pose proof (Hfp lyc Sc Wc (ms_mem ms) _ HART) as H. replace (Z.of_nat (length F_s) + 1) with 3 in H
    by (vm_compute; reflexivity). exact H. }
assert (EFP : seg_litA_rc F_s = 0x21340) by (vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0).
{ assert (S16 : pf_s1 v mod 16 = 0).
  { pose proof (Z.div_mod (pf_s1 v) 32 ltac:(lia)) as D. rewrite S5, Z.add_0_r in D. rewrite D.
    replace (32 * (pf_s1 v / 32)) with ((2 * (pf_s1 v / 32)) * 16) by lia. apply Z_mod_mult. }
  rewrite Zminus_mod, S16, S3. reflexivity. }
assert (Harg3 : argZ (ms_regs ms) 3 = p_c v + seg_spec.RC_READING).
{ unfold argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite Q13. unfold w64. apply unsigned_lit_small. p10_lia. }
assert (HFR : FR_cmd (rdW Wc (ms_mem ms))
    (snp_out CMD_SNP_K (spZ (ms_regs ms)) (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE)
      (sn_len (96 - 1) (rc_reading cf)))
    (seg_litA_rc F_s) (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7]) (rc_reading cf)).
{ pose proof (Z.mod_pos_bound (- (p_c v + seg_spec.RC_READING + Z.of_nat (length (rc_reading cf)) + 1)) 8
    ltac:(lia)) as HMW.
  apply (pfa8b_FR_s_regs _ _ _ _ _ _ Harg3).
  - lia.
  - rewrite EFP. unfold CMD_IMG_LO. lia.
  - rewrite EFP. unfold CMD_GOTW. lia.
  - exact HfS.
  - exact HfA3.
  - unfold snp_out. rewrite Hsp, HSN, EFP.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; p10_lia.
  - p10_lia.
  - exact (pfa8b_bytes_range_aview SEGS (w_H Wc) (ms_mem ms) _ _ HSTRw).
  - lia.
  - exact HSTRw.
  - exact HADDRw.
  - apply (amem_range_sub_app bc (req_size mc) _ _ Hbapp Hbceil); p10_lia.
  - unfold snp_out. rewrite Hsp, HSN.
    repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint, seg_spec.cstr_span; cbn [fst snd]; p10_lia. }
assert (HROM : RtDefs.rt_rom_view SEGS B Wc (ms_mem ms)).
{ intros a (sg & Hsg & Hw & Hr) Hoa Hea. exact (OROD1 a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Hoa Hea). }
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1)).
{ rewrite Q1. apply ret_ok_codeptr_v; [unfold PF_JOIN, AF_reac_segconf_parse_file; lia | reflexivity]. }
assert (Hdest : forall a, seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE <= a <
    seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE + 96 ->
    awr_byte SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
      (ablocks B (p_ly v) (p_S v)) (ablocks B lyc Sc) (frames (p_S v)) lyc [(5, pos)] a /\
    ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - CMD_SNP_K <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v))).
{ intros a Ha. split.
  - right; left. split.
    + exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [unfold seg_spec.RC_PARSE_W; left; reflexivity|].
      cbn [fst snd]. p10_lia.
    + exists bc, mc. split; [exact Hbc | p10_lia].
  - rewrite SPF in S1. p10_lia. }
(* 0x88888: snprintf(&c->seg[gi].role_file, 96, "%s", c->reading) *)
unfold pf_postm, PF_POSTr.
eapply (srr_after_artF SEGS).
{ exact (pfa8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (SIG SS___interceptor_trampoline_snprintf)
    (ASNPRINTF fx) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v))
    (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc _ 0
    (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE) 96 (seg_litA_rc F_s) (rc_reading cf)
    (pf_s1 v - pf_sp0 v) (getr (ms_regs ms) 1)
    HJ Q10 Q11 Q12 ltac:(lia) ltac:(p10_lia) ltac:(p10_lia) Hsp Ho16 ltac:(lia)
    ltac:(rewrite SPF; unfold CMD_SNP_K, ESTACK; lia) Q3 Q4 eq_refl Hraw Hdest
    (fun a Ha _ _ => apresent_writable SEGS _ _ a (proj1 (HbpresT a ltac:(p10_lia))))
    ltac:(apply (amem_range_sub_app bc (req_size mc) _ _ Hbapp Hbceil); p10_lia)
    (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) _ bc mc
      (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE) 96 HART Hbc ltac:(p10_lia) ltac:(p10_lia))
    (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) _ bc mc
      (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE) 96 HART Hbc ltac:(p10_lia) ltac:(p10_lia)
      ltac:(lia))
    ltac:(unfold YCbq.off_img; rewrite HSN; p10_lia) ltac:(rewrite SPF in S1; p10_lia)
    OSSP1 ltac:(unfold gotwA; lia) ltac:(unfold gotwA, CMD_IMG_HI, kImgEnd; lia) ltac:(unfold guardA; lia)
    ltac:(unfold guardA, CMD_IMG_HI, kImgEnd; lia) ltac:(unfold gotwA, CMD_IMG_LO; lia)
    ltac:(unfold guardA, CMD_IMG_LO; lia) HFR ltac:(lia) HROM HFRM). }
(* back at 0x8888c = JOIN, at the FP state fx1 the wrapper returned *)
cbv beta. intros fx1 regs2 mem2 md2 Hfx (HJ2 & HP2 & _ & HBY & HK2 & HPR2 & _).
rewrite Q1.
change (mkCfg (@mkst fx1 regs2 (Z_to_bv 64 (BASE + PF_JOIN)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at (fx := fx1) SEGS (BASE + PF_JOIN) regs2 mem2 md2).
apply (HJN fx1 v pos lyc Sc Wc regs2 mem2 md2 _ nm o ln d gi).
(* what the call kept and wrote *)
assert (KC : p10_kept v gi (rdW Wc memc) (rdW Wc mem2)).
{ split.
  - intros a Ha Hn.
    assert (Hd1 : ~ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE <= a <
                     seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE + sn_len (96 - 1) (rc_reading cf))).
    { rewrite HSN. intros Hd. apply Hn. unfold p10_W. right; right. p10_lia. }
    assert (Hd2 : ~ (pf_sp0 v + (pf_s1 v - pf_sp0 v) - CMD_SNP_K <= a < pf_sp0 v + (pf_s1 v - pf_sp0 v))).
    { intros Hd. apply Hn. unfold p10_W. left. rewrite SPF in S1 |- *. p10_lia. }
    rewrite (HK2 a Ha Hd1 Hd2). exact (proj1 KP1 a Ha Hn).
  - intros a Hv. exact (p10_vis_pres SEGS (w_H Wc) (ms_mem ms) mem2 HPR2 a (M1 a Hv)). }
pose proof (proj1 HJ2) as HAR2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mc HAR2 Hbc) as (_ & _ & _ & _ & HbpresJ & _).
assert (HFIRG1 : pf_rg (ms_regs ms) (a5_FI B v)).
{ unfold pf_rg in *. rewrite Forall_forall in *. intros rv Hrv. rewrite QK; [exact (HFIRG rv Hrv)|].
  unfold a5_FI in Hrv. cbn [In] in Hrv. repeat (destruct Hrv as [<- | Hrv]; [cbn [fst]; p10_in |]). destruct Hrv. }
split; [|split; [exact HMID | split]].
- (* pf_base at fx1, low still in scope *)
  split; [exact HCX|].
  split.
  { split; [exact HJ2|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
    split; [exact (p10_k_saved v pos gi _ _ HGEO KC _ HSAV)|].
    split; [exact (p10_k_flag v pos gi _ _ HGEO KC _ HFLAG)|].
    split; [exact (fxrel_frm0 fx fx1 HFRM Hfx)|].
    exact (a5_rg_pres (ms_regs ms) regs2 _ HP2 (a5_FI_cs B v) HFIRG1). }
  split; [exact (p10_k_obj v pos gi _ _ HGEO KC lyc Sc Htxt Ht0 Ht1 HOBJ)|].
  split; [exact (p10_k_sl v pos gi _ _ HGEO KC HSL) | exact (p10_k_fsh v pos gi _ _ HGEO KC _ HFSH)].
- (* the spine's state: c holds the updated record *)
  split; [|split; [|split]].
  + rewrite (snprintf_s1 96 (rc_reading cf) HNZ) by lia.
    apply (a10b_rconf_role (rdW Wc memc) (rdW Wc mem2) (p_c v) cf gi r (rc_reading cf) HRC HCUR ltac:(lia) HLT HNZ).
    * intros k Hk.
      assert (Hk1 : ~ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE <= seg_spec.rseg_addr (p_c v) gi +
          seg_spec.RS_ROLE + Z.of_nat k < seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE +
          sn_len (96 - 1) (rc_reading cf))) by (rewrite HSN; p10_lia).
      rewrite (HK2 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE + Z.of_nat k) ltac:(p10_lia) Hk1
        ltac:(rewrite SPF in S1; p10_lia)). exact (SV16 k Hk).
    * intros k Hk.
      assert (Hk1 : ~ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE <= seg_spec.rseg_addr (p_c v) gi +
          seg_spec.RS_ROLE_SET + Z.of_nat k < seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE +
          sn_len (96 - 1) (rc_reading cf))) by (rewrite HSN; p10_lia).
      rewrite (HK2 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_SET + Z.of_nat k) ltac:(p10_lia) Hk1
        ltac:(rewrite SPF in S1; p10_lia)). exact (SV20 k Hk).
    * assert (HPR : forall i, (i < 96)%nat -> exists z,
          rdW Wc mem2 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE + Z.of_nat i) = Some z /\ 0 <= z < 256).
      { intros i Hi.
        destruct (rdW Wc mem2 (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE + Z.of_nat i)) as [z|] eqn:Ez.
        - exists z. split; [reflexivity | exact (sa_aview_rng _ _ _ _ _ Ez)].
        - exfalso. exact (aview_some_of_apresent SEGS _ _ _
            (proj1 (HbpresJ (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE + Z.of_nat i) ltac:(p10_lia))) Ez). }
      exists (a10f_view (rdW Wc mem2) (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_ROLE_FILE) 96).
      split; [exact (a10f_view_bytes _ _ _ HPR)|].
      split; [apply a10f_view_len|]. split; [exact HLT|]. split; [exact HNZ|].
      apply nth_ext with (d := 0) (d' := 0).
      { rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, a10f_view_len. cbn [length]. lia. }
      intros i Hi. rewrite length_firstn in Hi. unfold seg_spec.zs in Hi. rewrite length_map, a10f_view_len in Hi.
      rewrite a10f_nth_firstn by lia.
      rewrite a10f_nth_zs by (rewrite a10f_view_len; lia).
      rewrite a10f_view_nth by lia.
      pose proof (HBY (Z.of_nat i) ltac:(rewrite HSN; lia)) as Hb. rewrite Nat2Z.id, HSB in Hb.
      rewrite Hb. cbn [a10f_o0]. apply a10f_unsigned_small. exact (sa_aview_rng _ _ _ _ _ Hb).
    * intros i Hi H1 H2 H3. apply (p10_k_cf v pos gi _ _ HGEO KC); [lia | p10_lia | p10_lia].
  + cbn [pf_cur_ok]. rewrite a10b_upd_len. exact HCUR.
  + exact (p10_k_nm v pos gi _ _ HGEO KC nm HNM).
  + pose proof (pf_next_skipn_lt (p_s v) o Ho) as Hlt.
    pose proof (pf_cnt_mono cf _ _ (Nat.lt_le_incl _ _ Hlt) HCNT) as Hc'.
    unfold pf_cnt in *. rewrite a10b_upd_refused, a10b_upd_overflow. exact Hc'.
- (* the registers at JOIN: callee-saved, the cut's *)
  unfold pf_rg, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    (rewrite HP2 by (unfold acallee_saved; lia); rewrite QK by p10_in; apply (a5_rg_get rX _ _ _ HRG); p10_in).
Qed.
End x.

(* the piece of pf_a10b_k.v at every FP state *)
Theorem pa10_s_ok : PA10_S B.
Proof. intros f0 n HJN. exact (p10s_rolev (fx := f0) n HJN). Qed.
End d.
