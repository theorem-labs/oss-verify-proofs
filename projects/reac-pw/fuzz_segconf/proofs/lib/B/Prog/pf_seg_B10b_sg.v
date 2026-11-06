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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths, module names and numbers changed; 536 of its 623 lines of code are new or changed and 4966 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B4.v, with its module paths and module names changed; 264 of its 345 lines of code are new or changed and 542 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the geometry and the
   keep lemmas of piece PB10_S of segment B10b of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B10b_k.v:
   HA_JOIN n -> H_ROLEV n). A B10b sub-lane of the image-B G3 walk owner, 2026-10-30. proves no function (kind: helper
   lemmas of a segment lemma of reac_segconf_parse_file's walk); no instruction is walked here.
   ADAPTED from the B10b segment lane's lib/B/Prog/pf_seg_B10b_j.v (961c19ce3f65: b10j_geo, b10j_SHb, the b10j_k_* /
   b10j_keep_* reader lemmas, the image-A A2 segment lane's pf_a2_g.v form), with this piece's write set in place of the frame's
   shadow cells:
     b10s_Wr: the block c (the two `sw` of 0x88d90 / 0x88dac into c->seg[gi].role / role_set and the snprintf
       destination &c->seg[gi].role_file, 0x88dc4) and the snprintf wrapper's scratch window [s1 - 8192, s1)
       (CMD_SNP_K = 2 * ESTACK below the call's sp = s1).
     b10s_cP: where the block c lies (pf_obj's sa_heap c SEG_C_SIZE through the allocator's block law): an
       application range below alloc_ceiling, off the image, apart from the class-5 frame, c mod 16 = 0 (pf_tf).
   Every object of the cut but the block's bytes (the text, the block's shadow, the catalogue, the literals, the
   read-only view, the guard cells, the class-5 frame and its shadow, the real stack's slots and saved registers)
   lies outside b10s_Wr, so b10s_kept carries it. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic (b10j's, from pf_a2_g.v) ---------- *)
Lemma b10s_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma b10s_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma b10s_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Ltac b10s_in := cbn [In app]; repeat first [left; reflexivity | right].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Lemma b10s_PF_SL_offs : forall v pos ov, In ov (PF_SL v pos) -> 0x00 <= fst ov <= 0xd8.
Proof.
intros v pos ov H. unfold PF_SL in H. cbn [In] in H.
repeat (destruct H as [<- | H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ---------- the geometry at ROLEV (b10j_geo) ---------- *)
Definition b10s_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma b10s_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  b10s_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc.
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI.
destruct HCX as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in Hfc, Happ.
rewrite EF in H32, Happ, Hf0, Hfc.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (b10s_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply b10s_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold b10s_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.
Lemma b10s_SHb : forall v pos, b10s_geoP v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ 0x7fff8000 + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= 0x10007fff8000 /\ pf_F v pos = 8 * (pf_F v pos / 8).
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
unfold pf_SH, shadow_addr, SHADOW_OFF. lia.
Qed.

(* ---------- where the block c lies ---------- *)
Definition b10s_cP (v : pfv) (pos : Z) : Prop :=
  4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ p_c v mod 16 = 0 /\
  (p_c v + seg_spec.SEG_C_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= p_c v) /\
  (p_c v + seg_spec.SEG_C_SIZE <= 0x10000 \/ 0x602000 <= p_c v) /\
  (p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v).
Lemma b10s_cblk : forall v pos lyc Sc Wc memc mdc,
  AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pf_tf v pos -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  b10s_cP v pos /\ exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= p_c v /\
    p_c v + seg_spec.SEG_C_SIZE <= b + req_size m.
Proof.
intros v pos lyc Sc Wc memc mdc HAR Hin EF HTF (b & m & Hb & H1 & H2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _ & _ & Hm).
pose proof (blk_off_imgP B lyc Sc Wc memc mdc b m HAR Hb) as Hoff.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
assert (Hr : m <= req_size m) by (unfold req_size; destruct (m =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
pose proof HTF as (_ & Hc16 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold off_img in Hoff.
unfold seg_spec.SEG_C_SIZE in *.
split; [|exists b, m; split; [exact Hb | split; lia]].
unfold b10s_cP, seg_spec.SEG_C_SIZE. split; [lia|]. split; [lia|]. split; [exact Hc16|]. split; [lia|]. split; lia.
Qed.

(* ---------- the piece's write set and what keeps outside it ---------- *)
Definition b10s_Wr (v : pfv) (a : Z) : Prop :=
  (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) \/ (pf_s1 v - 8192 <= a < pf_s1 v).
Definition b10s_kept (v : pfv) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ b10s_Wr v a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Lemma b10s_kept_trans : forall v rd1 rd2 rd3, b10s_kept v rd1 rd2 -> b10s_kept v rd2 rd3 -> b10s_kept v rd1 rd3.
Proof.
intros v rd1 rd2 rd3 [K1 M1] [K2 M2]. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (M2 a Ha (M1 a Ha H)).
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : b10s_geoP v pos.
Hypothesis GC : b10s_cP v pos.
(* a byte below the allocator's ceiling outside the block c *)
Definition b10s_out (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ ~ (p_c v <= x < p_c v + seg_spec.SEG_C_SIZE).
Lemma b10s_out_nw : forall x, b10s_out x -> 0 <= x < 2 ^ 64 /\ ~ b10s_Wr v x.
Proof using G GC.
intros x (Hx1 & Hx2). pose proof G as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
unfold b10s_Wr. split; [lia|]. intros [H | H]; [exact (Hx2 H) | lia].
Qed.
(* the shadow byte of an address below the ceiling: shadow memory, not the (application) block, not the window *)
Lemma b10s_sh_nw : forall x, 0 <= x < alloc_ceiling ->
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ b10s_Wr v (SHADOW_OFF + x / 8).
Proof using G GC.
intros x Hx. pose proof G as (S1 & S2 & S3 & S4 & _). pose proof GC as (C1 & C2 & _ & C4 & _).
pose proof asan_consts as (A1 & _).
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
unfold b10s_Wr, SHADOW_OFF, seg_spec.SEG_C_SIZE in *. lia.
Qed.
Lemma b10s_stack_nw : forall a, pf_s1 v <= a < 2 ^ 64 -> ~ b10s_Wr v a.
Proof using G GC.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & _). pose proof GC as (C1 & C2 & _).
unfold b10s_Wr. lia.
Qed.
Lemma b10s_frame_out : forall x, pf_F v pos <= x < pf_F v pos + 2048 -> b10s_out x.
Proof using G GC.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & F1 & F2 & _). pose proof GC as (_ & _ & _ & _ & _ & C6).
unfold b10s_out, seg_spec.SEG_C_SIZE in *. lia.
Qed.
Lemma b10s_out_img : forall x, 0x10000 <= x < kImgEnd -> b10s_out x.
Proof using G GC.
intros x Hx. pose proof GC as (_ & _ & _ & _ & C5 & _). pose proof asan_consts as (A1 & _).
unfold b10s_out, kImgEnd, seg_spec.SEG_C_SIZE in *. lia.
Qed.
Lemma b10s_out_inimg : forall x, in_img SEGS x -> b10s_out x.
Proof using G GC. intros x Hx. apply b10s_out_img. exact (pa_img_range x Hx). Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : b10s_kept v rd rd'.
Lemma b10s_k_byte : forall x, b10s_out x -> rd' x = rd x.
Proof using G GC K. intros x Hx. destruct (b10s_out_nw x Hx) as (H0 & H1). exact (proj1 K x H0 H1). Qed.
Lemma b10s_k_shadow : forall x, 0 <= x < alloc_ceiling -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof using G GC K. intros x Hx. destruct (b10s_sh_nw x Hx) as (H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma b10s_k_stack : forall a, pf_s1 v <= a < 2 ^ 64 -> rd' a = rd a.
Proof using G GC K. intros a Ha. apply (proj1 K); [pose proof G as (S1 & S2 & S3 & S4 & _); pose proof asan_consts as (A1 & _); lia|].
exact (b10s_stack_nw a Ha). Qed.
Lemma b10s_k_zs : forall p l, (forall i, (i < length l)%nat -> b10s_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof using G GC K. intros p l Ho H i Hi. rewrite (b10s_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b10s_k_bytes : forall p l, (forall i, (i < length l)%nat -> b10s_out (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof using G GC K. intros p l Ho H i Hi. rewrite (b10s_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma b10s_k_rdword : forall a, (forall k, 0 <= k < 8 -> b10s_out (a + k)) -> rdword rd' a = rdword rd a.
Proof using G GC K. intros a Ho. apply rdword_ext. intros k Hk. exact (b10s_k_byte _ (Ho k Hk)). Qed.
Lemma b10s_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof using G GC K.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma b10s_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof using G GC K.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma b10s_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> b10s_out x) -> sa_str rd p s -> sa_str rd' p s.
Proof using G GC K.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (b10s_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (b10s_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma b10s_k_addr : forall q n, (forall x, q <= x < q + n -> 0 <= x < alloc_ceiling) -> sa_addr rd q n -> sa_addr rd' q n.
Proof using G GC K.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (b10s_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (b10s_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma b10s_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof using G GC K.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (b10s_k_str a s); [|exact Hs]. intros x Hx. apply b10s_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma b10s_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof using G GC K.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (b10s_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (b10s_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply b10s_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma b10s_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof using G GC K.
intros H a Hro Ho He. rewrite (b10s_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply b10s_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply b10s_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma b10s_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof using G GC K.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> b10s_out (a + k))
  by (intros a Ha k Hk; apply b10s_out_img; lia).
split; [rewrite (b10s_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (b10s_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* the text's span is apart from the block (reader_pre's sa_disj, from the contract's premise) *)
Lemma b10s_text_disj : forall v, pf_cx B v ->
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE.
Proof.
intros v HCX. destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & HP) & _).
destruct HP as (HR & _). destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HD & _). exact HD.
Qed.
Lemma b10s_span_ge : forall a s, Z.of_nat (length s) + 1 <= seg_spec.cstr_span a s.
Proof. intros a s. unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia. Qed.

(* a range inside a live heap block of the cut's state lies below the ceiling *)
Lemma b10s_heap_low : forall lyc Sc (Wc : world SEGS) memc mdc q n x,
  AR SEGS B lyc Sc Wc memc mdc -> sa_heap B lyc Sc q n -> q <= x < q + n -> 4096 <= x < alloc_ceiling.
Proof.
intros lyc Sc Wc memc mdc q n x HAR (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & _ & _ & _ & Hm).
assert (Hr : m <= req_size m) by (unfold req_size; destruct (m =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
lia.
Qed.

(* ---------- the cut's objects, carried across the piece ---------- *)
Lemma b10s_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  b10s_geoP v pos -> b10s_cP v pos -> pf_cx B v -> AR SEGS B lyc Sc Wc memc mdc ->
  b10s_kept v rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HC HCX HAR K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
pose proof (b10s_text_disj v HCX) as HD. pose proof (b10s_span_ge (p_t v) (p_s v)) as HSP.
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> b10s_out v x).
{ intros x Hx. pose proof (b10s_heap_low lyc Sc Wc memc mdc _ _ x HAR H3 Hx) as Hl.
  unfold pf_len, sa_disj in *. split; [exact Hl | lia]. }
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> 0 <= x < alloc_ceiling)
  by (intros x Hx; pose proof (b10s_heap_low lyc Sc Wc memc mdc _ _ x HAR H5 Hx); lia).
assert (Ht' : forall x, p_t v <= x < p_t v + pf_len v -> 0 <= x < alloc_ceiling)
  by (intros x Hx; destruct (Ht x Hx) as (Hl & _); lia).
split; [apply (b10s_k_str v pos HG HC rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (b10s_k_addr v pos HG HC rd rd' K _ _ Ht' H2)|]. split; [exact H3|].
split; [exact (b10s_k_addr v pos HG HC rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (b10s_k_cat v pos HG HC rd rd' K _ H6)|].
split; [intros x Hx; exact (b10s_k_lit v pos HG HC rd rd' K _ _ (H7 x Hx))|].
split; [exact (b10s_k_rod v pos HG HC rd rd' K H8) | exact (b10s_k_ssp v pos HG HC rd rd' K H9)].
Qed.
Lemma b10s_keep_saved : forall v pos rd rd' regs, b10s_geoP v pos -> b10s_cP v pos -> b10s_kept v rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs HG HC K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (b10s_k_stack v pos HG HC rd rd' K). lia.
Qed.
Lemma b10s_keep_flag : forall v pos rd rd', b10s_geoP v pos -> b10s_cP v pos -> b10s_kept v rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos rd rd' HG HC K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. apply (b10s_k_byte v pos HG HC rd rd' K). apply (b10s_frame_out v pos HG HC). lia.
Qed.
Lemma b10s_keep_slot : forall v pos rd rd' off w, b10s_geoP v pos -> b10s_cP v pos -> b10s_kept v rd rd' ->
  0 <= off <= 0xd8 -> rdword rd (pf_s1 v + off) = Some w -> rdword rd' (pf_s1 v + off) = Some w.
Proof.
intros v pos rd rd' off w HG HC K Ho H. rewrite (rdword_ext rd rd'); [exact H|].
pose proof HG as (S1 & S2 & S3 & S4 & _). pose proof asan_consts as (C1 & _).
intros k Hk. apply (b10s_k_stack v pos HG HC rd rd' K). lia.
Qed.
Lemma b10s_keep_sl : forall v pos rd rd', b10s_geoP v pos -> b10s_cP v pos -> b10s_kept v rd rd' ->
  pf_sl rd (pf_s1 v) (PF_SL v pos) -> pf_sl rd' (pf_s1 v) (PF_SL v pos).
Proof.
intros v pos rd rd' HG HC K H. unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
pose proof (b10s_PF_SL_offs v pos ov Hov) as Ho.
exact (b10s_keep_slot v pos rd rd' (fst ov) (snd ov) HG HC K Ho (H ov Hov)).
Qed.
Lemma b10s_keep_nm : forall v pos rd rd' nm, b10s_geoP v pos -> b10s_cP v pos -> b10s_kept v rd rd' ->
  pf_nm rd (pf_F v pos + PF_O_CN) nm -> pf_nm rd' (pf_F v pos + PF_O_CN) nm.
Proof.
intros v pos rd rd' nm HG HC K (f & Hb & Henc). exists f. split; [|exact Henc].
intros i Hi. destruct Henc as [Hl _]. rewrite Hl in Hi. unfold PF_O_CN.
rewrite (b10s_k_byte v pos HG HC rd rd' K); [exact (Hb i ltac:(lia))|].
apply (b10s_frame_out v pos HG HC). lia.
Qed.
Lemma b10s_keep_fsh : forall v pos rd rd' sc, b10s_geoP v pos -> b10s_cP v pos -> b10s_kept v rd rd' ->
  pf_fsh rd (pf_SH v pos) sc -> pf_fsh rd' (pf_SH v pos) sc.
Proof.
intros v pos rd rd' sc HG HC K H i Hi.
destruct (b10s_SHb v pos HG) as (ESH & SH1 & SH2 & F8).
pose proof HG as (_ & _ & _ & _ & _ & _ & F1 & F2 & _).
assert (E : pf_SH v pos + i = SHADOW_OFF + (pf_F v pos + 8 * i) / 8).
{ rewrite ESH. rewrite F8 at 2. replace (8 * (pf_F v pos / 8) + 8 * i) with ((pf_F v pos / 8 + i) * 8) by lia.
  rewrite Z.div_mul by lia. lia. }
rewrite E, (b10s_k_shadow v pos HG HC rd rd' K) by lia. rewrite <- E. exact (H i Hi).
Qed.
End x.
End d.
