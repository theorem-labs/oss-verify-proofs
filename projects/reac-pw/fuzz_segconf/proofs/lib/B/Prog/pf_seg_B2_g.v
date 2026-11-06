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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_j.v, with its module paths and module names changed; 302 of its 359 lines of code are new or changed and 203 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B2 of reac_segconf_parse_file's
   walk (lib/B/Prog/pf_seg_B2.v), its geometry and the cut's objects carried across the segment. The B2 segment lane of
   the image-B G3 walk owner, 2026-10-30. ADAPTED from commit c181e576cd21 lib/A/Prog/pf_a2_g.v (image A):
   names pa2_ -> pb2_, image B's numbers (the real frame 0x160 = 352: s1 = (sp0 - 0x160) & -32, 0x87e38 / 0x87e78;
   STK_reac_segconf_parse_file = 12832, SegInstB STK_values), image B's write set (below), c's slot 0xc8 kept.
   pb2_geo: the numbers at FTAKEN (afn_pre's astk_ok for sp0, the realigned s1, the class-5 frame F of the journal,
   32-aligned, an application range, outside the image range [0x10000, kImgEnd = 0x602000) by the AR's client-image
   law and the ledger's image cover). pb2_Wr: every byte the segment writes - __asan_set_shadow_f8's stack window
   below s1, the slots s1 + 0x88 .. 0xa0, s1 + 0xd8 .. 0xe0, s1 + 0xf0 .. 0xf8, the frame header F .. F + 24, the
   frame's 144 shadow cells SH .. SH + 144. pb2_kept: bytes outside pb2_Wr keep their value and mapped bytes stay
   mapped. pb2_keep_*: from pb2_kept, the cut's objects (pf_obj, pf_lab, sa_rconf, the saved registers, the flag word,
   c's slot 0xc8) at the FTAKEN reader hold at the FRAME reader: each object is an application byte below
   alloc_ceiling outside the frame (pb2_out), so neither it nor its shadow cell is in pb2_Wr; a tail or a shadow hull
   is kept by the mapped clause; the saved registers (sp0 - 0x68 .. sp0), c's slot and the flag word lie outside
   pb2_Wr by the geometry. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
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

(* ---------- arithmetic ---------- *)
Lemma pb2_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma pb2_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* a byte outside an 8-aligned range [F, F + 2048) has its shadow outside the range's first 256 cells *)
Lemma pb2_granule : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 2048) -> 0 <= x ->
  ~ (F / 8 <= x / 8 < F / 8 + 256).
Proof.
intros F x HF Hx H0 [H1 H2]. apply Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. rewrite HF in DF. lia.
Qed.
Lemma pb2_crt_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pb2_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma pb2_le_byte_range : forall v n k, 0 <= YG0f.le_byte v n k < 256.
Proof. intros v n k. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma pb2_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
(* a register of a list *)
Lemma pb2_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma pb2_rg_bv : forall rX L r v (b : bv 5), pf_rg rX L -> In (r, v) L -> bv_unsigned b = r -> getr rX b = w64 v.
Proof. intros rX L r v b H Hin Hb. rewrite <- (Z_to_bv_bv_unsigned 5 b), Hb. exact (pb2_rg rX L r v H Hin). Qed.
Ltac pb2_in := cbn [In app]; repeat first [left; reflexivity | right].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------- the segment's write set and what keeps outside it ---------- *)
(* __asan_set_shadow_f8's window below s1 (the call 0x87f4c at sp = s1); the slots s1 + 0x88 / 0x98 (0x87edc,
   0x87f10), s1 + 0xd8 (0x87f48) and s1 + 0xf0 (0x87ee0, never read); the frame header F .. F + 24 (0x87f08, 0x87f0c,
   0x87f14); the frame's 144 shadow cells (0x87f20-0x87f3c, the call, 0x87f50-0x88070). c's slot s1 + 0xc8 (pf_fi)
   lies outside. *)
Definition pb2_Wr (v : pfv) (pos a : Z) : Prop :=
  (pf_s1 v - ESTACK <= a < pf_s1 v) \/ (pf_s1 v + 0x88 <= a < pf_s1 v + 0xa0) \/
  (pf_s1 v + 0xd8 <= a < pf_s1 v + 0xe0) \/ (pf_s1 v + 0xf0 <= a < pf_s1 v + 0xf8) \/
  (pf_F v pos <= a < pf_F v pos + 24) \/ (pf_SH v pos <= a < pf_SH v pos + 144).
Definition pb2_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb2_Wr v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Lemma pb2_kept_trans : forall v pos rd1 rd2 rd3, pb2_kept v pos rd1 rd2 -> pb2_kept v pos rd2 rd3 ->
  pb2_kept v pos rd1 rd3.
Proof.
intros v pos rd1 rd2 rd3 [K1 M1] [K2 M2]. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (M2 a Ha (M1 a Ha H)).
Qed.
(* the numbers of the frame and the stack at the cut (afn_pre's astk_ok, the journal's class-5 frame) *)
Definition pb2_geoP (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + 12832 <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 368 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\ pf_s1 v mod 16 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\
  (pf_F v pos + 2048 <= 0x7fff7000 \/ 0x10007fff8000 <= pf_F v pos) /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)).
Lemma pb2_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  pb2_geoP v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
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
pose proof (pb2_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply pb2_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | exact HAR]]]].
unfold pb2_geoP, pf_s1.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|]. split; [exact R3|].
split; [lia|]. split; [lia|]. split; [exact H32|]. split; [lia|].
intros a Ha Hf. rewrite <- EF in Hf.
destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
  ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
apply Hz. unfold in_zr. unfold kImgEnd in *. lia.
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : pb2_geoP v pos.
(* a byte the segment never touches, nor its shadow cell: below the allocator's ceiling, an application byte, and
   outside the class-5 frame *)
Definition pb2_out (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ (x < 0x7fff7000 \/ 0x10007fff8000 <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
Lemma pb2_out_nw : forall x, pb2_out x ->
  0 <= x < 2 ^ 64 /\ ~ pb2_Wr v pos x /\ 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ pb2_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx2 & Hx3).
pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (pb2_granule (pf_F v pos) x F8 Hx3 ltac:(lia)) as Gr.
unfold pb2_Wr, pf_SH, shadow_addr, SHADOW_OFF, ESTACK.
split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.
Lemma pb2_out_img : forall x, 0x10000 <= x < kImgEnd -> pb2_out x.
Proof.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & I1). pose proof asan_consts as (C1 & _).
unfold kImgEnd in *. split; [lia|]. split; [lia|]. exact (I1 x Hx).
Qed.
Lemma pb2_out_inimg : forall x, in_img SEGS x -> pb2_out x.
Proof. intros x Hx. apply pb2_out_img. exact (pa_img_range x Hx). Qed.
(* the stack slots of the prologue's saved registers and the frame's flag word *)
Lemma pb2_saved_nw : forall a, pf_sp0 v - 104 <= a < pf_sp0 v -> 0 <= a < 2 ^ 64 /\ ~ pb2_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
unfold pb2_Wr, pf_SH, shadow_addr, SHADOW_OFF, ESTACK. lia.
Qed.
Lemma pb2_c8_nw : forall a, pf_s1 v + 0xc8 <= a < pf_s1 v + 0xd0 -> 0 <= a < 2 ^ 64 /\ ~ pb2_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
unfold pb2_Wr, pf_SH, shadow_addr, SHADOW_OFF, ESTACK. lia.
Qed.
Lemma pb2_flag_nw : forall a, pf_F v pos + 2040 <= a < pf_F v pos + 2048 -> 0 <= a < 2 ^ 64 /\ ~ pb2_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)).
unfold pb2_Wr, pf_SH, shadow_addr, SHADOW_OFF, ESTACK. lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : pb2_kept v pos rd rd'.
Lemma pb2_k_byte : forall x, pb2_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (pb2_out_nw x Hx) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma pb2_k_shadow : forall x, pb2_out x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (pb2_out_nw x Hx) as (_ & _ & H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma pb2_k_zs : forall p l, (forall i, (i < length l)%nat -> pb2_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (pb2_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma pb2_k_bytes : forall p l, (forall i, (i < length l)%nat -> pb2_out (p + Z.of_nat i)) -> sa_bytes rd p l -> sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (pb2_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma pb2_k_rdword : forall a, (forall k, 0 <= k < 8 -> pb2_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (pb2_k_byte _ (Ho k Hk)). Qed.
Lemma pb2_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma pb2_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma pb2_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> pb2_out x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (pb2_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (pb2_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma pb2_k_addr : forall q n, (forall x, q <= x < q + n -> pb2_out x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (pb2_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (pb2_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma pb2_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (pb2_k_str a s); [|exact Hs]. intros x Hx. apply pb2_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma pb2_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pb2_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (pb2_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply pb2_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma pb2_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (pb2_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply pb2_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply pb2_out_img. unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma pb2_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> pb2_out (a + k))
  by (intros a Ha k Hk; apply pb2_out_img; lia).
split; [rewrite (pb2_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (pb2_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* a range inside a live heap block of the cut's state lies outside the frame the segment lays *)
Lemma pb2_out_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc b m x,
  pb2_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  In (b, m) (ablocks B lyc Sc) -> b <= x < b + req_size m -> pb2_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold pb2_out. lia.
Qed.
Lemma pb2_out_sa_heap : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  pb2_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_heap B lyc Sc q n -> q <= x < q + n -> pb2_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc q n x HG HAR Hin EF (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
apply (pb2_out_heap v pos lyc Sc Wc memc mdc b m x HG HAR Hin EF Hb). lia.
Qed.
(* a range inside a side-stack frame of the entry state *)
Lemma pb2_out_fframe : forall v pos lyc Sc (Wc : world SEGS) memc mdc S0 q n x,
  pb2_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> frames Sc = (5, pos) :: frames S0 ->
  frame_addr lyc 5 pos = pf_F v pos -> sa_fframe lyc S0 q n -> q <= x < q + n -> pb2_out v pos x.
Proof.
intros v pos lyc Sc Wc memc mdc S0 q n x HG HAR Hfrs EF (cid & p & Hin & Hc & H1 & H2) Hx.
assert (HinC : In (cid, p) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc cid p HAR HinC) as (Hf0 & Hfc & Happ).
apply in_split in Hin as (l1 & l2 & El).
pose proof (sep_frames_pos SEGS B LAWS lyc Sc Wc memc mdc (5, pos) (cid, p) [] l1 l2 HAR
  ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold pb2_out. lia.
Qed.

(* ---------- the cut's objects, carried across the segment ---------- *)
Lemma pb2_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  pb2_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pb2_kept v pos rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR Hin EF K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> pb2_out v pos x)
  by (intros x Hx; exact (pb2_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H3 Hx)).
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> pb2_out v pos x)
  by (intros x Hx; exact (pb2_out_sa_heap v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H5 Hx)).
split; [apply (pb2_k_str v pos HG rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (pb2_k_addr v pos HG rd rd' K _ _ Ht H2)|]. split; [exact H3|].
split; [exact (pb2_k_addr v pos HG rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (pb2_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (pb2_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (pb2_k_rod v pos HG rd rd' K H8) | exact (pb2_k_ssp v pos HG rd rd' K H9)].
Qed.
Lemma pb2_keep_rconf : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd' cf,
  pb2_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  pb2_kept v pos rd rd' -> sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  sa_rconf rd (p_c v) cf -> sa_rconf rd' (p_c v) cf.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' cf HG HAR Hin EF K Hh (bs & Hb & Henc).
exists bs. split; [|exact Henc]. apply (pb2_k_bytes v pos HG rd rd' K); [|exact Hb].
intros i Hi. destruct Henc as [Hl _].
apply (pb2_out_sa_heap v pos lyc Sc Wc memc mdc _ _ _ HG HAR Hin EF Hh). lia.
Qed.
(* the label: where it lies is the entry's (pf_cx), its bytes and shadow at the cut's reader are pf_lab's *)
Lemma pb2_keep_lab : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  pb2_geoP v pos -> AR SEGS B lyc Sc Wc memc mdc -> frames Sc = (5, pos) :: frames (p_S v) ->
  frame_addr lyc 5 pos = pf_F v pos -> lyc = p_ly v ->
  Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v)) ->
  pf_cx B v -> pb2_kept v pos rd rd' -> pf_lab B v lyc Sc rd -> pf_lab B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR Hfrs EF Ely HPm HCX K (Hos & Hloc).
destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (_ & _ & HL)) & _).
unfold pf_lab. destruct (p_lab v) as [l|] eqn:El; [|split; [exact Hos | exact I]].
destruct HL as (_ & Hwhere & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (Ho : forall x, p_lp v <= x < p_lp v + (Z.of_nat (length l) + 1) -> pb2_out v pos x).
{ intros x Hx. destruct Hwhere as [(b & m & Hb & H1 & H2) | [Hf | (Hi & _)]].
  - apply (pb2_out_sa_heap v pos lyc Sc Wc memc mdc (p_lp v) (Z.of_nat (length l) + 1) x HG HAR Hin EF); [|exact Hx].
    exists b, m. split; [|lia]. apply (Permutation_in _ (Permutation_sym HPm)). exact Hb.
  - rewrite <- Ely in Hf. exact (pb2_out_fframe v pos lyc Sc Wc memc mdc (p_S v) _ _ x HG HAR Hfrs EF Hf Hx).
  - apply (pb2_out_inimg v pos HG). exact (proj1 (Hi x Hx)). }
destruct Hos as (Hnz & Hs). destruct Hloc as (Hw & Ha).
split; [split; [exact Hnz | apply (pb2_k_str v pos HG rd rd' K); [exact Ho | exact Hs]]|].
split; [exact Hw | exact (pb2_k_addr v pos HG rd rd' K _ _ Ho Ha)].
Qed.
(* the prologue's saved registers and the frame's flag word *)
Lemma pb2_keep_saved : forall v pos rd rd' regs, pb2_geoP v pos -> pb2_kept v pos rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs HG K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
intros k Hk. destruct (pb2_saved_nw v pos HG (pf_sp0 v - 8 - 8 * Z.of_nat j + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
(* c's slot s1 + 0xc8 (pf_fi; 0x87ea0) *)
Lemma pb2_keep_c8 : forall v pos rd rd' c, pb2_geoP v pos -> pb2_kept v pos rd rd' ->
  pf_sl rd (pf_s1 v) [(0xc8, c)] -> pf_sl rd' (pf_s1 v) [(0xc8, c)].
Proof.
intros v pos rd rd' c HG K H. apply Forall_cons; [|apply Forall_nil]. apply Forall_inv in H. cbn [fst snd] in *.
rewrite (rdword_ext rd rd'); [exact H|].
intros k Hk. destruct (pb2_c8_nw v pos HG (pf_s1 v + 0xc8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma pb2_keep_flag : forall v pos rd rd', pb2_geoP v pos -> pb2_kept v pos rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos rd rd' HG K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (pb2_flag_nw v pos HG (pf_F v pos + 2048 - 8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
End x.
End d.
