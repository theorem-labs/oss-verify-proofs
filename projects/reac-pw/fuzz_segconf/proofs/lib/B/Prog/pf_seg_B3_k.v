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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B4.v, with its module paths and module names changed; 381 of its 460 lines of code are new or changed and 544 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B3 of reac_segconf_parse_file's
   walk (lib/B/Prog/pf_seg_B3.v, FRAME 0x88074 -> DONE 0x89114 / HEAD 0x881f8), its geometry, its write set, what it
   keeps, and the two mid-segment states. The B3 segment lane of the image-B G3 walk owner, 2026-10-30. ADAPTED from the image-A G3 walk owner's image-A
   kit of segment A2 (lib/A/Prog/pf_a2_g.v, commit 3f59c8d75ed4: pa2_geo, pa2_out, pa2_k_str and the
   other pa2_k lemmas, pa2_keep_obj) and segment A5 (pf_a5_k.v: a5_G, a5_heap_out, a5_img_out), re-derived for B3's writes on image B:
   - pb3_G / pb3_geo: the numbers at FRAME. B's prologue `addi sp,sp,-352; andi sp,sp,-32` (0x87e38, 0x87e78):
     sp0 - 384 <= s1 <= sp0 - 352; STK 12832; the class-5 frame F (2048 bytes, 32-aligned, in the application
     range, off the image), the block c (in the application range, off the image, apart from the frame).
   - label_amem8_of_place: a C string of n bytes and its NUL in a live heap block, a live side-stack frame or the
     image has 8 bytes of application memory past its NUL: in_app's low arm ends at kLowShadowBeg = 0x7fff7000,
     4095 bytes below amem_range's kLowMemEnd - 1; its high arm at ASAN_CEIL < kHighMemEnd - 8. This is
     cmd_args_amem's premise of the snprintf at 0x880cc (RtPFCmd.v:86-91), derived from the contract's three places
     of the label (reac_segconf_parse_file_c.v:180-182): no new premise.
   - pb3_Wr: every byte B3 writes - parse_file's stack window below s1 + 0xd8 (the slots and the snprintf / memset
     windows), c->reading .. c->gen (snprintf 0x880cc, `sw` 0x880fc), cur_name (memset 0x88130) and its two shadow
     cells SH + 4, SH + 5 (0x8811c, 0x88120). pb3_kept: bytes outside pb3_Wr keep their value, mapped bytes stay
     mapped. pb3_keep_obj / _saved / _flag: the cut's objects (pf_obj, the saved registers, the flag word) carried across.
   - pb3_MID1 (0x880d0, after the snprintf) and pb3_MID2 (0x88134, after the memset): the states between B3's three
     pieces. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- arithmetic ---------- *)
Lemma pb3_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Lemma pb3_round32 : forall x, 0 <= x -> x mod 16 = 0 ->
  x - 16 <= x - x mod 32 <= x /\ (x - x mod 32) mod 32 = 0 /\ (x - x mod 32) mod 16 = 0.
Proof.
intros x Hx H16. pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M.
pose proof (Z.div_mod x 16 ltac:(lia)) as D16.
assert (E : x - x mod 32 = 32 * (x / 32)) by lia. rewrite E.
assert (x mod 32 = 0 \/ x mod 32 = 16) by lia.
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* a byte outside an 8-aligned range [F, F + 2048) has its shadow outside the range's 256 cells *)
Lemma pb3_granule : forall F x, F mod 8 = 0 -> ~ (F <= x < F + 2048) -> 0 <= x ->
  ~ (F / 8 <= x / 8 < F / 8 + 256).
Proof.
intros F x HF Hx H0 [H1 H2]. apply Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. rewrite HF in DF. lia.
Qed.
Lemma pb3_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma pb3_den_off : forall E n v k, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. reflexivity. Qed.
Lemma pb3_zrange : forall (f : Z -> bool) lo (n : nat),
  forallb (fun k => f (lo + Z.of_nat k)) (seq 0 n) = true -> forall i, lo <= i < lo + Z.of_nat n -> f i = true.
Proof.
intros f lo n H i Hi. rewrite forallb_forall in H.
specialize (H (Z.to_nat (i - lo)) ltac:(apply in_seq; lia)).
replace (lo + Z.of_nat (Z.to_nat (i - lo))) with i in H by lia. exact H.
Qed.
(* registers of a list *)
Lemma pb3_rg : forall rX L r v, pf_rg rX L -> In (r, v) L -> getr rX (Z_to_bv 5 r) = w64 v.
Proof. intros rX L r v H Hin. exact (proj1 (Forall_forall _ _) H (r, v) Hin). Qed.
Lemma pb3_rg_bv : forall rX L r v (b : bv 5), pf_rg rX L -> In (r, v) L -> bv_unsigned b = r -> getr rX b = w64 v.
Proof. intros rX L r v b H Hin Hb. rewrite <- (Z_to_bv_bv_unsigned 5 b), Hb. exact (pb3_rg rX L r v H Hin). Qed.
Lemma pb3_rg_sub : forall rX L L', pf_rg rX L -> (forall x, In x L' -> In x L) -> pf_rg rX L'.
Proof. intros rX L L' H Hs. unfold pf_rg in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hs x Hx)). Qed.
Lemma pb3_rg_app : forall rX L1 L2, pf_rg rX (L1 ++ L2) <-> pf_rg rX L1 /\ pf_rg rX L2.
Proof. intros rX L1 L2. unfold pf_rg. apply Forall_app. Qed.
Lemma pb3_sl_app : forall rd b L1 L2, pf_sl rd b (L1 ++ L2) <-> pf_sl rd b L1 /\ pf_sl rd b L2.
Proof. intros rd b L1 L2. unfold pf_sl. apply Forall_app. Qed.
Lemma pb3_sl_get : forall rd b L o x, pf_sl rd b L -> In (o, x) L -> rdword rd (b + o) = Some x.
Proof. intros rd b L o x H Hin. exact (proj1 (Forall_forall _ _) H (o, x) Hin). Qed.
Ltac pb3_in := cbn [In app]; repeat first [left; reflexivity | right].
(* the cells of PF_SC_HEAD are PF_SC0's but cur_name's two (4, 5) *)
Lemma pb3_shb_head : forall i, 0 <= i < 144 ->
  pf_shb PF_SC_HEAD i = if (4 <=? i) && (i <? 6) then 0 else pf_shb PF_SC0 i.
Proof.
intros i Hi. apply Z.eqb_eq. revert i Hi.
apply (pb3_zrange (fun i => pf_shb PF_SC_HEAD i =? (if (4 <=? i) && (i <? 6) then 0 else pf_shb PF_SC0 i)) 0 144).
vm_compute. reflexivity.
Qed.

(* the text of the snprintf at 0x880cc: the label, or "reac-pw.conf" (.str.1 0x21360) when there is none, and the
   record after it (c->reading written, gen not yet) *)
Definition pb3_T (lab : option (list Z)) : list Z := match lab with Some l => l | None => S_base end.
Definition pb3_rc1 (rcs : rconf) (lab : option (list Z)) : rconf :=
  RConf (rc_seg rcs) (rc_refusal rcs) (rc_refused rcs) (rc_overflow rcs) (firstn 95 (pb3_T lab)) (rc_gen rcs).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* ---------- the label's 8 bytes past its NUL (the snprintf's cmd_args_amem) ---------- *)
Lemma label_amem8_of_place : forall ly S (W : world SEGS) mem md lp n,
  AR SEGS B ly S W mem md -> 0 <= n ->
  (sa_heap B ly S lp (n + 1) \/ sa_fframe ly S lp (n + 1) \/ sa_img SEGS B lp (n + 1)) ->
  amem_range lp (n + 8).
Proof.
intros ly S W mem md lp n HAR Hn Hw.
pose proof ASAN_CEIL_range as [AC _]. unfold ASAN_CEIL in AC.
destruct Hw as [(b & m & Hb & H1 & H2) | [(cid & p & Hin & Hc & H1 & H2) | Hi]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & H4 & Hce & Happ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; split; lia].
- destruct (al_frames _ _ LAWS ly S W mem md cid p HAR Hin) as (_ & Happ & _ & _).
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd.
  destruct Happ as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; split; lia].
- destruct (Hi (lp + n) ltac:(lia)) as (Hi2 & _).
  pose proof (pa_img_range _ Hi2) as Hr. unfold amem_range, kLowMemEnd, kImgEnd in *. left; lia.
Qed.
(* at the contract's label: its three places are reac_segconf_parse_file_pre's Some arm *)
Lemma pb3_lab_amem : forall v, pf_cx B v ->
  match p_lab v with Some l => amem_range (p_lp v) (Z.of_nat (length l) + 8) | None => True end.
Proof.
intros v HCX. destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & Hl0 & (fe & (_ & _ & HL)) & _).
destruct (p_lab v) as [l|]; [|exact I].
destruct HL as (_ & Hw & _).
apply (label_amem8_of_place (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) (p_lp v) (Z.of_nat (length l))
  (proj1 HPRE) ltac:(lia)).
destruct Hw as [H | [H | (H & _)]]; [left | right; left | right; right]; exact H.
Qed.

Section x. Context {fx : YK11.FPState}.

(* ---------- the numbers at FRAME ---------- *)
Definition pb3_G (v : pfv) (pos : Z) : Prop :=
  alloc_ceiling + STK_reac_segconf_parse_file <= pf_sp0 v /\ pf_sp0 v <= 2 ^ 47 /\ pf_sp0 v mod 16 = 0 /\
  pf_sp0 v - 384 <= pf_s1 v <= pf_sp0 v - 352 /\ pf_s1 v mod 32 = 0 /\
  4096 <= pf_F v pos /\ pf_F v pos + 2048 <= alloc_ceiling /\ pf_F v pos mod 32 = 0 /\ in_app (pf_F v pos) 2048 /\
  (forall a, 0x10000 <= a < kImgEnd -> ~ (pf_F v pos <= a < pf_F v pos + 2048)) /\
  4096 <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= alloc_ceiling /\ in_app (p_c v) seg_spec.SEG_C_SIZE /\
  off_img (p_c v) seg_spec.SEG_C_SIZE /\ p_c v mod 16 = 0 /\
  (p_c v + seg_spec.SEG_C_SIZE <= pf_F v pos \/ pf_F v pos + 2048 <= p_c v).
Lemma pb3_geo : forall v pos lyc Sc Wc rX memc mdc, pf_cx B v -> pf_fi B v pos lyc Sc Wc rX memc mdc ->
  sa_heap B lyc Sc (p_c v) seg_spec.SEG_C_SIZE ->
  pb3_G v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\
  frames Sc = (5, pos) :: frames (p_S v) /\ AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v /\
  (forall a, pf_F v pos <= a < pf_F v pos + 2048 -> apresent (w_H Wc) memc a) /\
  (forall i, 0 <= i < 256 -> apresent (w_H Wc) memc (pf_SH v pos + i)).
Proof.
intros v pos lyc Sc Wc rX memc mdc HCX HFI (bc & mc & Hbc & Hc1 & Hc2).
destruct HCX as (HPRE & _ & _ & _ & _ & _ & _ & _ & (fe & ((Hc0 & Hc16 & _) & _)) & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in Hslo.
destruct HFI as (HJ & Hly & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (H32 & Happ & Hfb & Hsh).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 5 pos HAR Hin) as (Hf0 & Hfc & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & Hb4 & Hbce & Hbapp & _ & _ & Hm).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hr].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hbc) as Hoff.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hbc Hin) as Hsep.
pose proof HAR as (_ & LG & _).
pose proof (pa_img_cover lyc Sc mdc LG) as [IC1 IC2].
assert (EF : frame_addr lyc 5 pos = pf_F v pos) by (subst lyc; reflexivity).
pose proof asan_consts as (C1 & _).
change (fs_frame_bytes 5) with 2048 in *. change (2048 / 8) with 256 in Hsh.
rewrite EF in H32, Happ, Hf0, Hfc, Hfb, Hsh, Hsep.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsh.
change (spZ (p_regs v)) with (pf_sp0 v) in Hal, Hslo, Hshi.
assert (Hsp : 0 <= pf_sp0 v) by lia.
pose proof (pb3_round32 (pf_sp0 v - 352) ltac:(lia) ltac:(apply pb3_m16; [exact Hal | reflexivity])) as (R1 & R2 & R3).
split; [|split; [exact Hin | split; [exact EF | split; [exact Hfrs | split; [exact HAR | split; [exact Hly|]]]]]].
- unfold pb3_G, pf_s1. rewrite ESTK.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold off_img in Hoff |- *.
  unfold in_app in Hbapp |- *.
  split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [exact R2|].
  split; [lia|]. split; [lia|]. split; [exact H32|]. split; [exact Happ|].
  split.
  { intros a Ha Hf. rewrite <- EF in Hf.
    destruct (al_client_img _ _ LAWS lyc Sc Wc memc mdc a HAR
      ltac:(right; left; exists 5, pos; split; [exact Hin | change (fs_frame_bytes 5) with 2048; exact Hf])) as (Hz & _).
    apply Hz. unfold in_zr. unfold kImgEnd in *. lia. }
  split; [lia|]. split; [lia|].
  split; [split; [lia | destruct Hbapp as [_ [Hl | [Hh1 Hh2]]]; [left; lia | right; split; lia]]|].
  split; [destruct Hoff as [Ho | Ho]; [left; lia | right; lia]|].
  split; [exact Hc16 | lia].
- split; [exact (fun a Ha => proj1 (Hfb a Ha))|]. intros i Hi. exact (proj1 (Hsh i Hi)).
Qed.
Lemma pb3_SHb : forall v pos, pb3_G v pos ->
  pf_SH v pos = SHADOW_OFF + pf_F v pos / 8 /\ kLowMemEnd + 512 <= pf_SH v pos /\
  pf_SH v pos + 256 <= kHighShadowEnd /\ pf_F v pos = 8 * (pf_F v pos / 8) /\ pf_F v pos mod 8 = 0.
Proof.
intros v pos (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & _). pose proof asan_consts as (C1 & _).
assert (F8 : pf_F v pos mod 8 = 0).
{ apply Z.mod_divide in F3 as [q Hq]; [|lia]. rewrite Hq. replace (q * 32) with ((4 * q) * 8) by lia. apply Z_mod_mult. }
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
assert (Hq3 : (pf_F v pos + 2048) / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; lia).
assert (Hq4 : alloc_ceiling / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in Hq4.
assert (Hq2 : (pf_F v pos + 2048) / 8 = pf_F v pos / 8 + 256).
{ replace (pf_F v pos + 2048) with (pf_F v pos + 256 * 8) by lia. apply Z.div_add. lia. }
unfold pf_SH, shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd. lia.
Qed.

(* ---------- the segment's write set and what keeps outside it ---------- *)
Definition pb3_Wr (v : pfv) (pos a : Z) : Prop :=
  (pf_sp0 v - STK_reac_segconf_parse_file <= a < pf_s1 v + 0xd8) \/
  (p_c v + seg_spec.RC_READING <= a < p_c v + seg_spec.RC_GEN + 4) \/
  (pf_F v pos + PF_O_CN <= a < pf_F v pos + PF_O_CN + 16) \/ (pf_SH v pos + 4 <= a < pf_SH v pos + 6).
Definition pb3_kept (v : pfv) (pos : Z) (rd rd' : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ pb3_Wr v pos a -> rd' a = rd a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd a <> None -> rd' a <> None).
Lemma pb3_kept_refl : forall v pos rd, pb3_kept v pos rd rd.
Proof. intros v pos rd. split; [intros; reflexivity | intros a _ H; exact H]. Qed.
Lemma pb3_kept_trans : forall v pos rd1 rd2 rd3, pb3_kept v pos rd1 rd2 -> pb3_kept v pos rd2 rd3 ->
  pb3_kept v pos rd1 rd3.
Proof.
intros v pos rd1 rd2 rd3 [K1 M1] [K2 M2]. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (M2 a Ha (M1 a Ha H)).
Qed.

Section k.
Variable v : pfv.
Variable pos : Z.
Hypothesis G : pb3_G v pos.
(* a byte whose shadow cell the segment never writes: below the allocator's ceiling, outside the frame *)
Definition pb3_outsh (x : Z) : Prop := 0 <= x < alloc_ceiling /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
(* a byte the segment never writes, nor its shadow cell: an application byte below the ceiling, outside the frame
   and outside the block c *)
Definition pb3_out (x : Z) : Prop :=
  4096 <= x < alloc_ceiling /\ (x < kLowShadowBeg \/ kHighMemBeg <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048) /\
  ~ (p_c v <= x < p_c v + seg_spec.SEG_C_SIZE).
Lemma pb3_outsh_nw : forall x, pb3_outsh x ->
  0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ pb3_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx3).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (pb3_granule (pf_F v pos) x F8 Hx3 ltac:(lia)) as Gr.
assert (Hq4 : x / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 0xffffff00000 in Hq4.
unfold in_app, kLowShadowBeg, kHighMemBeg in F4, C3.
unfold pb3_Wr, PF_O_CN, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. rewrite ESTK in *.
rewrite ESH. unfold SHADOW_OFF in *. unfold kLowMemEnd, kHighShadowEnd in *.
split; [lia|]. intros [W | [W | [W | W]]]; lia.
Qed.
Lemma pb3_out_nw : forall x, pb3_out x ->
  0 <= x < 2 ^ 64 /\ ~ pb3_Wr v pos x /\ 0 <= SHADOW_OFF + x / 8 < 2 ^ 64 /\ ~ pb3_Wr v pos (SHADOW_OFF + x / 8).
Proof.
intros x (Hx1 & Hx2 & Hx3 & Hx4).
destruct (pb3_outsh_nw x ltac:(split; [lia | exact Hx3])) as (H1 & H2).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
split; [lia|]. split; [|split; [exact H1 | exact H2]].
unfold pb3_Wr, PF_O_CN, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. rewrite ESTK in *.
unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *.
intros [W | [W | [W | W]]]; lia.
Qed.
Lemma pb3_out_img : forall x, 0x10000 <= x < kImgEnd -> pb3_out x.
Proof.
intros x Hx. pose proof G as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I1 & _ & _ & _ & C4 & _).
pose proof asan_consts as (A1 & _).
unfold pb3_out, off_img, kImgEnd, kLowShadowBeg in *. split; [lia|]. split; [lia|]. split; [exact (I1 x Hx)|]. lia.
Qed.
Lemma pb3_out_inimg : forall x, in_img SEGS x -> pb3_out x.
Proof. intros x Hx. apply pb3_out_img. exact (pa_img_range x Hx). Qed.
(* the stack slots of the prologue's saved registers, the frame's flag word, the frame's shadow cells but 4 and 5 *)
Lemma pb3_saved_nw : forall a, pf_sp0 v - 104 <= a < pf_sp0 v -> 0 <= a < 2 ^ 64 /\ ~ pb3_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof asan_consts as (A1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
unfold pb3_Wr, PF_O_CN, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. rewrite ESTK in *.
unfold kLowMemEnd, kHighShadowEnd in *. split; [lia|]. intros [W | [W | [W | W]]]; lia.
Qed.
Lemma pb3_flag_nw : forall a, pf_F v pos + 2040 <= a < pf_F v pos + 2048 -> 0 <= a < 2 ^ 64 /\ ~ pb3_Wr v pos a.
Proof.
intros a Ha. pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof asan_consts as (A1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
unfold in_app, kLowShadowBeg, kHighMemBeg in F4.
unfold pb3_Wr, PF_O_CN, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. rewrite ESTK in *.
unfold kLowMemEnd, kHighShadowEnd in *. split; [lia|]. intros [W | [W | [W | W]]]; lia.
Qed.
Lemma pb3_cell_nw : forall i, 0 <= i < 144 -> ~ (4 <= i < 6) ->
  0 <= pf_SH v pos + i < 2 ^ 64 /\ ~ pb3_Wr v pos (pf_SH v pos + i).
Proof.
intros i Hi Hn. pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof asan_consts as (A1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
unfold in_app, kLowShadowBeg, kHighMemBeg in F4, C3.
unfold pb3_Wr, PF_O_CN, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. rewrite ESTK in *.
unfold kLowMemEnd, kHighShadowEnd in *. split; [lia|]. intros [W | [W | [W | W]]]; lia.
Qed.
(* a byte of the block c outside the fields reading .. gen, and its shadow *)
Lemma pb3_cbyte_nw : forall a, p_c v <= a < p_c v + seg_spec.SEG_C_SIZE ->
  ~ (p_c v + seg_spec.RC_READING <= a < p_c v + seg_spec.RC_GEN + 4) -> 0 <= a < 2 ^ 64 /\ ~ pb3_Wr v pos a.
Proof.
intros a Ha Hn. pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof asan_consts as (A1 & _). pose proof STK_values as (_ & _ & _ & ESTK & _).
unfold in_app, kLowShadowBeg, kHighMemBeg in F4, C3.
unfold pb3_Wr, PF_O_CN, seg_spec.RC_READING, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. rewrite ESTK in *.
unfold kLowMemEnd, kHighShadowEnd in *. split; [lia|]. intros [W | [W | [W | W]]]; lia.
Qed.

Section r.
Variables rd rd' : reader.
Hypothesis K : pb3_kept v pos rd rd'.
Lemma pb3_k_byte : forall x, pb3_out x -> rd' x = rd x.
Proof. intros x Hx. destruct (pb3_out_nw x Hx) as (H0 & H1 & _). exact (proj1 K x H0 H1). Qed.
Lemma pb3_k_shadow : forall x, pb3_outsh x -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8).
Proof. intros x Hx. destruct (pb3_outsh_nw x Hx) as (H0 & H1). exact (proj1 K _ H0 H1). Qed.
Lemma pb3_k_zs : forall p l, (forall i, (i < length l)%nat -> pb3_out (p + Z.of_nat i)) -> sa_zs rd p l -> sa_zs rd' p l.
Proof. intros p l Ho H i Hi. rewrite (pb3_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma pb3_k_bytes : forall p l, (forall i, (i < length l)%nat -> pb3_out (p + Z.of_nat i)) -> sa_bytes rd p l ->
  sa_bytes rd' p l.
Proof. intros p l Ho H i Hi. rewrite (pb3_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma pb3_k_rdword : forall a, (forall k, 0 <= k < 8 -> pb3_out (a + k)) -> rdword rd' a = rdword rd a.
Proof. intros a Ho. apply rdword_ext. intros k Hk. exact (pb3_k_byte _ (Ho k Hk)). Qed.
Lemma pb3_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd e -> sa_tail rd' e.
Proof.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma pb3_k_hull : forall q n, 0 <= q -> q + n <= 2 ^ 63 -> 0 < n -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros q n H0 H1 Hn H s Hs. apply (proj2 K s); [|exact (H s Hs)].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (q + n - 1) 8 ltac:(lia)).
pose proof (Z.div_pos (2147450880 + q / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)).
lia.
Qed.
Lemma pb3_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> pb3_out x) -> sa_str rd p s ->
  sa_str rd' p s.
Proof.
intros p s Ho [[Hz Hn] Ht].
destruct (Ho (p + Z.of_nat (length s)) ltac:(lia)) as (He & _).
pose proof asan_consts as (C1 & _).
split; [split; [|exact Hn] | exact (pb3_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (pb3_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma pb3_k_addr : forall q n, (forall x, q <= x < q + n -> pb3_outsh x) -> sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros q n Ho (H0 & H1 & H2 & H3 & H4). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
split; [|intros Hn; exact (pb3_k_hull _ _ H0 H1 Hn (H4 Hn))].
intros x Hx. destruct (H3 x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (pb3_k_shadow x (Ho x Hx)). exact Hs.
Qed.
Lemma pb3_out_outsh : forall x, pb3_out x -> pb3_outsh x.
Proof. intros x (H1 & _ & H3 & _). split; [lia | exact H3]. Qed.
Lemma pb3_k_lit : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B rd' a s.
Proof.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
apply (pb3_k_str a s); [|exact Hs]. intros x Hx. apply pb3_out_inimg. exact (proj1 (Hi x ltac:(lia))).
Qed.
Lemma pb3_k_cat : forall cat, sa_cat SEGS B rd cat -> sa_cat SEGS B rd' cat.
Proof.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (pb3_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (pb3_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply pb3_out_inimg. apply Hi. unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma pb3_k_rod : arodata_okP SEGS RLO_A RHI_A B rd -> arodata_okP SEGS RLO_A RHI_A B rd'.
Proof.
intros H a Hro Ho He. rewrite (pb3_k_byte a); [exact (H a Hro Ho He)|].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply pb3_out_inimg. exists sg. split; [exact Hsg | exact Hr].
- apply pb3_out_img. pose proof pf_B_values as (E1 & E2 & _). rewrite E1, E2 in Hr. unfold kImgEnd. lia.
Qed.
Lemma pb3_k_ssp : sa_ssp rd gotwA guardA -> sa_ssp rd' gotwA guardA.
Proof.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> pb3_out (a + k))
  by (intros a Ha k Hk; apply pb3_out_img; lia).
split; [rewrite (pb3_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (pb3_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End r.
End k.

(* a byte of a live heap block of the cut's state: an application byte below the ceiling, outside the frame *)
Lemma pb3_heap_out : forall v pos lyc Sc (Wc : world SEGS) memc mdc q n x,
  pb3_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_heap B lyc Sc q n -> q <= x < q + n ->
  4096 <= x < alloc_ceiling /\ (x < kLowShadowBeg \/ kHighMemBeg <= x) /\ ~ (pf_F v pos <= x < pf_F v pos + 2048).
Proof.
intros v pos lyc Sc Wc memc mdc q n x HG HAR Hin EF (b & m & Hb & H1 & H2) Hx.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & H4 & Hc & Happ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as [_ Hr].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m 5 pos HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold kLowShadowBeg, kHighMemBeg. lia.
Qed.

(* ---------- the cut's objects, carried across the segment ---------- *)
Lemma pb3_keep_obj : forall v pos lyc Sc (Wc : world SEGS) memc mdc rd rd',
  pb3_G v pos -> AR SEGS B lyc Sc Wc memc mdc -> In (5, pos) (frames Sc) -> frame_addr lyc 5 pos = pf_F v pos ->
  sa_disj (p_t v) (seg_spec.cstr_span (p_t v) (p_s v)) (p_c v) seg_spec.SEG_C_SIZE ->
  pb3_kept v pos rd rd' -> pf_obj B v lyc Sc rd -> pf_obj B v lyc Sc rd'.
Proof.
intros v pos lyc Sc Wc memc mdc rd rd' HG HAR Hin EF Hdj K (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
assert (Hsp : Z.of_nat (length (p_s v)) + 1 <= seg_spec.cstr_span (p_t v) (p_s v)).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)). lia. }
assert (Ht : forall x, p_t v <= x < p_t v + pf_len v -> pb3_out v pos x).
{ intros x Hx. destruct (pb3_heap_out v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H3 Hx) as (X1 & X2 & X3).
  unfold pb3_out. split; [lia|]. split; [exact X2|]. split; [exact X3|].
  unfold sa_disj, pf_len in *. lia. }
assert (Hc : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE -> pb3_outsh v pos x).
{ intros x Hx. destruct (pb3_heap_out v pos lyc Sc Wc memc mdc _ _ x HG HAR Hin EF H5 Hx) as (X1 & X2 & X3).
  split; [lia | exact X3]. }
split; [apply (pb3_k_str v pos HG rd rd' K); [intros x Hx; apply Ht; unfold pf_len; lia | exact H1]|].
split; [exact (pb3_k_addr v pos HG rd rd' K _ _ (fun x Hx => pb3_out_outsh v pos x (Ht x Hx)) H2)|]. split; [exact H3|].
split; [exact (pb3_k_addr v pos HG rd rd' K _ _ Hc H4)|]. split; [exact H5|].
split; [exact (pb3_k_cat v pos HG rd rd' K _ H6)|].
split; [intros x Hx; exact (pb3_k_lit v pos HG rd rd' K _ _ (H7 x Hx))|].
split; [exact (pb3_k_rod v pos HG rd rd' K H8) | exact (pb3_k_ssp v pos HG rd rd' K H9)].
Qed.
(* the prologue's saved registers and the frame's flag word *)
Lemma pb3_keep_saved : forall v pos rd rd' regs, pb3_G v pos -> pb3_kept v pos rd rd' ->
  pf_saved rd (pf_sp0 v) regs -> pf_saved rd' (pf_sp0 v) regs.
Proof.
intros v pos rd rd' regs HG K H j r Hj. rewrite (rdword_ext rd rd'); [exact (H j r Hj)|].
assert (Hj13 : (j < 13)%nat) by (change 13%nat with (length PF_SAVED); apply nth_error_Some; rewrite Hj; discriminate).
intros k Hk. destruct (pb3_saved_nw v pos HG (pf_sp0 v - 8 - 8 * Z.of_nat j + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
Lemma pb3_keep_flag : forall v pos rd rd', pb3_G v pos -> pb3_kept v pos rd rd' ->
  rdword rd (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) ->
  rdword rd' (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos).
Proof.
intros v pos rd rd' HG K H. rewrite (rdword_ext rd rd'); [exact H|]. change (fs_frame_bytes 5) with 2048.
intros k Hk. destruct (pb3_flag_nw v pos HG (pf_F v pos + 2048 - 8 + k) ltac:(lia)) as (H0 & H1).
exact (proj1 K _ H0 H1).
Qed.
(* the frame's shadow cells but cur_name's two *)
Lemma pb3_keep_cells : forall v pos rd rd' i, pb3_G v pos -> pb3_kept v pos rd rd' -> 0 <= i < 144 -> ~ (4 <= i < 6) ->
  rd' (pf_SH v pos + i) = rd (pf_SH v pos + i).
Proof.
intros v pos rd rd' i HG K Hi Hn. destruct (pb3_cell_nw v pos HG i Hi Hn) as (H0 & H1). exact (proj1 K _ H0 H1).
Qed.
(* the block c's bytes outside reading .. gen *)
Lemma pb3_keep_cbyte : forall v pos rd rd' a, pb3_G v pos -> pb3_kept v pos rd rd' ->
  p_c v <= a < p_c v + seg_spec.SEG_C_SIZE ->
  ~ (p_c v + seg_spec.RC_READING <= a < p_c v + seg_spec.RC_GEN + 4) -> rd' a = rd a.
Proof.
intros v pos rd rd' a HG K Ha Hn. destruct (pb3_cbyte_nw v pos HG a Ha Hn) as (H0 & H1). exact (proj1 K _ H0 H1).
Qed.
End x.

(* ---------- the states between the segment's pieces ---------- *)
(* pf_fi's registers: sp, gp, tp, s0, s1, s4 *)
Definition PB3_FI (v : pfv) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)].
Section y. Context {fx : YK11.FPState}.
(* MID1, 0x880d0 (the snprintf at 0x880cc returned): c->reading holds the label's first 95 bytes and a NUL; s5 = SH,
   s6 = c + 0x40e0 (0x880a4), s7 = c + 0x4080 (0x880a8), s11 = t; the slots 0x88, 0x98, 0xd8 (FRAME's) and 0xc8
   (c); the frame's shadow as FRAME has it; every other byte the cut's but pb3_Wr's *)
Definition pb3_MID1 (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memA : word -> option byte) (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  pb3_kept v pos (rdW Wc memA) (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (pb3_rc1 (p_rcs v) (p_lab v)) /\
  pf_sl (rdW Wc memc) (pf_s1 v)
    [(0x88, pf_F v pos); (0x98, pf_F v pos); (0xd8, pf_SH v pos + 8); (0xc8, p_c v)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC0 /\
  pf_rg rX (PB3_FI v ++ [(21, pf_SH v pos); (22, p_c v + seg_spec.RC_GEN); (23, p_c v + seg_spec.RC_READING);
    (27, p_t v)]).
(* MID2, 0x88134 (the memset at 0x88130 returned): c holds pf_start (gen + 1 stored at 0x880fc); cur_name in scope
   (cells 4, 5 zero, 0x8811c / 0x88120) and zero; the slots 0x18, 0x48, 0x20, 0x40 (0x8810c .. 0x88128); s3 = &c->n
   (0x880f4), s2 = 0x3000 (0x880e8) *)
Definition pb3_MID2 (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (memA : word -> option byte) (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 /\
  pb3_kept v pos (rdW Wc memA) (rdW Wc memc) /\
  sa_rconf (rdW Wc memc) (p_c v) (pf_start (p_rcs v) (p_lab v)) /\
  pf_sl (rdW Wc memc) (pf_s1 v)
    [(0x88, pf_F v pos); (0x98, pf_F v pos); (0xd8, pf_SH v pos + 8); (0xc8, p_c v);
     (0x18, shadow_addr (p_c v + seg_spec.RC_GEN)); (0x48, p_c v + seg_spec.RC_READING);
     (0x20, p_c v + seg_spec.RC_GEN); (0x40, pf_F v pos + PF_O_CN)] /\
  pf_fsh (rdW Wc memc) (pf_SH v pos) PF_SC_HEAD /\
  (forall i, 0 <= i < 16 -> rdW Wc memc (pf_F v pos + PF_O_CN + i) = Some 0) /\
  pf_rg rX (PB3_FI v ++ [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000); (27, p_t v)]).
End y.
End d.
