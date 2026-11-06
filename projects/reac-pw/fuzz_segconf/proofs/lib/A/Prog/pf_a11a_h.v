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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_s.v, with its module names changed; 951 of its 1055 lines of code are new or changed and 539 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the hit arm of segment A11a of reac_segconf_parse_file's walk,
   a11a_hit_ok : HA_LOWOUT n -> A11_HIT_stmt n (lib/A/Prog/pf_a11a_k.v). Part of segment A11a's proof (the hit arm), by the G3 walk owner,
   2026-10-30. proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk -- A11a's hit arm,
   two snprintf calls into the heap block).

   THE CODE (dis/reac_segconf_parse_file.fuzz_segconf.asan.s, 0x88540 .. 0x8859c, 24 instructions, 1 inline check):
     HIT     0x88540 ld a4,0xb0(s1); a0 = a4 + 0x24; a2 = 0x21340 ("%s", listing object 35); a1 = 24; a3 = s4 (low146);
                     s4 = a4 (cur); 0x8855c jal snprintf          snprintf(&cur->model, 24, "%s", low146)
     RET_SN1 0x88560 a0 = s4 + 0x3c; check #27 (store4); 0x88578 sw 1,0x3c(s4); a0 = s4 + 0x40; a2 = 0x21340;
                     a1 = 96; a3 = slot 0x58 (c + RC_READING); 0x88590 jal snprintf
                                                                  snprintf(&cur->model_file, 96, "%s", c->reading)
     RET_SN2 0x88594 s8 = slot 0x90 (c); a0 = -8; 0x8859c j LOWOUT
   THE PROOF. Three seeds (pa_entry_st_ok_full), one at each of HIT, RET_SN1 and RET_SN2, each with only the slot or
   cell it reads or writes as a region; the runs to the two jal and to LOWOUT (plain executor at HIT and RET_SN2, the
   token executor at RET_SN1 for check #27, decided by the shadow entry over cur + 0x3c .. + 0x44); each snprintf by
   segment A8b's pf_a8b_t.pfa8b_aj_snprintf_atSF with pfa8b_FR_s_regs ("%s", one string argument), the destination in
   the heap block c inside the walk's footprint (awr_byte's block disjunct). Each return point is its own lemma
   (a11h_r1, a11h_r2) stated at the ambient FP state, applied at the FP state the call returned. The cut's objects
   are carried from HIT to LOWOUT in one step (a11h_base_move: A5's a5_move0 restated over this arm's write set
   a11h_W, the scratch window below s1 and cur->model .. cur->model_file; proof shape of lib/A/Prog/pf_a5_k.v),
   and c's record is rebuilt by pf_a11a_f.v's a11f_rconf_model. Section hypotheses: SNP (snprintf, interface row
   4) and OBJ (the format literal's listing atom); no SSPX, no VRO: both callees keep every byte outside their
   destination and their window. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtFormat RtPFCmd RtPFShared.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces pf_a11a_k pf_a11a_f pf_a2_g pf_a5_d pf_a5_k pf_a6_k pf_a8b_t.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** Pure facts *)
Lemma a11h_m16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 32 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (32 * (x / 32)) with ((2 * (x / 32)) * 16) by lia. apply Z_mod_mult.
Qed.
(* the cap bytes a reader shows at d, as a byte list (a byte the reader does not show reads as 0) *)
Definition a11h_rdb (rd : reader) (d : Z) (i : nat) : byte :=
  match rd (d + Z.of_nat i) with Some z => Z_to_bv 8 z | None => ZB0 end.
Definition a11h_rdf (rd : reader) (d : Z) (cap : nat) : list byte := map (a11h_rdb rd d) (seq 0 cap).
Lemma a11h_rdf_len : forall rd d cap, length (a11h_rdf rd d cap) = cap.
Proof. intros rd d cap. unfold a11h_rdf. rewrite length_map, length_seq. reflexivity. Qed.
Lemma a11h_rdf_nth : forall rd d cap i, (i < cap)%nat -> nth i (a11h_rdf rd d cap) ZB0 = a11h_rdb rd d i.
Proof.
intros rd d cap i Hi. unfold a11h_rdf.
rewrite (nth_indep _ ZB0 (a11h_rdb rd d 0)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
(* a C string T and its NUL read back at d, the rest of a cap-byte field present: the field's bytes encode T *)
Lemma a11h_cstr : forall (rd : reader) (d : Z) (cap : nat) (T : list Z),
  (forall j, 0 <= j <= Z.of_nat (length T) -> rd (d + j) = Some (nth (Z.to_nat j) (T ++ [0]) 0)) ->
  (forall j, 0 <= j < Z.of_nat cap -> rd (d + j) <> None) ->
  (forall a z, rd a = Some z -> 0 <= z < 256) ->
  (length T < cap)%nat -> ~ In 0 T ->
  exists f, length f = cap /\ sa_bytes rd d f /\ seg_spec.cstr_enc cap T f.
Proof.
intros rd d cap T HT HP HR HL HN. exists (a11h_rdf rd d cap).
assert (HV : forall i, (i < cap)%nat -> bv_unsigned (nth i (a11h_rdf rd d cap) ZB0) = match rd (d + Z.of_nat i) with
  Some z => z | None => 0 end /\ rd (d + Z.of_nat i) <> None).
{ intros i Hi. rewrite a11h_rdf_nth by exact Hi. unfold a11h_rdb.
  destruct (rd (d + Z.of_nat i)) as [z|] eqn:E.
  - split; [apply a11f_unsigned_byte; exact (HR _ _ E) | discriminate].
  - exfalso. exact (HP (Z.of_nat i) ltac:(lia) E). }
split; [apply a11h_rdf_len|]. split.
{ intros i Hi. rewrite a11h_rdf_len in Hi. destruct (HV i Hi) as [E1 E2].
  rewrite E1. destruct (rd (d + Z.of_nat i)) as [z|]; [reflexivity | exfalso; exact (E2 eq_refl)]. }
unfold seg_spec.cstr_enc. split; [apply a11h_rdf_len|]. split; [exact HL|]. split; [exact HN|].
apply nth_ext with (d := 0) (d' := 0).
- rewrite length_firstn, length_app. unfold seg_spec.zs. rewrite length_map, a11h_rdf_len. cbn [length]. lia.
- intros i Hi. rewrite length_firstn in Hi. unfold seg_spec.zs in *. rewrite length_map, a11h_rdf_len in Hi.
  rewrite a11f_nth_firstn by lia.
  rewrite (nth_indep _ 0 (bv_unsigned ZB0)) by (rewrite length_map, a11h_rdf_len; lia).
  rewrite map_nth. destruct (HV i ltac:(lia)) as [E1 _]. rewrite E1.
  rewrite (HT (Z.of_nat i)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.
(* the reading field of c: c->reading's bytes and NUL, and every byte of the block shown *)
Lemma a11h_reading : forall (rd : reader) c cf, sa_rconf rd c cf ->
  sa_zs rd (c + seg_spec.RC_READING) (rc_reading cf ++ [0]) /\ ~ In 0 (rc_reading cf) /\
  (length (rc_reading cf) < 96)%nat /\ (forall a, c <= a < c + seg_spec.SEG_C_SIZE -> rd a <> None).
Proof.
intros rd c cf (bs & Hbs & Henc).
unfold seg_spec.rconf_enc in Henc.
destruct Henc as (Hlen & _ & _ & _ & _ & _ & _ & _ & _ & Hread & _).
destruct Hread as (L96 & HL & HN & HF).
assert (EC : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
assert (ER : seg_spec.RC_READING = 0x4080) by reflexivity.
split; [|split; [exact HN|split; [exact HL|]]].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  assert (Hb : (Z.to_nat seg_spec.RC_READING + i < length bs)%nat) by (rewrite ER; lia).
  replace (c + seg_spec.RC_READING + Z.of_nat i) with (c + Z.of_nat (Z.to_nat seg_spec.RC_READING + i))
    by (rewrite ER; lia).
  rewrite (Hbs _ Hb). f_equal.
  rewrite <- HF. unfold seg_spec.zs.
  rewrite a11f_nth_firstn by lia.
  rewrite (nth_indep _ 0 (bv_unsigned ZB0)) by (rewrite length_map; unfold seg_spec.fldz;
    rewrite a11f_fld_len; rewrite ER; lia).
  rewrite map_nth. unfold seg_spec.fldz. rewrite a11f_fld_nth by lia. reflexivity.
- intros a Ha. replace a with (c + Z.of_nat (Z.to_nat (a - c))) by lia.
  rewrite (Hbs (Z.to_nat (a - c)) ltac:(lia)). discriminate.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the interceptor owner's interface row 4 (pf_pieces.v:672-673), at the listing's snprintf trampoline *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf) gotwA guardA.
(* the listing's object atoms over the walk's abstract instance (SegObj.v): the format "%s" is object 35 *)
Hypothesis OBJ : seg_val_objs (PI := PI).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** This arm's numbers and its write set *)
Definition a11h_cur (v : pfv) (gi : nat) : Z := seg_spec.rseg_addr (p_c v) gi.
(* the bytes the arm writes: both snprintf windows below s1, and cur->model .. cur->model_file *)
Definition a11h_W (v : pfv) (gi : nat) (a : Z) : Prop :=
  (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) \/ (a11h_cur v gi + 0x24 <= a < a11h_cur v gi + 0xa0).
Definition a11h_kept (v : pfv) (gi : nat) (rd0 rd : reader) : Prop :=
  (forall a, 0 <= a < 2 ^ 64 -> ~ a11h_W v gi a -> rd a = rd0 a) /\
  (forall a, 0 <= a < 2 ^ 64 -> rd0 a <> None -> rd a <> None).
(* the block c and the entry gi of the cut *)
Definition a11h_blk (v : pfv) (gi : nat) (bc mc : Z) : Prop :=
  bc <= p_c v /\ p_c v + seg_spec.SEG_C_SIZE <= bc + req_size mc /\ 4096 <= bc /\ bc + req_size mc <= alloc_ceiling /\
  in_app bc (req_size mc) /\ off_img bc (req_size mc) /\ (gi < 32)%nat /\ 0 < p_c v /\ p_c v mod 16 = 0.
(* a byte the arm does not write *)
Definition a11h_far (v : pfv) (gi : nat) (x : Z) : Prop :=
  (0 <= x < alloc_ceiling /\ ~ (a11h_cur v gi + 0x24 <= x < a11h_cur v gi + 0xa0)) \/ (pf_s1 v <= x < 2 ^ 64).

Lemma a11h_kept_trans : forall v gi rd0 rd1 rd2, a11h_kept v gi rd0 rd1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ a11h_W v gi a -> rd2 a = rd1 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rd1 a <> None -> rd2 a <> None) -> a11h_kept v gi rd0 rd2.
Proof.
intros v gi rd0 rd1 rd2 [K1 V1] K2 V2. split.
- intros a Ha Hn. rewrite (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha H. exact (V2 a Ha (V1 a Ha H)).
Qed.
Lemma a11h_cur_in : forall v gi bc mc, a11h_blk v gi bc mc ->
  bc <= a11h_cur v gi /\ a11h_cur v gi + 0xa0 <= p_c v + 11392 /\ p_c v + 11392 <= bc + req_size mc /\
  a11h_cur v gi = p_c v + 356 * Z.of_nat gi.
Proof.
intros v gi bc mc (B1 & B2 & _ & _ & _ & _ & B7 & B8 & _).
unfold a11h_cur, seg_spec.rseg_addr, seg_spec.RSEG_SIZE. unfold seg_spec.SEG_C_SIZE in B2. lia.
Qed.
Lemma a11h_k : forall v pos gi bc mc rd0 rd x, a5_G v pos -> a11h_blk v gi bc mc -> a11h_kept v gi rd0 rd ->
  a11h_far v gi x -> rd x = rd0 x.
Proof.
intros v pos gi bc mc rd0 rd x G BLK [K _] F.
pose proof G as (G1 & G2 & G3 & G4 & _). pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof (a11h_cur_in v gi bc mc BLK) as (I1 & I2 & I3 & _).
pose proof BLK as (_ & _ & _ & B4 & _).
pose proof asan_consts as (C1 & _). apply K.
- destruct F as [[F1 _] | F1]; lia.
- unfold a11h_W, RtPFCmd.CMD_SNP_K, ESTACK. destruct F as [[F1 F2] | F1]; lia.
Qed.

Section k.
Variables (v : pfv) (pos : Z) (gi : nat) (bc mc : Z) (rd0 rd : reader).
Hypothesis G : a5_G v pos.
Hypothesis BLK : a11h_blk v gi bc mc.
Hypothesis K : a11h_kept v gi rd0 rd.
(* the bytes the arm does not write: the image, the shadow band, the stack from s1 up, the block c off the written
   fields, a heap byte off c, the class-5 frame *)
Lemma a11h_far_img : forall x, 0x10000 <= x < kImgEnd -> a11h_far v gi x.
Proof using G BLK.
intros x Hx. pose proof (a11h_cur_in v gi bc mc BLK) as (I1 & I2 & I3 & _).
pose proof BLK as (_ & _ & _ & _ & _ & B6 & _). pose proof asan_consts as (C1 & _).
unfold off_img, kImgEnd in *. left. lia.
Qed.
Lemma a11h_far_band : forall x, SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44 -> a11h_far v gi x.
Proof using G BLK.
intros x Hx. pose proof (a11h_cur_in v gi bc mc BLK) as (I1 & I2 & I3 & _).
pose proof BLK as (_ & _ & _ & B4 & B5 & _). pose proof asan_consts as (C1 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. left. lia.
Qed.
Lemma a11h_far_shadow : forall y, 0 <= y < 2 ^ 47 -> a11h_far v gi (SHADOW_OFF + y / 8).
Proof using G BLK.
intros y Hy. apply a11h_far_band.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound y 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
lia.
Qed.
Lemma a11h_far_hi : forall x, pf_s1 v <= x < 2 ^ 64 -> a11h_far v gi x.
Proof using G BLK. intros x Hx. right. exact Hx. Qed.
Lemma a11h_far_c : forall x, p_c v <= x < p_c v + seg_spec.SEG_C_SIZE ->
  ~ (a11h_cur v gi + 0x24 <= x < a11h_cur v gi + 0xa0) -> a11h_far v gi x.
Proof using G BLK.
intros x Hx Hn. pose proof BLK as (B1 & B2 & B3 & B4 & _). left. split; [lia | exact Hn].
Qed.
Lemma a11h_far_out_c : forall x, 0 <= x < alloc_ceiling -> ~ (p_c v <= x < p_c v + seg_spec.SEG_C_SIZE) ->
  a11h_far v gi x.
Proof using G BLK.
intros x Hx Hn. pose proof (a11h_cur_in v gi bc mc BLK) as (I1 & I2 & I3 & I4).
pose proof BLK as (B1 & B2 & _ & _ & _ & _ & B7 & _). unfold seg_spec.SEG_C_SIZE in *. left. split; [exact Hx | lia].
Qed.
Lemma a11h_far_frame : forall F x, (F + 2048 <= bc \/ bc + req_size mc <= F) -> F + 2048 <= alloc_ceiling ->
  F <= x < F + 2048 -> 0 <= F -> a11h_far v gi x.
Proof using G BLK.
intros F x Hd Hc Hx HF. pose proof (a11h_cur_in v gi bc mc BLK) as (I1 & I2 & I3 & I4). left. lia.
Qed.
(* the objects a reader shows at those bytes *)
Lemma a11h_k_byte : forall x, a11h_far v gi x -> rd x = rd0 x.
Proof using G BLK K. intros x Hx. exact (a11h_k v pos gi bc mc rd0 rd x G BLK K Hx). Qed.
Lemma a11h_k_zs : forall p l, (forall i, (i < length l)%nat -> a11h_far v gi (p + Z.of_nat i)) ->
  sa_zs rd0 p l -> sa_zs rd p l.
Proof using G BLK K. intros p l Ho H i Hi. rewrite (a11h_k_byte _ (Ho i Hi)). exact (H i Hi). Qed.
Lemma a11h_k_rdword : forall a, (forall k, 0 <= k < 8 -> a11h_far v gi (a + k)) -> rdword rd a = rdword rd0 a.
Proof using G BLK K. intros a Ho. apply rdword_ext. intros k Hk. exact (a11h_k_byte _ (Ho k Hk)). Qed.
Lemma a11h_k_tail : forall e, 0 <= e -> e + 8 <= 2 ^ 64 -> sa_tail rd0 e -> sa_tail rd e.
Proof using G BLK K.
intros e H0 H1 H x Hx. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
exact (proj2 K x ltac:(lia) (H x Hx)).
Qed.
Lemma a11h_k_str : forall p s, (forall x, p <= x < p + (Z.of_nat (length s) + 1) -> a11h_far v gi x) ->
  0 <= p -> p + Z.of_nat (length s) + 8 <= 2 ^ 64 -> sa_str rd0 p s -> sa_str rd p s.
Proof using G BLK K.
intros p s Ho H0 H1 [[Hz Hn] Ht].
split; [split; [|exact Hn] | exact (a11h_k_tail (p + Z.of_nat (length s)) ltac:(lia) ltac:(lia) Ht)].
apply (a11h_k_zs p (s ++ [0])); [|exact Hz]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Ho. lia.
Qed.
Lemma a11h_k_lit : forall a s, sa_lit SEGS B rd0 a s -> sa_lit SEGS B rd a s.
Proof using G BLK K.
intros a s (Ha & Hs & Hp & Hr & Hi). split; [exact Ha|]. split; [|exact (conj Hp (conj Hr Hi))].
pose proof (pa_img_range _ (proj1 (Hi (a + Z.of_nat (length s)) ltac:(lia)))) as Hrg. unfold kImgEnd in Hrg.
apply (a11h_k_str a s); [| lia | lia | exact Hs].
intros x Hx. apply a11h_far_img. exact (pa_img_range _ (proj1 (Hi x Hx))).
Qed.
Lemma a11h_k_cat : forall cat, sa_cat SEGS B rd0 cat -> sa_cat SEGS B rd cat.
Proof using G BLK K.
intros cat (Hp & Hi & Hrows). split; [exact Hp|]. split; [exact Hi|].
intros i Hn. destruct (Hrows i Hn) as (tp & Htp & Hl). exists tp. split; [|exact (a11h_k_lit tp _ Hl)].
assert (Hn' : (Z.of_nat i < 11)) by (unfold pin_spec.CAT_N in Hn; lia).
rewrite (a11h_k_rdword (pin_spec.row_addr cat i)); [exact Htp|].
intros k Hk. apply a11h_far_img. apply pa_img_range.
refine (proj1 (Hi (pin_spec.row_addr cat i + k) _)).
unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. lia.
Qed.
Lemma a11h_k_rod : arodata_okP SEGS RLO_A RHI_A B rd0 -> arodata_okP SEGS RLO_A RHI_A B rd.
Proof using G BLK K.
intros H a Hro Ho He. rewrite (a11h_k_byte a); [exact (H a Hro Ho He)|].
apply a11h_far_img.
destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
- apply pa_img_range. exists sg. split; [exact Hsg | exact Hr].
- unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI, kImgEnd in *. lia.
Qed.
Lemma a11h_k_ssp : sa_ssp rd0 gotwA guardA -> sa_ssp rd gotwA guardA.
Proof using G BLK K.
intros (G1 & g & G2).
assert (Ho : forall a, 0x10000 <= a /\ a + 8 <= kImgEnd -> forall k, 0 <= k < 8 -> a11h_far v gi (a + k))
  by (intros a Ha k Hk; apply a11h_far_img; lia).
split; [rewrite (a11h_k_rdword gotwA); [exact G1 | apply Ho; unfold gotwA, kImgEnd; lia]|].
exists g. rewrite (a11h_k_rdword guardA); [exact G2 | apply Ho; unfold guardA, kImgEnd; lia].
Qed.
End k.

(** ** The cut at HIT: its numbers *)
Section g. Context {fx : YK11.FPState}.
Lemma a11h_geo : forall v pos lyc Sc Wc rX memc mdc sc cf nm k gi,
  pf_base B v pos lyc Sc Wc rX memc mdc sc -> pf_st v pos (rdW Wc memc) cf (Some gi) nm k ->
  AR SEGS B lyc Sc Wc memc mdc /\ lyc = p_ly v /\ In (5, pos) (frames Sc) /\ a5_G v pos /\
  (gi < length (rc_seg cf))%nat /\
  exists bc mc, In (bc, mc) (ablocks B lyc Sc) /\ a11h_blk v gi bc mc /\
    (pf_F v pos + 2048 <= bc \/ bc + req_size mc <= pf_F v pos).
Proof.
intros v pos lyc Sc Wc rX memc mdc sc cf nm k gi HB HST.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc sc HB) as (HAR & Hly & Hin & G & _).
destruct HB as (HCX & _ & HOBJ & _).
destruct HOBJ as (_ & _ & _ & _ & HC & _).
destruct HST as ((bs & _ & Henc) & HCUR & _).
destruct Henc as (_ & Hn32 & _).
change (gi < length (rc_seg cf))%nat in HCUR.
destruct (a6_cx B v HCX) as (Hc0 & Hc16 & _).
destruct HC as (bc & mc & Hbc & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & H4096 & Hceil & Happ & _ & _ & Hm).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hreq].
pose proof (blk_off_imgP B lyc Sc Wc memc mdc bc mc HAR Hbc) as Hoff.
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc bc mc 5 pos HAR Hbc Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hly in Hd. change (fs_frame_bytes 5) with 2048 in Hd.
change (frame_addr (p_ly v) 5 pos) with (pf_F v pos) in Hd.
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hin|]. split; [exact G|]. split; [exact HCUR|].
exists bc, mc. split; [exact Hbc|]. split; [|lia].
unfold a11h_blk. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Happ|].
split; [exact Hoff|]. split; [lia|]. split; [lia | exact Hc16].
Qed.
End g.

(** ** The snprintf step at either site: a destination inside cur->model .. cur->model_file, the format "%s" at
    seg_litA_rc F_s, one string argument w in a3 (pf_a8b_t.v's pfa8b_aj_snprintf_atSF and pfa8b_FR_s_regs) *)
Section s. Context {fx : YK11.FPState}.
Lemma a11h_snp : forall v pos lyc Sc (Wc : world SEGS) (regsT : bvmap 5 word) memT mdT gi bc mc off n
    (w : Z) (T : list Z) raw,
  a5_G v pos -> a11h_blk v gi bc mc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memT mdT 0 ->
  In (bc, mc) (ablocks B lyc Sc) ->
  getr regsT 10 = w64 (a11h_cur v gi + off) -> getr regsT 11 = w64 n ->
  getr regsT 12 = w64 (seg_litA_rc F_s) -> getr regsT (Z_to_bv 5 13) = w64 w ->
  spZ regsT = pf_s1 v -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  0x24 <= off -> off + n <= 0xa0 -> 1 <= n ->
  sa_lit SEGS B (rdW Wc memT) (seg_litA_rc F_s) F_s -> sa_ssp (rdW Wc memT) gotwA guardA ->
  arodata_okP SEGS RLO_A RHI_A B (rdW Wc memT) -> frm0 fx ->
  0 < w < 2 ^ 47 -> sa_str (rdW Wc memT) w T -> sa_addr (rdW Wc memT) w (Z.of_nat (length T) + 1) ->
  amem_range w (Z.of_nat (length T) + 8) -> Z.of_nat (length T) < n ->
  w + seg_spec.cstr_span w T <= pf_s1 v - RtPFCmd.CMD_SNP_K ->
  (w + seg_spec.cstr_span w T <= a11h_cur v gi + off \/ a11h_cur v gi + off + n <= w) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = Wc /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
      c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
      ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
        (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem2 md2 0 /\
      aregs_preserved regsT regs2 /\
      (forall j, 0 <= j <= Z.of_nat (length T) ->
         rdW Wc mem2 (a11h_cur v gi + off + j) = Some (nth (Z.to_nat j) (T ++ [0]) 0)) /\
      (forall a, 0 <= a < 2 ^ 64 ->
         ~ (a11h_cur v gi + off <= a < a11h_cur v gi + off + (Z.of_nat (length T) + 1)) ->
         ~ (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc memT a) /\
      (forall a, apresent (w_H Wc) memT a -> apresent (w_H Wc) mem2 a)).
Proof.
intros v pos lyc Sc Wc regsT memT mdT gi bc mc off n w T raw G BLK HJ Hbc R10 R11 R12 R13 Rsp R3 R4 R1 Hraw
  Hoff Hoffn Hn LIT SSP ROD FRM Hw STR ADDR AMEM HTn HDW HDD.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof BLK as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof (a11h_cur_in v gi bc mc BLK) as (CI1 & CI2 & CI3 & CI4).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
pose proof (proj1 HJ) as HAR.
assert (EF : seg_litA_rc F_s = 136000) by (vm_compute; reflexivity).
assert (Hs16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by (apply pa2_m16; [apply a11h_m16; exact G5 | exact G3]).
assert (ESN : RtPFShared.sn_bytes (n - 1) T = T ++ [0]).
{ unfold RtPFShared.sn_bytes. rewrite firstn_all2 by lia. reflexivity. }
assert (ELN : RtPFShared.sn_len (n - 1) T = Z.of_nat (length T) + 1).
{ unfold RtPFShared.sn_len. rewrite ESN, length_app. cbn [length]. lia. }
pose proof LIT as (Lf0 & LSTR & LPIN & _ & _).
assert (LADDR : sa_addr (rdW Wc memT) (seg_litA_rc F_s) 3).
{ pose proof (LPIN _ _ _ _ _ HAR) as HA. rewrite pfa8b_F_s_len in HA. exact HA. }
eapply SRr_mono.
{ apply (pfa8b_aj_snprintf_atSF SEGS B LAWS pa_segs_low gotwA guardA (SIGMA SS___interceptor_trampoline_snprintf)
    (SNP fx) Wc regsT memT STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdT 0 (a11h_cur v gi + off) n (seg_litA_rc F_s) T
    (pf_s1 v - pf_sp0 v) raw HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - rewrite Rsp. lia.
  - exact Hs16.
  - lia.
  - unfold RtPFCmd.CMD_SNP_K, ESTACK. rewrite SPF. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hraw.
  - intros a Ha. split.
    + right; left. split.
      * exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [left; reflexivity|]. cbn [fst snd].
        unfold seg_spec.RC_N. lia.
      * exists bc, mc. split; [exact Hbc | lia].
    + unfold RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - intros a Ha _ [[_ Himg] | Hsp]; [|exfalso; lia].
    exfalso. exact (blk_img SEGS B LAWS lyc Sc Wc memT mdT bc mc a HAR Hbc ltac:(lia) Himg).
  - exact (amem8_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (a11h_cur v gi + off) n HAR Hbc ltac:(lia) ltac:(lia)
      ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (a11h_cur v gi + off) n HAR Hbc
      ltac:(lia) ltac:(lia)).
  - exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memT mdT bc mc (a11h_cur v gi + off) n HAR Hbc
      ltac:(lia) ltac:(lia) ltac:(lia)).
  - rewrite ELN. apply (pfa8b_off_img_sub bc (req_size mc)); [exact B6 | lia | lia | lia].
  - unfold RtPFCmd.CMD_IMG_HI, kImgEnd, RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - exact SSP.
  - unfold gotwA. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_HI, kImgEnd. lia.
  - unfold guardA. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_HI, kImgEnd. lia.
  - unfold gotwA, RtPFCmd.CMD_IMG_LO. lia.
  - unfold guardA, RtPFCmd.CMD_IMG_LO. lia.
  - rewrite ELN, Rsp. apply (pfa8b_FR_s_regs _ _ (seg_litA_rc F_s) w T regsT).
    + unfold argZ. change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13). rewrite R13. unfold w64.
      apply unsigned_lit_small. lia.
    + rewrite EF. lia.
    + rewrite EF. unfold RtPFCmd.CMD_IMG_LO. lia.
    + rewrite EF. unfold RtPFCmd.CMD_GOTW. lia.
    + exact LSTR.
    + exact LADDR.
    + unfold RtPFShared.snp_out. rewrite EF.
      unfold off_img in B6. unfold RtPFCmd.CMD_SNP_K, ESTACK.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    + lia.
    + exact (pfa8b_bytes_range_aview SEGS (w_H Wc) memT w T STR).
    + lia.
    + exact STR.
    + exact ADDR.
    + exact AMEM.
    + unfold RtPFShared.snp_out.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
  - lia.
  - intros a Hrom Ho He. exact (ROD a (or_introl Hrom) Ho He).
  - exact FRM. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hf & -> & HJ2 & HP2 & _ & HBY & HK & HPR & _).
split; [reflexivity|]. exists fx1, regs2, mem2, md2.
split; [exact Hf|]. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
split.
{ intros j Hj. rewrite ELN in HBY. rewrite <- ESN. apply HBY. lia. }
split.
{ intros a Ha Hd Hwin. apply HK; [exact Ha | rewrite ELN; exact Hd | intros Hc; apply Hwin; lia]. }
exact HPR.
Qed.
End s.

(** ** Tools *)
(* a register of a symbolic state at its value (the A10b proof's pf_a10b_j.v pj_rreg, there from the A2 proof's
   pf_a2.v), also for the st_ok a run to a call leaves *)
Ltac a11h_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg SEGS Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* a run whose regions are read-only writes nothing (trim_s.v's ta_awr) *)
Ltac a11h_awr_ro := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(** ** The cut's objects from HIT at the reader of a later point: pf_base at the FP state reached (piece A5's
    a5_move0, pf_a5_k.v, restated over this arm's write set a11h_W; its proof shape) *)
Section m. Context {fx : YK11.FPState}.
Lemma a11h_base_move : forall (f0 : YK11.FPState) v pos lyc Sc (Wc : world SEGS) rX0 memc0 mdc0 rX mem md gi bc mc,
  pf_base (fx := f0) B v pos lyc Sc Wc rX0 memc0 mdc0 PF_SC_L146 ->
  fxrel f0 fx -> a11h_blk v gi bc mc -> (pf_F v pos + 2048 <= bc \/ bc + req_size mc <= pf_F v pos) ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem md 0 ->
  a11h_kept v gi (rdW Wc memc0) (rdW Wc mem) ->
  pf_rg rX (a5_FI B v) ->
  pf_base (fx := fx) B v pos lyc Sc Wc rX mem md PF_SC_L146.
Proof.
intros f0 v pos lyc Sc Wc rX0 memc0 mdc0 rX mem md gi bc mc HB Hfx BLK HFD HJ K HRG.
pose proof (a5_geo (fx := f0) B v pos lyc Sc Wc rX0 memc0 mdc0 PF_SC_L146 HB) as (HAR & Hly & Hin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct HFI as (_ & _ & HSc & HP0 & HSV & HFL & HFRM & _).
destruct HOBJ as (T1 & T2 & T3 & C1 & C2 & CA & LI & RO & SS).
pose proof (proj1 HJ) as HAR'.
destruct (a6_cx B v HCX) as (Hc0 & Hc16 & HLS & HDJ & _).
pose proof T3 as (bt & mt & Hbt & Ht1 & Ht2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc0 mdc0 bt mt HAR Hbt) as (_ & Hbt4 & Hbtc & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
pose proof (Z.mod_pos_bound (- (p_t v + Z.of_nat (length (p_s v)) + 1)) 8 ltac:(lia)) as Hsp8.
unfold sa_disj, seg_spec.cstr_span, pf_len in *.
change (fs_frame_bytes 5) with 2048 in *.
split; [exact HCX|].
split.
{ split; [exact HJ|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HP0|].
  split.
  { intros j r Hj. rewrite <- (HSV j r Hj). apply rdword_ext. intros k Hk.
    pose proof (proj1 (nth_error_Some PF_SAVED j) ltac:(rewrite Hj; discriminate)) as Hj13.
    unfold PF_SAVED in Hj13. cbn [length] in Hj13.
    apply (a11h_k_byte v pos gi bc mc _ _ G BLK K). apply (a11h_far_hi v pos gi bc mc G BLK). lia. }
  split.
  { rewrite <- HFL. apply rdword_ext. intros k Hk.
    apply (a11h_k_byte v pos gi bc mc _ _ G BLK K). apply (a11h_far_frame v pos gi bc mc G BLK (pf_F v pos)); lia. }
  split; [exact (fxrel_frm0 f0 fx HFRM Hfx)|].
  exact HRG. }
split.
{ split.
  { apply (a11h_k_str v pos gi bc mc _ _ G BLK K); [| lia | lia | exact T1].
    intros x Hx. apply (a11h_far_out_c v pos gi bc mc G BLK); lia. }
  split; [exact (a6_heap_addr B lyc Sc Wc mem md _ _ HAR' T3 ltac:(lia))|].
  split; [exact T3|].
  split; [exact (a6_heap_addr B lyc Sc Wc mem md _ _ HAR' C2 ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
  split; [exact C2|].
  split; [exact (a11h_k_cat v pos gi bc mc _ _ G BLK K _ CA)|].
  split; [intros x Hx; exact (a11h_k_lit v pos gi bc mc _ _ G BLK K _ _ (LI x Hx))|].
  split; [exact (a11h_k_rod v pos gi bc mc _ _ G BLK K RO)|].
  exact (a11h_k_ssp v pos gi bc mc _ _ G BLK K SS). }
split.
{ unfold pf_sl in *. rewrite Forall_forall in *. intros ov Hov.
  assert (Ho : 0x20 <= fst ov <= 0xb8).
  { unfold PF_SL in Hov. cbn [In] in Hov.
    repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
  rewrite <- (HSL ov Hov). apply rdword_ext. intros k Hk.
  apply (a11h_k_byte v pos gi bc mc _ _ G BLK K). apply (a11h_far_hi v pos gi bc mc G BLK). lia. }
intros i Hi. rewrite (a11h_k_byte v pos gi bc mc _ _ G BLK K); [exact (HFSH i Hi)|].
apply (a11h_far_band v pos gi bc mc G BLK). unfold kLowMemEnd, kHighShadowEnd, SHADOW_OFF in *. lia.
Qed.

(** ** The seed at RET_SN2 (0x88594): every register its own atom, slot 0x90 (c, extra atom 32) read-only on s1 *)
Definition a11h_ss2 : sstate := mkSS A11_RET_SN2 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x90 0x98 0 0 [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma a11h_seed2 : forall v pos (Wc : world SEGS) (regs : bvmap 5 word) mem,
  a5_G v pos -> getr regs (Z_to_bv 5 9) = w64 (pf_s1 v) ->
  rdword (rdW Wc mem) (pf_s1 v + 0x90) = Some (p_c v) -> 0 <= p_c v < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 (p_c v)])) a11h_ss2
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 (BASE + A11_RET_SN2)) mem (seg_rom SEGS))).
Proof.
intros v pos Wc regs mem G R9 W90 Hc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
set (E := Eimg (Ereg regs [w64 (p_c v)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (p_c v))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold a11h_ss2. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x90 8 (SOff 32 0) (p_c v)).
  + cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + cbn. lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) mem _ _ W90).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9. change (2 ^ 5) with 32. repeat split; lia.
Qed.
End m.

(** ** RET_SN2 (0x88594) -> LOWOUT: s8 = slot 0x90 = c, a0 = -8, the jump; c holds the updated record *)
Section r2. Context {fx : YK11.FPState}.
Lemma a11h_r2 : forall n, HA_LOWOUT B n -> forall (f0 : YK11.FPState) v pos lyc Sc (Wc : world SEGS) rX0 memc0 mdc0
    cf nm o ln d gi val i (regs : bvmap 5 word) mem md,
  pf_base (fx := f0) B v pos lyc Sc Wc rX0 memc0 mdc0 PF_SC_L146 -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc0) cf (Some gi) nm (length (skipn o (p_s v))) ->
  ~ In 0 val -> by_token (r_low val 0 24) = Some i -> fxrel f0 fx ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem md 0 ->
  a11h_kept v gi (rdW Wc memc0) (rdW Wc mem) ->
  (forall j, 0 <= j <= Z.of_nat (length (r_low val 0 24)) ->
     rdW Wc mem (a11h_cur v gi + 0x24 + j) = Some (nth (Z.to_nat j) (r_low val 0 24 ++ [0]) 0)) ->
  (forall k, 0 <= k < 4 -> rdW Wc mem (a11h_cur v gi + 0x3c + k) = Some (if k =? 0 then 1 else 0)) ->
  (forall j, 0 <= j <= Z.of_nat (length (rc_reading cf)) ->
     rdW Wc mem (a11h_cur v gi + 0x40 + j) = Some (nth (Z.to_nat j) (rc_reading cf ++ [0]) 0)) ->
  pf_rg regs (a5_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++ [(20, a11h_cur v gi)]) ->
  SRr SEGS Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + A11_RET_SN2)) mem (seg_rom SEGS)) md)
    (a11_post (fx := fx) B v cf gi nm val o ln).
Proof.
intros n HL f0 v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi val i regs mem md HB HMID HST HNZ HBT Hfx HJ K
  B1 B2 B3 HRG.
destruct (a11h_geo (fx := f0) v pos lyc Sc Wc rX0 memc0 mdc0 PF_SC_L146 cf nm _ gi HB HST)
  as (HAR0 & Hly & Hin & G & Hgi & bc & mc & Hbc & BLK & HFD).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof BLK as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7 & BL8 & BL9).
pose proof (a11h_cur_in v gi bc mc BLK) as (CI1 & CI2 & CI3 & CI4).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
pose proof HB as (_ & _ & _ & HSL & _).
assert (R9 : getr regs (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get regs _ 9 _ HRG); unfold a5_FI; pa2_in).
pose proof (proj1 (Forall_forall _ _) HSL (0x90, p_c v) ltac:(unfold PF_SL; pa2_in)) as W90. cbn [fst snd] in W90.
assert (W90' : rdword (rdW Wc mem) (pf_s1 v + 0x90) = Some (p_c v)).
{ rewrite <- W90. apply (a11h_k_rdword v pos gi bc mc _ _ G BLK K). intros k Hk.
  apply (a11h_far_hi v pos gi bc mc G BLK). lia. }
pose proof (a11h_seed2 (fx := fx) v pos Wc regs mem G R9 W90' ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 (p_c v)]))) by apply Eimg_env.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r ->
  ew (Eimg (Ereg regs [w64 (p_c v)])) n0 = getr regs r) by (intros n0 r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs [w64 (p_c v)])) 32 = w64 (p_c v))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
revert HS HEI EE E32. generalize (Eimg (Ereg regs [w64 (p_c v)])) as E. intros E HS HEI EE E32.
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
(* 0x88594 .. 0x8859c: s8 = c, a0 = -8, the jump to LOWOUT *)
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ PF_LOWOUT.
{ a11h_awr_ro. }
cbn [ms_mem mkst] in HFr, HG, HF.
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc mem a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) mem (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV : forall a, rdW Wc mem a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) mem (ms_mem ms) a HG Hv)).
pose proof (a11h_kept_trans v gi _ _ _ K (fun a Ha _ => KM a Ha) (fun a Ha Hv => KV a Hv)) as K2.
assert (Q24 : getr (ms_regs ms) (Z_to_bv 5 24) = w64 (p_c v)).
{ a11h_rreg HS. cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity. }
assert (Q10 : getr (ms_regs ms) (Z_to_bv 5 10) = w64 (-8)).
{ a11h_rreg HS. cbn [sv_denot]. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 22; 18; 19; 20; 21; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [a11h_rreg HS; rewrite pa2_crt_den_atom0; apply EE; reflexivity |]). destruct Hr. }
pmkst HS.
unfold a11_post, a11_step. rewrite HBT.
lazymatch goal with |- SRr _ _ (mkCfg (@mkst _ ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (@mkst fx rg (Z_to_bv 64 (BASE + k)) mm rom) mdx)
    with (cfg_at (fx := fx) SEGS (BASE + PF_LOWOUT) rg mm mdx) end.
apply (HL fx v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv
  (r_upd cf gi (rs_with_model (snprintf_s 24 F_s [AS (r_low val 0 24)]) (snprintf_s 96 F_s [AS (rc_reading cf)])))
  nm o ln d gi).
pose proof HMID as (Ho & _).
destruct HST as (HRC & HCUR & HNM & HCNT).
split; [|split; [exact HMID|split]].
- (* the cut's objects *)
  apply (a11h_base_move (fx := fx) f0 v pos lyc Sc Wc rX0 memc0 mdc0 (ms_regs ms) (ms_mem ms) mdv gi bc mc HB Hfx BLK HFD
    HJ K2).
  unfold pf_rg, a5_FI. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    (rewrite QK; [apply (a5_rg_get regs _ _ _ HRG); unfold a5_FI; pa2_in | pa2_in]).
- (* c holds the updated record; cur, cur_name, the counters *)
  split; [|split; [exact (a11f_cur_ok_upd cf gi _ gi HCUR)|split]].
  + apply (a11f_rconf_model (rdW Wc memc0) _ (p_c v) cf gi);
      [exact HRC | exact Hgi | lia | unfold seg_spec.SEG_C_SIZE; lia |].
    destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdv bc mc (proj1 HJ) Hbc) as (_ & _ & _ & _ & HPRES & _).
    assert (PR : forall a, bc <= a < bc + req_size mc -> rdW Wc (ms_mem ms) a <> None)
      by (intros a Ha; apply (aview_some_of_apresent SEGS); exact (proj1 (HPRES a Ha))).
    pose proof (sa_aview_rng SEGS (w_H Wc) (ms_mem ms)) as RNG.
    pose proof (a11f_low_len val 24 HNZ) as LL. pose proof (a11f_low_nulfree val 24 HNZ) as LN.
    destruct (a11h_reading (rdW Wc memc0) (p_c v) cf HRC) as (_ & RN & RL & _).
    unfold a11f_wrote. split; [|split; [|split]].
    * intros a Ha H1 H2 H3. apply (a11h_k_byte v pos gi bc mc _ _ G BLK K2).
      apply (a11h_far_c v pos gi bc mc G BLK); [exact Ha|].
      unfold a11h_cur, seg_spec.RS_MODEL, seg_spec.RS_MODEL_SET, seg_spec.RS_MODEL_FILE in *. lia.
    * destruct (a11h_cstr (rdW Wc (ms_mem ms)) (a11h_cur v gi + 0x24) 24 (r_low val 0 24))
        as (f24 & L24 & S24 & C24).
      { intros j Hj. rewrite KM by lia. exact (B1 j Hj). }
      { intros j Hj. apply PR. lia. }
      { exact RNG. }
      { rewrite LL. lia. }
      { exact LN. }
      exists f24. rewrite (a11f_snprintf_low val HNZ). split; [exact L24|]. split; [exact S24 | exact C24].
    * eexists. split; [|reflexivity].
      lazymatch goal with |- sa_bytes _ _ ?f4 => assert (L4 : length f4 = 4%nat) by (vm_compute; reflexivity) end.
      intros k Hk. rewrite L4 in Hk.
      change (seg_spec.rseg_addr (p_c v) gi + seg_spec.RS_MODEL_SET) with (a11h_cur v gi + 0x3c).
      rewrite KM by lia. rewrite (B2 (Z.of_nat k)) by lia.
      destruct k as [|[|[|[|k]]]]; [vm_compute; reflexivity .. | lia].
    * destruct (a11h_cstr (rdW Wc (ms_mem ms)) (a11h_cur v gi + 0x40) 96 (rc_reading cf))
        as (f96 & L96 & S96 & C96).
      { intros j Hj. rewrite KM by lia. exact (B3 j Hj). }
      { intros j Hj. apply PR. lia. }
      { exact RNG. }
      { exact RL. }
      { exact RN. }
      exists f96. rewrite (snprintf_s1 96 (rc_reading cf) RN ltac:(lia)). split; [exact L96|].
      split; [exact S96 | exact C96].
  + destruct HNM as (fnm & Hfb & Henc). exists fnm. split; [|exact Henc].
    intros i0 Hi0. destruct Henc as [Hl _].
    rewrite (a11h_k_byte v pos gi bc mc _ _ G BLK K2); [exact (Hfb i0 Hi0)|].
    apply (a11h_far_frame v pos gi bc mc G BLK (pf_F v pos)); [exact HFD | lia | unfold PF_O_CN; lia | lia].
  + apply (pf_cnt_mono _ (length (skipn o (p_s v)))); [pose proof (pf_next_skipn_lt (p_s v) o Ho); lia|].
    apply a11f_cnt_upd. exact HCNT.
- (* the registers *)
  unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
    first [exact Q24 | exact Q10
          | rewrite QK; [apply (a5_rg_get regs _ _ _ HRG); unfold a5_FI, PF_RL, PF_RM; pa2_in | pa2_in]].
Qed.
End r2.

(** ** The format literal "%s": listing object 35 (SegList.v's two PAddHi at the two sites), seg_litA_rc F_s = 0x21340
    (reac_segconf_parse.v's lbl_atom, at object 35) *)
Lemma a11h_fmt_atom : forall E, img_env VAL A_LIM E -> ew E 276%nat = w64 (seg_litA_rc F_s).
Proof.
intros E HE. rewrite (img_env_atomP E 276%nat HE) by (unfold A_TEXT, A_LIM; lia).
change 276%nat with (A_OBJ 35). rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.
Lemma a11h_heap_sub : forall ly S q n q' n', sa_heap B ly S q n -> q <= q' -> q' + n' <= q + n -> sa_heap B ly S q' n'.
Proof. intros ly S q n q' n' (b & m & Hb & H1 & H2) H3 H4. exists b, m. split; [exact Hb | lia]. Qed.
Lemma a11h_lit_F_s : In F_s PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. left. reflexivity. Qed.

(** ** The seeds at HIT (0x88540: slot 0xb0 = cur, extra atom 32) and at RET_SN1 (0x88560: slot 0x58 = c + RC_READING,
    extra atom 32, read-only on s1; cur->model_set = cur + 0x3c .. + 0x40 writable on s4's atom; the shadow entry over
    cur + 0x3c .. + 0x44 decides check #27) *)
Definition a11h_ss0 : sstate := mkSS A11_HIT sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xb0 0xb8 0 0 [YP09.mkChunk 0xb0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Definition a11h_ss1 : sstate := mkSS A11_RET_SN1 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0x58 0x60 0 0 [YP09.mkChunk 0x58 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 20%nat) 0x3c 0x40 0x3c 0x40 []] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, PTR 2); (22%nat, mkAF SB SB 0)] [] []).
Definition a11h_Bx : sv := SOff 22 0.
Definition a11h_SH1 : list shent := [mkSHE 20 0x3c 0x44].

Section q. Context {fx : YK11.FPState}.
Lemma a11h_seed0 : forall v pos gi (Wc : world SEGS) (regs : bvmap 5 word) mem,
  a5_G v pos -> getr regs (Z_to_bv 5 9) = w64 (pf_s1 v) ->
  rdword (rdW Wc mem) (pf_s1 v + 0xb0) = Some (a11h_cur v gi) -> 0 <= a11h_cur v gi < 2 ^ 64 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 (a11h_cur v gi)])) a11h_ss0
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 (BASE + A11_HIT)) mem (seg_rom SEGS))).
Proof.
intros v pos gi Wc regs mem G R9 Wb0 Hc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
set (E := Eimg (Ereg regs [w64 (a11h_cur v gi)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (a11h_cur v gi))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold a11h_ss0. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (pf_s1 v) 0xb0 8 (SOff 32 0) (a11h_cur v gi)).
  + cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + cbn. lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) mem _ _ Wb0).
- cbn. tauto.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9. change (2 ^ 5) with 32. repeat split; lia.
Qed.
Lemma a11h_seed1 : forall v pos gi bc mc (Wc : world SEGS) (regs : bvmap 5 word) mem,
  a5_G v pos -> a11h_blk v gi bc mc ->
  getr regs (Z_to_bv 5 9) = w64 (pf_s1 v) -> getr regs (Z_to_bv 5 20) = w64 (a11h_cur v gi) ->
  getr regs (Z_to_bv 5 22) = w64 SHADOW_OFF ->
  rdword (rdW Wc mem) (pf_s1 v + 0x58) = Some (p_c v + seg_spec.RC_READING) ->
  (forall a, a11h_cur v gi + 0x3c <= a < a11h_cur v gi + 0x40 -> apresent (w_H Wc) mem a) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 (p_c v + seg_spec.RC_READING)])) a11h_ss1
    (restrict (w_H Wc) (mkst regs (Z_to_bv 64 (BASE + A11_RET_SN1)) mem (seg_rom SEGS))).
Proof.
intros v pos gi bc mc Wc regs mem G BLK R9 R20 R22 W58 HP.
pose proof G as (G1 & G2 & G3 & G4 & G5 & _).
pose proof BLK as (BL1 & BL2 & BL3 & BL4 & _ & _ & BL7 & BL8 & BL9).
pose proof (a11h_cur_in v gi bc mc BLK) as (CI1 & CI2 & CI3 & CI4).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
assert (ER : seg_spec.RC_READING = 0x4080) by reflexivity.
unfold seg_spec.SEG_C_SIZE in BL2.
set (E := Eimg (Ereg regs [w64 (p_c v + seg_spec.RC_READING)])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = a11h_cur v gi)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), R22; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (E32 : ew E 32 = w64 (p_c v + seg_spec.RC_READING))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold a11h_ss1. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x58 8 (SOff 32 0) (p_c v + seg_spec.RC_READING)).
    * cbn [sv_denot]. rewrite E32. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * exact (val_mem_of_rdword SEGS (w_H Wc) mem _ _ W58).
  + rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply HP. lia.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val]. rewrite U9, U20. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
  rewrite U9, U20, U22, SB_SHADOW_OFF. change (2 ^ 5) with 32. change (2 ^ 2) with 4.
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. unfold SHADOW_OFF. repeat split; lia.
Qed.
End q.

(** ** RET_SN1 (0x88560) -> the second snprintf -> RET_SN2: check #27, cur->model_set = 1, the call *)
Section r1. Context {fx : YK11.FPState}.
Lemma a11h_r1 : forall n, HA_LOWOUT B n -> forall (f0 : YK11.FPState) v pos lyc Sc (Wc : world SEGS) rX0 memc0 mdc0
    cf nm o ln d gi val i (regs : bvmap 5 word) mem md,
  pf_base (fx := f0) B v pos lyc Sc Wc rX0 memc0 mdc0 PF_SC_L146 -> pf_mid v o ln d n ->
  pf_st v pos (rdW Wc memc0) cf (Some gi) nm (length (skipn o (p_s v))) ->
  ~ In 0 val -> by_token (r_low val 0 24) = Some i -> fxrel f0 fx ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc mem md 0 ->
  a11h_kept v gi (rdW Wc memc0) (rdW Wc mem) ->
  (forall j, 0 <= j <= Z.of_nat (length (r_low val 0 24)) ->
     rdW Wc mem (a11h_cur v gi + 0x24 + j) = Some (nth (Z.to_nat j) (r_low val 0 24 ++ [0]) 0)) ->
  pf_rg regs (a5_FI B v ++ PF_RL v pos ++ PF_RM v o ln ++ [(20, a11h_cur v gi)]) ->
  SRr SEGS Wc (mkCfg (@mkst fx regs (Z_to_bv 64 (BASE + A11_RET_SN1)) mem (seg_rom SEGS)) md)
    (a11_post (fx := fx) B v cf gi nm val o ln).
Proof.
intros n HL f0 v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi val i regs mem md HB HMID HST HNZ HBT Hfx HJ K
  B1 HRG.
destruct (a11h_geo (fx := f0) v pos lyc Sc Wc rX0 memc0 mdc0 PF_SC_L146 cf nm _ gi HB HST)
  as (HAR0 & Hly & Hin & G & Hgi & bc & mc & Hbc & BLK & HFD).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof BLK as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7 & BL8 & BL9).
pose proof (a11h_cur_in v gi bc mc BLK) as (CI1 & CI2 & CI3 & CI4).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
assert (ER : seg_spec.RC_READING = 0x4080) by reflexivity.
assert (EC : seg_spec.SEG_C_SIZE = 16616) by reflexivity.
pose proof (a11f_low_len val 24 HNZ) as LL.
pose proof HB as (_ & (_ & _ & _ & _ & _ & _ & HFRM & _) & HOBJ & HSL & _).
pose proof HOBJ as (_ & _ & _ & _ & C2 & _ & LI & RO & SS).
pose proof HST as (HRC & _).
pose proof (proj1 HJ) as HAR.
assert (R9 : getr regs (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get regs _ 9 _ HRG); unfold a5_FI; pa2_in).
assert (R20 : getr regs (Z_to_bv 5 20) = w64 (a11h_cur v gi))
  by (apply (a5_rg_get regs _ 20 _ HRG); unfold a5_FI, PF_RL, PF_RM; pa2_in).
assert (R22 : getr regs (Z_to_bv 5 22) = w64 SHADOW_OFF) by (apply (a5_rg_get regs _ 22 _ HRG); unfold a5_FI; pa2_in).
pose proof (proj1 (Forall_forall _ _) HSL (0x58, p_c v + seg_spec.RC_READING) ltac:(unfold PF_SL; pa2_in)) as W58.
cbn [fst snd] in W58.
assert (W58' : rdword (rdW Wc mem) (pf_s1 v + 0x58) = Some (p_c v + seg_spec.RC_READING)).
{ rewrite <- W58. apply (a11h_k_rdword v pos gi bc mc _ _ G BLK K). intros k Hk.
  apply (a11h_far_hi v pos gi bc mc G BLK). lia. }
destruct (al_blocks _ _ LAWS lyc Sc Wc mem md bc mc HAR Hbc) as (_ & _ & _ & _ & HPRES & _).
pose proof (a11h_seed1 (fx := fx) v pos gi bc mc Wc regs mem G BLK R9 R20 R22 W58'
  (fun a Ha => proj1 (HPRES a ltac:(lia)))) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs [w64 (p_c v + seg_spec.RC_READING)]))) by apply Eimg_env.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r ->
  ew (Eimg (Ereg regs [w64 (p_c v + seg_spec.RC_READING)])) n0 = getr regs r)
  by (intros n0 r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg regs [w64 (p_c v + seg_spec.RC_READING)])) 32 = w64 (p_c v + seg_spec.RC_READING))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
revert HS HEI EE E32. generalize (Eimg (Ereg regs [w64 (p_c v + seg_spec.RC_READING)])) as E.
intros E HS HEI EE E32.
assert (E20 : ew E 20 = Z_to_bv 64 (a11h_cur v gi)) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (U20 : bv_unsigned (ew E 20) = a11h_cur v gi) by (rewrite E20; apply unsigned_lit_small; lia).
assert (UB : U E a11h_Bx = SHADOW_OFF).
{ unfold a11h_Bx. apply U_atom; [rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); exact R22 | unfold SHADOW_OFF; lia]. }
assert (UC : U E (SOff 20 0) = a11h_cur v gi) by (apply U_atom; [exact E20 | lia]).
assert (SHOK : sh_ok SEGS a11h_Bx a11h_SH1 E (mrestrict (w_H Wc) mem)).
{ unfold sh_ok, a11h_SH1. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) mem E a11h_Bx 20%nat (a11h_cur v gi + 0x3c) 8 (a11h_cur v gi) 0x3c 0x44
    (range_addressable_of_block SEGS B LAWS lyc Sc Wc mem md bc mc (a11h_cur v gi + 0x3c) 8 HAR Hbc
       ltac:(lia) ltac:(lia)) UB UC); [lia | lia |].
  intros x Hx. change (Z.min 0x3c 0x44) with 0x3c in Hx. change (Z.max 0x3c 0x44) with 0x44 in Hx.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
(* 0x88560 .. 0x88590: check #27 (decided by the shadow entry), model_set = 1, the call's arguments, the jal *)
paj_run_tok (paj_run (fx := fx) B LAWS) HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 20%nat) (b := a11h_cur v gi); [reflexivity | exact U20 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - exists (p_c v, p_c v + seg_spec.RC_N + 4). split; [left; reflexivity|]. cbn [fst snd].
    unfold seg_spec.RC_N. lia.
  - exists bc, mc. split; [exact Hbc | lia]. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM1 : forall a, 0 <= a < 2 ^ 64 -> ~ (a11h_cur v gi + 0x3c <= a < a11h_cur v gi + 0x40) ->
    rdW Wc (ms_mem ms) a = rdW Wc mem a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) mem (ms_mem ms)
    (fun a => a11h_cur v gi + 0x3c <= a < a11h_cur v gi + 0x40) HFr); [|exact Ha | exact Hn].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U20 in Hrr; lia |]).
  destruct Hin'. }
assert (KV1 : forall a, rdW Wc mem a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) mem (ms_mem ms) a HG Hv)).
pose proof (a11h_kept_trans v gi _ _ _ K
  (fun a Ha Hw => KM1 a Ha ltac:(intros Hc; apply Hw; right; lia)) (fun a Ha Hv => KV1 a Hv)) as K1.
(* the four bytes the sw wrote *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
cbn [ms_mem restrict] in HR1.
pose proof (field_of_region_any E (mrestrict (w_H Wc) (ms_mem ms)) 20 (a11h_cur v gi) _ 60 64 60 64 60 4%N (SLit 1)
  HR1 U20 ltac:(left; reflexivity) ltac:(cbn; lia)) as VM.
assert (B2 : forall k, 0 <= k < 4 -> rdW Wc (ms_mem ms) (a11h_cur v gi + 0x3c + k) = Some (if k =? 0 then 1 else 0)).
{ intros k Hk. pose proof (VM (Z.to_nat k) ltac:(cbn; lia)) as Vk.
  replace (a11h_cur v gi + 0x3c + k) with (a11h_cur v gi + 60 + Z.of_nat (Z.to_nat k)) by lia.
  unfold aview. rewrite Vk. cbn [option_map]. f_equal. cbn [sv_denot].
  assert (Hk4 : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct Hk4 as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity. }
(* the registers at the jal *)
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A11_RET_SN2)).
{ a11h_rreg HS. cbn [sv_denot]. rewrite (img_env_codeptr E HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms) 10 = w64 (a11h_cur v gi + 0x40)).
{ a11h_rreg HS. cbn [sv_denot]. rewrite U20. reflexivity. }
assert (Q11 : getr (ms_regs ms) 11 = w64 96) by (a11h_rreg HS; reflexivity).
assert (Q12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_s)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0. exact (a11h_fmt_atom E HEI). }
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (p_c v + seg_spec.RC_READING)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0. exact E32. }
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 2%nat (Z_to_bv 5 2) eq_refl).
  apply (a5_rg_get regs _ 2 _ HRG). unfold a5_FI; pa2_in. }
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl).
  apply (a5_rg_get regs _ 3 _ HRG). unfold a5_FI; pa2_in. }
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl).
  apply (a5_rg_get regs _ 4 _ HRG). unfold a5_FI; pa2_in. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 22; 18; 19; 20; 21; 24; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [a11h_rreg HS; rewrite pa2_crt_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Rsp : spZ (ms_regs ms) = pf_s1 v) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (EA2 : A11_RET_SN2 = 14432) by (vm_compute; reflexivity).
(* c->reading, the second call's argument *)
destruct (a11h_reading (rdW Wc memc0) (p_c v) cf HRC) as (RZ & RN & RL & RP).
assert (STR0 : sa_str (rdW Wc memc0) (p_c v + seg_spec.RC_READING) (rc_reading cf)).
{ split; [split; [exact RZ | exact RN]|].
  intros x Hx. apply RP.
  pose proof (Z.mod_pos_bound (p_c v + seg_spec.RC_READING + Z.of_nat (length (rc_reading cf))) 8 ltac:(lia)). lia. }
assert (STR2 : sa_str (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_READING) (rc_reading cf)).
{ apply (a11h_k_str v pos gi bc mc _ _ G BLK K1); [| lia | lia | exact STR0].
  intros x Hx. apply (a11h_far_c v pos gi bc mc G BLK); lia. }
unfold a11_post, pf_postm, PF_POSTr.
pmkst HS.
eapply SRr_bind.
{ apply (a11h_snp (fx := fx) v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv gi bc mc 0x40 96
    (p_c v + seg_spec.RC_READING) (rc_reading cf) (Z_to_bv 64 (BASE + A11_RET_SN2)) G BLK HJ Hbc Q10 Q11 Q12 Q13
    Rsp Q3 Q4 Q1 (ret_ok_codeptr_v A11_RET_SN2 ltac:(rewrite EA2; lia) ltac:(rewrite EA2; reflexivity))).
  - lia.
  - lia.
  - lia.
  - exact (a11h_k_lit v pos gi bc mc _ _ G BLK K1 _ _ (LI F_s a11h_lit_F_s)).
  - exact (a11h_k_ssp v pos gi bc mc _ _ G BLK K1 SS).
  - exact (a11h_k_rod v pos gi bc mc _ _ G BLK K1 RO).
  - exact (fxrel_frm0 f0 fx HFRM Hfx).
  - lia.
  - exact STR2.
  - exact (a6_heap_addr B lyc Sc Wc (ms_mem ms) mdv _ _ (proj1 HJ)
      (a11h_heap_sub lyc Sc (p_c v) seg_spec.SEG_C_SIZE (p_c v + seg_spec.RC_READING)
         (Z.of_nat (length (rc_reading cf)) + 1) C2 ltac:(lia) ltac:(rewrite EC; lia)) ltac:(lia)).
  - exact (amem8_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv bc mc (p_c v + seg_spec.RC_READING)
      (Z.of_nat (length (rc_reading cf))) (proj1 HJ) Hbc ltac:(lia) ltac:(lia) ltac:(lia)).
  - lia.
  - unfold seg_spec.cstr_span.
    pose proof (Z.mod_pos_bound (- (p_c v + seg_spec.RC_READING + Z.of_nat (length (rc_reading cf)) + 1)) 8
      ltac:(lia)).
    unfold RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - right. lia. }
cbv beta. intros W2 c2 _ (-> & fx2 & regs2 & mem2 & md2 & Hf2 & -> & HJ2 & HP2 & HB3 & HK3 & HPR3).
eapply (srr_apost_baseF_lift (fx := fx) SEGS fx2); [exact Hf2|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKP & _).
apply (a11h_r2 (fx := fx2) n HL f0 v pos lyc Sc Wc rX0 memc0 mdc0 cf nm o ln d gi val i regs2 mem2 md2 HB HMID HST
  HNZ HBT (fxrel_trans f0 fx fx2 Hfx Hf2) HJ2).
- apply (a11h_kept_trans v gi _ _ _ K1).
  + intros a Ha Hw. apply HK3; [exact Ha | intros Hc; apply Hw; right; lia | intros Hc; apply Hw; left; exact Hc].
  + intros a Ha Hv.
    assert (HW : (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) \/
      (a11h_cur v gi + 0x40 <= a < a11h_cur v gi + 0x40 + (Z.of_nat (length (rc_reading cf)) + 1)) \/
      (~ (a11h_cur v gi + 0x40 <= a < a11h_cur v gi + 0x40 + (Z.of_nat (length (rc_reading cf)) + 1)) /\
       ~ (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v))) by lia.
    destruct HW as [HW | [HW | [HW1 HW2]]].
    * apply (aview_some_of_apresent SEGS). apply HSTKP. unfold RtPFCmd.CMD_SNP_K, ESTACK in HW. rewrite SPF. lia.
    * replace a with (a11h_cur v gi + 0x40 + (a - (a11h_cur v gi + 0x40))) by lia. rewrite HB3 by lia.
      discriminate.
    * rewrite (HK3 a Ha HW1 HW2). exact Hv.
- intros j Hj. rewrite (HK3 (a11h_cur v gi + 0x24 + j)) by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia).
  rewrite KM1 by lia. exact (B1 j Hj).
- intros k Hk. rewrite (HK3 (a11h_cur v gi + 0x3c + k)) by (unfold RtPFCmd.CMD_SNP_K, ESTACK; lia). exact (B2 k Hk).
- exact HB3.
- apply (a5_rg_pres (ms_regs ms) regs2 _ HP2).
  + apply Forall_app. split; [apply a5_FI_cs|]. apply Forall_app. split; [apply a5_RL_cs|].
    apply Forall_app. split; [apply a5_RM_cs|].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst]. unfold acallee_saved. lia.
  + unfold pf_rg, a5_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      (rewrite QK; [apply (a5_rg_get regs _ _ _ HRG); unfold a5_FI, PF_RL, PF_RM; pa2_in | pa2_in]).
Qed.
End r1.

(** ** HIT (0x88540) -> the first snprintf -> RET_SN1: the theorem *)
Section h. Context {fx : YK11.FPState}.
Theorem a11a_hit_ok : forall n : nat, HA_LOWOUT B n -> A11_HIT_stmt (fx := fx) B n.
Proof.
intros n HL v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val i HI.
destruct HI as ((HB & HMID & HST & HSTRv & HINB & HSLb) & HBT & HLOW & HRG).
pose proof HSTRv as ((_ & HNZ) & _).
destruct (a11h_geo (fx := fx) v pos lyc Sc Wc rX memc mdc PF_SC_L146 cf nm _ gi HB HST)
  as (HAR0 & Hly & Hin & G & Hgi & bc & mc & Hbc & BLK & HFD).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof BLK as (BL1 & BL2 & BL3 & BL4 & BL5 & BL6 & BL7 & BL8 & BL9).
pose proof (a11h_cur_in v gi bc mc BLK) as (CI1 & CI2 & CI3 & CI4).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof asan_consts as (AC1 & _).
pose proof (a11f_low_len val 24 HNZ) as LL.
pose proof HB as (_ & (HJ & _ & _ & _ & _ & _ & HFRM & HFI) & HOBJ & _ & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & _ & _ & LI & RO & SS).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (a5_rg_get rX _ 9 _ HFI); pa2_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 (pf_F v pos + PF_O_L146)) by (apply (a5_rg_get rX _ 20 _ HRG); unfold PF_RL, PF_RM; pa2_in).
pose proof (Forall_inv HSLb) as Wb0. cbn [fst snd] in Wb0.
pose proof (a11h_seed0 (fx := fx) v pos gi Wc rX memc G R9 Wb0 ltac:(lia)) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX [w64 (a11h_cur v gi)]))) by apply Eimg_env.
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r ->
  ew (Eimg (Ereg rX [w64 (a11h_cur v gi)])) n0 = getr rX r) by (intros n0 r Hn; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew (Eimg (Ereg rX [w64 (a11h_cur v gi)])) 32 = w64 (a11h_cur v gi))
  by (rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
revert HS HEI EE E32. generalize (Eimg (Ereg rX [w64 (a11h_cur v gi)])) as E. intros E HS HEI EE E32.
assert (U32 : bv_unsigned (ew E 32) = a11h_cur v gi) by (rewrite E32; unfold w64; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + A11_HIT)) with (Z_to_bv 64 (BASE + A11_HIT)).
(* 0x88540 .. 0x8855c: a4 = cur, a0 = cur + 0x24, a2 = "%s", a1 = 24, a3 = low146, s4 = cur, the jal *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ a11h_awr_ro. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]). destruct Hin'. }
assert (KV0 : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
assert (K0 : a11h_kept v gi (rdW Wc memc) (rdW Wc (ms_mem ms)))
  by (split; [intros a Ha _; exact (KM0 a Ha) | intros a Ha Hv; exact (KV0 a Hv)]).
(* the registers at the jal *)
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A11_RET_SN1)).
{ a11h_rreg HS. cbn [sv_denot]. rewrite (img_env_codeptr E HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms) 10 = w64 (a11h_cur v gi + 0x24)).
{ a11h_rreg HS. cbn [sv_denot]. rewrite U32. reflexivity. }
assert (Q11 : getr (ms_regs ms) 11 = w64 24) by (a11h_rreg HS; reflexivity).
assert (Q12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_s)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0. exact (a11h_fmt_atom E HEI). }
assert (Q13 : getr (ms_regs ms) (Z_to_bv 5 13) = w64 (pf_F v pos + PF_O_L146)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 20%nat (Z_to_bv 5 20) eq_refl). exact R20. }
assert (Q20 : getr (ms_regs ms) (Z_to_bv 5 20) = w64 (a11h_cur v gi)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0. exact E32. }
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 2%nat (Z_to_bv 5 2) eq_refl).
  apply (a5_rg_get rX _ 2 _ HFI). pa2_in. }
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl).
  apply (a5_rg_get rX _ 3 _ HFI). pa2_in. }
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ a11h_rreg HS. rewrite pa2_crt_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl).
  apply (a5_rg_get rX _ 4 _ HFI). pa2_in. }
assert (QK : forall r, In r [2; 3; 4; 8; 9; 22; 18; 19; 21; 24; 26; 27] ->
    getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr]; [a11h_rreg HS; rewrite pa2_crt_den_atom0; apply EE; reflexivity |]). destruct Hr. }
assert (Rsp : spZ (ms_regs ms) = pf_s1 v) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (EA1 : A11_RET_SN1 = 14380) by (vm_compute; reflexivity).
(* low146, the first call's argument: in the frame, its three shadow cells 0x5c .. 0x5e in scope *)
assert (F8 : pf_F v pos mod 8 = 0) by (apply Z.mod_divide in G8; [destruct G8 as [q Hq]; rewrite Hq;
  replace (q * 32) with ((4 * q) * 8) by lia; apply Z_mod_mult | lia]).
assert (HZ : forall j, 92 <= j < 95 -> rdW Wc (ms_mem ms) (pf_SH v pos + j) = Some 0).
{ intros j Hj. rewrite KM0 by (unfold kHighShadowEnd, kLowMemEnd in G11, G12; lia). rewrite (HFSH j ltac:(lia)).
  f_equal.
  apply Z.eqb_eq. revert j Hj. apply (pa2_zrange (fun j => pf_shb PF_SC_L146 j =? 0) 92 3). vm_compute. reflexivity. }
assert (LADDR : sa_addr (rdW Wc (ms_mem ms)) (pf_F v pos + PF_O_L146) (Z.of_nat (length (r_low val 0 24)) + 1)).
{ unfold PF_O_L146. split; [lia|]. split; [lia|].
  split; [exact (amem_range_sub_app (pf_F v pos) 2048 (pf_F v pos + 0x2e0) (Z.of_nat (length (r_low val 0 24)) + 1)
    G9 G7 ltac:(lia) ltac:(lia) ltac:(lia))|].
  split.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace (SHADOW_OFF + x / 8) with (pf_SH v pos + (x / 8 - pf_F v pos / 8)) by (rewrite G10; lia).
    apply HZ. pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF. rewrite F8 in DF.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia.
  - intros Hn. apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv 5 pos); [exact (proj1 HJ) | exact Hin | | | exact Hn];
      rewrite Hly; change (frame_addr (p_ly v) 5 pos) with (pf_F v pos); change (fs_frame_bytes 5) with 2048; lia. }
assert (LSTR : sa_str (rdW Wc (ms_mem ms)) (pf_F v pos + PF_O_L146) (r_low val 0 24)).
{ apply (a11h_k_str v pos gi bc mc _ _ G BLK K0); [| unfold PF_O_L146; lia | unfold PF_O_L146; lia | exact HLOW].
  intros x Hx. apply (a11h_far_frame v pos gi bc mc G BLK (pf_F v pos)); [exact HFD | lia | unfold PF_O_L146 in Hx; lia | lia]. }
unfold a11_post, pf_postm, PF_POSTr.
pmkst HS.
eapply SRr_bind.
{ apply (a11h_snp (fx := fx) v pos lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv gi bc mc 0x24 24
    (pf_F v pos + PF_O_L146) (r_low val 0 24) (Z_to_bv 64 (BASE + A11_RET_SN1)) G BLK HJ Hbc Q10 Q11 Q12 Q13
    Rsp Q3 Q4 Q1 (ret_ok_codeptr_v A11_RET_SN1 ltac:(rewrite EA1; lia) ltac:(rewrite EA1; reflexivity))).
  - lia.
  - lia.
  - lia.
  - exact (a11h_k_lit v pos gi bc mc _ _ G BLK K0 _ _ (LI F_s a11h_lit_F_s)).
  - exact (a11h_k_ssp v pos gi bc mc _ _ G BLK K0 SS).
  - exact (a11h_k_rod v pos gi bc mc _ _ G BLK K0 RO).
  - exact HFRM.
  - unfold PF_O_L146. lia.
  - exact LSTR.
  - exact LADDR.
  - exact (amem_range_sub_app (pf_F v pos) 2048 (pf_F v pos + PF_O_L146) (Z.of_nat (length (r_low val 0 24)) + 8)
      G9 G7 ltac:(unfold PF_O_L146; lia) ltac:(unfold PF_O_L146; lia) ltac:(lia)).
  - lia.
  - unfold seg_spec.cstr_span, PF_O_L146.
    pose proof (Z.mod_pos_bound (- (pf_F v pos + 0x2e0 + Z.of_nat (length (r_low val 0 24)) + 1)) 8 ltac:(lia)).
    unfold RtPFCmd.CMD_SNP_K, ESTACK. lia.
  - unfold seg_spec.cstr_span, PF_O_L146.
    pose proof (Z.mod_pos_bound (- (pf_F v pos + 0x2e0 + Z.of_nat (length (r_low val 0 24)) + 1)) 8 ltac:(lia)).
    lia. }
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hf1 & -> & HJ2 & HP2 & HB1 & HK1 & HPR1).
eapply (srr_apost_baseF_lift (fx := fx) SEGS fx1); [exact Hf1|].
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKP & _).
apply (a11h_r1 (fx := fx1) n HL fx v pos lyc Sc Wc rX memc mdc cf nm o ln d gi val i regs2 mem2 md2 HB HMID HST
  HNZ HBT Hf1 HJ2).
- apply (a11h_kept_trans v gi _ _ _ K0).
  + intros a Ha Hw. apply HK1; [exact Ha | intros Hc; apply Hw; right; lia | intros Hc; apply Hw; left; exact Hc].
  + intros a Ha Hv.
    assert (HW : (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v) \/
      (a11h_cur v gi + 0x24 <= a < a11h_cur v gi + 0x24 + (Z.of_nat (length (r_low val 0 24)) + 1)) \/
      (~ (a11h_cur v gi + 0x24 <= a < a11h_cur v gi + 0x24 + (Z.of_nat (length (r_low val 0 24)) + 1)) /\
       ~ (pf_s1 v - RtPFCmd.CMD_SNP_K <= a < pf_s1 v))) by lia.
    destruct HW as [HW | [HW | [HW1 HW2]]].
    * apply (aview_some_of_apresent SEGS). apply HSTKP. unfold RtPFCmd.CMD_SNP_K, ESTACK in HW. rewrite SPF. lia.
    * replace a with (a11h_cur v gi + 0x24 + (a - (a11h_cur v gi + 0x24))) by lia. rewrite HB1 by lia.
      discriminate.
    * rewrite (HK1 a Ha HW1 HW2). exact Hv.
- exact HB1.
- apply (a5_rg_pres (ms_regs ms) regs2 _ HP2).
  + apply Forall_app. split; [apply a5_FI_cs|]. apply Forall_app. split; [apply a5_RL_cs|].
    apply Forall_app. split; [apply a5_RM_cs|].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst]. unfold acallee_saved. lia.
  + unfold pf_rg, a5_FI, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [exact Q20
            | rewrite QK; [first [solve [apply (a5_rg_get rX _ _ _ HFI); pa2_in]
                                 | solve [apply (a5_rg_get rX _ _ _ HRG); unfold PF_RL, PF_RM; pa2_in]]
                          | solve [pa2_in]]].
Qed.
End h.

End d.
