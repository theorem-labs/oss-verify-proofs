(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed. *)
(* Modified by Theorem Labs: the shared part of proofs/libreac/fuzz_decode/lib/A/Prog/check_round_trip_cg.v (origin/ossv/recipes 88154566652a: dec_utrace, the read-only reads and their two instance facts, the value-0 shadow granule of a table, the leaf instances dec_leaf_at / dec_leaf_wr_at and the runtime cells as constant cells of the record) for reac-repacer/fuzz_uci's image A: module paths changed, the image is the core's tfibsegs (lib/A/AB1v.v), the read-only reads and the cells are fuzz_uci.asan's, measured on the pinned image. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/UciCg.v, with its module paths changed; 778 of its 849 lines of code are new or changed and 69 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/DgnTransportCg.v; 74 of its 131 lines of code are new or changed and 792 lines of the source are left out. *)
(* io_send_seg_src: where io_send's frame may lie.

   lib/A/Prog/DgnTransportCg.v trans_src_ok lets the bytes a callee reads lie in a heap block, in a caller's
   side-stack frame, in a harness global, in the machine stack, or in TRANS_RO_RD. Carrying them across a callee
   that is not a leaf (check_sent_frame, check_inflight_retry, check_latest_sent) needs acall_kept_g's image
   clause, and that clause asks, for a TRANS_RO_RD byte, that it is not an owned static and not errno:
   trans_ro_rd_unowned B and trans_rom_no_errno B, which trans_src_ok_acall_g takes as premises.
   transport_io_send_cg_holds_stmt gives NEITHER.

   It does not have to: io_send's frame can never lie in TRANS_RO_RD. check_sent_frame's model call makes the frame
   at least SPEC_MIN_FRAME = 60 bytes (lib/A/Prog/io_send_seg_frm.v ios_len60), and no run of 60 addresses is
   TRANS_RO_RD throughout: the longest run of the table is the two jump tables 0x20fac (32 bytes) and 0x20fcc
   (24 bytes), which touch, so 56 bytes, and every other range is shorter and has a gap after it (ios_ro_run60,
   decided range by range). ios_src_ok_not_ro is what a segment uses: at 60 <= n the TRANS_RO_RD case of
   trans_src_ok is refuted, and the cases left are the heap block, the caller's side-stack frame, G and the
   machine stack, which every callee keeps without those two record facts. ios_src_ok_acall_g is DgnTransportCg.v
   trans_src_ok_acall_g's proof with that case closed by ios_ro_run60 instead of the two record facts: the walk
   carries the frame across check_sent_frame, check_inflight_retry and check_latest_sent with it. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
Import ListNotations.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* The table as a decision. *)
Definition ios_ro_b (a : Z) : bool :=
  existsb (fun r : Z * Z => ((fst r <=? a) && (a <? fst r + snd r))%bool) TRANS_RO_RD.

Lemma ios_ro_b_of : forall a, trans_in_ro_rd a -> ios_ro_b a = true.
Proof.
  intros a H. apply Exists_exists in H as (r & Hin & Hr). unfold ios_ro_b. apply existsb_exists.
  exists r. split; [exact Hin|]. unfold in_zr in Hr. cbn [fst snd] in Hr.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

(* The first address at or after each range's end that no range of the table holds (the two jump tables touch, so
   they share one): twenty-five addresses, each decided against the table. *)
Definition ios_ro_gaps : list Z :=
  [0x10358; 0x103a0; 0x20fe4; 0x21020; 0x21046; 0x21066; 0x21086; 0x210a3; 0x210c9; 0x210e9; 0x21107; 0x21126;
   0x21146; 0x21166; 0x21186; 0x211c6; 0x21209; 0x21229; 0xa3d80; 0xa3db0; 0xa3dd0; 0xa3e00; 0xa3e40; 0xa3e78;
   0xa3ed0].

Lemma ios_ro_gaps_free : forallb (fun g => negb (ios_ro_b g)) ios_ro_gaps = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ios_ro_gap_of : forall g, In g ios_ro_gaps -> ios_ro_b g = false.
Proof.
  intros g Hin. pose proof (proj1 (forallb_forall _ _) ios_ro_gaps_free g Hin) as H.
  apply negb_true_iff in H. exact H.
Qed.

(* Every address the table holds has a gap of the list within 56 bytes above it. The range that holds a is found by
   list membership (no open comparison is evaluated), then the gap above it is tried from the list. *)
Ltac ios_try_gap g :=
  exists g; split;
  [ unfold ios_ro_gaps; cbn [In]; repeat (first [left; reflexivity | right]) | lia ].

Lemma ios_ro_near_gap : forall a, ios_ro_b a = true ->
  exists g, In g ios_ro_gaps /\ a < g <= a + 56.
Proof.
  intros a H. unfold ios_ro_b in H. apply existsb_exists in H as (r & Hin & Hr).
  apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold TRANS_RO_RD, TRANS_RO_GLOBALS in Hin. cbn [app In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [fst snd] in H1, H2 |]); try contradiction.
  all: unfold TRANS_JT_LLVMF, TRANS_JT_NOTICE, TRANS_K_LLVMF, TRANS_K_POLL, TRANS_SCALE, TRANS_HOST, TRANS_DESK,
         TRANS_SPEC_BCAST, TRANS_SPEC_OUI, TRANS_STR_C24, TRANS_STR_PC, TRANS_CMD, TRANS_DESK2, TRANS_NOTDD,
         TRANS_OTHER, TRANS_STR4, TRANS_BROADCAST, TRANS_PNAME0, TRANS_PNAME1, TRANS_IO, TRANS_SPEC_C24,
         TRANS_SPEC_PC, TRANS_SRC, TRANS_DST, TRANS_NAME, TRANS_PERS in H1, H2.
  all: first
    [ ios_try_gap 0x10358 | ios_try_gap 0x103a0 | ios_try_gap 0x20fe4 | ios_try_gap 0x21020
    | ios_try_gap 0x21046 | ios_try_gap 0x21066 | ios_try_gap 0x21086 | ios_try_gap 0x210a3
    | ios_try_gap 0x210c9 | ios_try_gap 0x210e9 | ios_try_gap 0x21107 | ios_try_gap 0x21126
    | ios_try_gap 0x21146 | ios_try_gap 0x21166 | ios_try_gap 0x21186 | ios_try_gap 0x211c6
    | ios_try_gap 0x21209 | ios_try_gap 0x21229 | ios_try_gap 0xa3d80 | ios_try_gap 0xa3db0
    | ios_try_gap 0xa3dd0 | ios_try_gap 0xa3e00 | ios_try_gap 0xa3e40 | ios_try_gap 0xa3e78
    | ios_try_gap 0xa3ed0 ].
Qed.

(* So no sixty addresses in a row are all TRANS_RO_RD. *)
Lemma ios_ro_run60 : forall q n, 60 <= n -> (forall a, q <= a < q + n -> trans_in_ro_rd a) -> False.
Proof.
  intros q n Hn Hro.
  assert (H0 : ios_ro_b q = true) by (apply ios_ro_b_of; apply Hro; lia).
  destruct (ios_ro_near_gap q H0) as (g & Hin & Hg).
  pose proof (ios_ro_b_of g (Hro g ltac:(lia))) as HT.
  rewrite (ios_ro_gap_of g Hin) in HT. discriminate HT.
Qed.

Section src. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.

(* A range of at least 60 bytes that trans_src_ok places is NOT in TRANS_RO_RD. *)
Lemma ios_src_ok_not_ro : forall lyc Sc (W : world segs) memc q n,
  60 <= n -> trans_src_ok B lyc Sc W memc q n ->
  decode_in_block B lyc Sc q n \/
  ((decode_in_fake lyc Sc q n \/
    ((forall a, q <= a < q + n -> inG TG.G_HARNESS a) /\ trans_sh_any B q n) \/
    (ly_stk_lo lyc <= q /\ q + n <= ly_stk_hi lyc)) /\
   decode_rd_ok W memc q n).
Proof.
  intros lyc Sc W memc q n Hn [Hb | (HL & Hrd)]; [left; exact Hb|].
  right. split; [|exact Hrd].
  destruct HL as [HF | [HG | [HS | (HR & _)]]].
  - left. exact HF.
  - right. left. exact HG.
  - right. right. exact HS.
  - exfalso. exact (ios_ro_run60 q n Hn HR).
Qed.

(* DgnTransportCg.v trans_src_ok_acall_g without the two record facts it takes for the TRANS_RO_RD case: at
   60 <= n that case cannot arise. *)
Lemma ios_src_ok_acall_g : AR_laws segs B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  acall_kept_g segs B TG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  gx_kept segs TG.G_HARNESS W memc W2 mem2 ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 60 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    HK HGK HnE HnEs Hoff Hs Hn.
  pose proof HK as (K1 & K2 & K3 & K4 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct (ios_src_ok_not_ro lyc Sc W memc q n Hn Hs) as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | (S1 & S3)]].
      + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exact (HGK a (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia. }
  split; [|exact KV].
  exact (trans_src_ok_kept B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
           KV KS Hs ltac:(lia)).
Qed.

End src.
