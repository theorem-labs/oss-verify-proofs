(* crtA_w_head: the entry piece of the cgif-form walk of check_round_trip, image A (lib/A/Prog/crtA_cuts.v):
   from CRT_ENTRY to CRT_RET_CALLOC, ending in the cut crtA_at_calloc.

   The walk, in order (the offsets are crtA_iface.v's names):
     1. an INNER journal is started at the entry state (YCbq.v:1827 ajournal_sub_init; stack window
        [spZ regs - DEC_CRT_STK, spZ regs), no footprint, no frame of its own);
     2. crt_seg1_F (the prologue: the 96-byte frame, the shadow offset loaded through the runtime cells) runs as a
        footprint run (crtA_walk.v crtA_run); the inner journal is re-established after the frame write
        (YCbq.v:636 ajournal_exec, the written bytes are in the journal's stack window);
     3. malloc(4 nch ns) by amalloc04_rule (YC5d.v:57), with the entry chain (s0 is still the caller's);
     4. crt_seg2_F (s0 := P), malloc(8 nch) by amalloc04_rule with the empty chain (s0 = P lies below sp);
     5. crt_seg3_F (the `bnez s7` is taken), calloc(3 nch ns, 1) by acalloc04_rule (YGCalloc.v:255) at
        lib/A/DecodeCalloc.v's DEC_CALLOC_MAX / DEC_CALLOC_DEPTH; its depth premise comes from crtA_head's own
        premise `ly_bot lyc + DEC_CALLOC_DEPTH + DEC_CRT_FRAME < spZ regs` (ly_bot is kept by the inner journal);
     6. the cut crtA_at_calloc, taken as the hypothesis of the piece.
   The frame the prologue wrote is kept across each call by the rule's acall_kept (every byte at or above
   alloc_ceiling outside the callee's window [sp - 96 - ASTACK, sp - 96) keeps its view), the scoped read-only view
   crtA_rom_on by acall_kept's image clause at the points of RO_RD (whose side conditions are crtA_ro_scoped), and
   across the footprint runs by the runs' munch.  The float state is the entry's throughout: no float
   instruction runs before +0xc4, and the allocator rules state pre and post at the same {fx}. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n YK1b YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame Cells Step Regs6ss ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import Img0 AsanCells DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeSyms DecodeAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_iface check_round_trip_cg crtA_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import crtA_walk crtA_segs crtA_cells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit AsanKA.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.

(* A closed address term replaced by its value (computed, never written by hand). *)
Ltac crt_val X := let v := eval vm_compute in X in change X with v in *.

(* ---- image facts ---- *)

(* Every loaded segment of image A lies in the image bounds of lib/Reusable/YImgTop.v (the proof of
   a working branch lib/A/Prog/DecodeImg.v decode_img_range / decode_segs_low,
   restated here because that file is not part of this lane). *)
Lemma crtA_img_range : forall a, in_img decodesegs0 a -> IMG_LO <= a < IMG_TOP.
Proof.
intros a (sg & Hin & Hr).
pose proof segs_in_asan as Hall. unfold segs_in in Hall. rewrite forallb_forall in Hall.
pose proof (Hall sg Hin) as Hb. apply andb_true_iff in Hb as [Hlo Hhi].
apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. unfold seg_lo, seg_hi in Hlo, Hhi. lia.
Qed.

Lemma crtA_segs_low : forall a, in_img decodesegs0 a -> 0 <= a < kLowMemEnd.
Proof.
intros a Ha. pose proof (crtA_img_range a Ha) as [H1 H2].
pose proof IMG_LO_val as E1. pose proof IMG_TOP_val as E2. unfold kLowMemEnd. lia.
Qed.

Lemma crtA_rom_img : forall a, in_rom decodesegs0 a -> in_img decodesegs0 a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.

(* ---- traces and chains ---- *)

(* The allocator's trace at a call (YCbq.v:317 call_trace0) is check_round_trip_cg.v's dec_utrace of the return
   address followed by the chain's return addresses. *)
Lemma crtA_trace0 : forall pc0 regs ch, call_trace0 pc0 regs ch = dec_utrace pc0 (raZ regs :: spine ch).
Proof.
intros pc0 regs ch. unfold call_trace0, unwind_of_chain, dec_utrace.
assert (E : flat_map (fun ra : Z => if ra =? pc0 then [] else [ra]) (raZ regs :: spine ch) =
            flat_map (fun r : Z * Z * Z => match r with (_, ra, _) => if ra =? pc0 then [] else [ra] end)
              ((spZ regs, raZ regs, s0Z regs) :: ch)).
{ cbn [flat_map]. f_equal. unfold spine. induction ch as [|[[fp ra] nfp] ch IH]; [reflexivity|].
  cbn [flat_map map fst snd]. rewrite IH. reflexivity. }
rewrite E. reflexivity.
Qed.

(* The same for calloc's trace (YGCalloc.v:216 ctrace0, the same text). *)
Lemma crtA_ctrace0 : forall pc0 regs ch, ctrace0 pc0 regs ch = dec_utrace pc0 (raZ regs :: spine ch).
Proof. intros pc0 regs ch. change (ctrace0 pc0 regs ch) with (call_trace0 pc0 regs ch). apply crtA_trace0. Qed.

(* At a call whose s0 lies at or below sp, bad_next holds and the chain is empty (YG0d.v:218 chain_pre). *)
Lemma crtA_chain_pre_low : forall ly rd (regs : bvmap 5 word),
  4096 <= raZ regs -> s0Z regs <= spZ regs -> chain_pre ly rd regs [].
Proof.
intros ly rd regs Hra Hs. unfold chain_pre. split; [exact Hra|].
destruct (frame0_ok ly regs); [|reflexivity].
unfold bad_next. rewrite (proj2 (Z.leb_le _ _) Hs). cbn [orb]. reflexivity.
Qed.

(* ---- memory ---- *)

(* Two present bytes with the same view are the same byte. *)
Lemma crtA_byte_eq : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  apresent H m a -> apresent H' m' a -> aview decodesegs0 H' m' a = aview decodesegs0 H m a ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros H H' m m' a [Hh [b Hb]] [Hh' [b' Hb']] E.
apply mbyte_of_aview in E. unfold YP09.mbyte, mrestrict in E. rewrite Hh, Hh', Hb, Hb' in E.
rewrite Hb, Hb'. exact E.
Qed.

(* rw_cells is a property of the bytes of its range only. *)
Lemma crtA_rw_cells_eq : forall (m m' : word -> option byte) A cs,
  rw_cells rsegs m A cs ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wa (A + i)) = m (wa (A + i))) ->
  rw_cells rsegs m' A cs.
Proof.
intros m m' A cs [[Hwf [H0 [H1 Hb]]] [W0 [W1 Hw]]] E.
pose proof (cells_bytes_length cs Hwf) as L.
split; [split; [exact Hwf|] |].
- split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (Hb i Hi). unfold mrd. rewrite (E (Z.of_nat i)); [reflexivity|]. rewrite L in Hi. lia.
- split; [exact W0|]. split; [exact W1|]. intros i Hi.
  unfold wview. rewrite (E i Hi). exact (Hw i Hi).
Qed.

Lemma crt_fr_size : forall c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra,
  cells_size (crt_fr c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) = 96%nat.
Proof. reflexivity. Qed.

Lemma crtA_frame_eq : forall (regs0 : bvmap 5 word) (m m' : word -> option byte),
  crtA_frame regs0 m ->
  (forall a, spZ regs0 - CRT_FRAME <= a < spZ regs0 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  crtA_frame regs0 m'.
Proof.
intros regs0 m m' Hf E. unfold crtA_frame in *. apply (crtA_rw_cells_eq m m' _ _ Hf).
intros i Hi. rewrite crt_fr_size in Hi. change (Z.of_nat 96) with 96 in Hi.
unfold wa. apply E. unfold CRT_FRAME. lia.
Qed.

(* A range of visible bytes is in the walk's footprint (LeafCgKit.v:83 RNG_W). *)
Lemma crtA_rng_vis : forall (W : world decodesegs0) a n, 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> w_H W (Z_to_bv 64 (a + i)) = false) ->
  ExecF.rng (LCK.RNG_W (world decodesegs0) (@w_H decodesegs0) W) a n.
Proof.
intros W a n H0 H1 Hv. split; [exact H0|]. split; [exact H1|].
intros b j Hb Hj. unfold LCK.RNG_W, LCK.range_avoids. intros kk Hk. unfold LCK.woff.
assert (Ub : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
rewrite Ub. replace (b + Z.of_nat kk) with (a + (b + Z.of_nat kk - a)) by lia. apply Hv. lia.
Qed.

(* Present bytes form a stack range in decode's sense (lib/Lib/Frame.v stk). *)
Lemma crtA_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
- unfold wview. rewrite Hb. discriminate.
- exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* A register of a state reached by a run, read off the run's register map. *)
Lemma crtA_reg_of : forall (R F : bvmap 5 word) pc fc rv m ro ms' (n : Z) (v : word),
  ms_eqv (MS R F pc fc rv m ro) ms' -> is_x0 (Z_to_bv 5 n) = false -> YKK.getr R (Z_to_bv 5 n) = v ->
  YKK.getr (ms_regs ms') (Z_to_bv 5 n) = v.
Proof.
intros R F pc fc rv m ro ms' n v E Hx Hv.
rewrite (crtA_ms_reg R F pc fc rv m ro ms' (Z_to_bv 5 n) E Hx). exact Hv.
Qed.

Lemma hd_ret64 : YK0s.ret_ok (w64 (CRT_AT 0x64)).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma hd_ret70 : YK0s.ret_ok (w64 (CRT_AT 0x70)).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma hd_ret88 : YK0s.ret_ok (w64 (CRT_AT 0x88)).
Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.

(* raZ of a map whose ra is an address of check_round_trip. *)
Lemma hd_raZ : forall (r : bvmap 5 word) off,
  YKK.getr r (Z_to_bv 5 1) = w64 (CRT_AT off) -> 0 <= off <= 4096 -> raZ r = CRT_AT off.
Proof.
intros r off E Ho. change (raZ r) with (bv_unsigned (YKK.getr r (Z_to_bv 5 1))). rewrite E. unfold w64.
apply unsigned_lit. unfold CRT_AT, CRT_ENTRY. crt_val (decode_sigma DS_check_round_trip). lia.
Qed.

Section Head.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation segs := decodesegs0.
Variable B : asyms.
Variable MT : ameter_ops.
Variable RO_RD : list (Z * Z).
Hypothesis HMPC : pc_wrap_malloc (as_code B) = decode_sigma DS___interceptor_trampoline_malloc.
Hypothesis HFPC : pc_wrap_free (as_code B) = decode_sigma DS___interceptor_trampoline_free.
Hypothesis HCELLS : dec_crt_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC : forall fx' : YKK.FPState, @amalloc04_rule fx' rc dec_A_sink_head segs B MT.
Hypothesis ACALLOC : forall fx' : YKK.FPState, @acalloc04_rule fx' segs B (as_universe B)
  (@ajournal rc dec_A_sink_head segs B) (@acall_kept rc segs B) (mo_ok MT) (mo_le MT) (mo_malloc MT)
  (decode_sigma DS___interceptor_trampoline_calloc) DEC_A_calloc_ra0 DEC_CALLOC_MAX DEC_CALLOC_DEPTH.
Local Notation ajournalA := (@ajournal rc dec_A_sink_head segs B).

Section Entry.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Se : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (audio pcm nch ns bA nA bP nP T : Z) (ch : list (Z * Z * Z)).
Hypothesis HPRE : crtA_pre B MT RO_RD STK sp0 FP ly Se W0 mem0 md0 own lyc Sc W memc mdc k regs
  audio pcm nch ns bA nA bP nP T ch.
Hypothesis CUT : crtA_at_calloc B MT RO_RD.
Hypothesis HFRM : frm_zero (@fp_csr fx).
(* The stack depth the calloc rule asks at its call (YGCalloc.v:258), stated at the entry by the statement
   (check_round_trip_cg.v, after `3 * nch * ns <= 1440`): sp at the call is spZ regs - DEC_CRT_FRAME. *)
Hypothesis HDEPTH : ly_bot lyc + DEC_CALLOC_DEPTH + DEC_CRT_FRAME < spZ regs.
Local Notation POST := (dec_crt_post B MT STK sp0 FP ly Se W0 mem0 md0 own lyc Sc W memc k regs nch ns).
(* The inner journal: from the entry state, stack window [spZ regs - DEC_CRT_STK, spZ regs). *)
Local Notation JI ly1 S1 W1 m1 md1 k1 :=
  (ajournalA DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 W1 m1 md1 k1).

Ltac hd_pre := pose proof HPRE as (HJ & Hra & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hch & Hal & Hwlo & Hwhi &
  Hev & Hnch & Hns & Hreg & HbA & HbA1 & HbA2 & HbP & HbP1 & HbP2 & Hbraid & Hnev & Hlive & Hmo & Hcost &
  Htm & Htf & Hfix & Hrom & Hsc).

(* The registers check_round_trip keeps from its prologue on (callee-saved, so every call keeps them). *)
Definition hd_kept (regs1 : bvmap 5 word) : Prop :=
  YKK.getr regs1 (Z_to_bv 5 2) = w64 (spZ regs - CRT_FRAME) /\
  YKK.getr regs1 (Z_to_bv 5 3) = YKK.getr regs (Z_to_bv 5 3) /\
  YKK.getr regs1 (Z_to_bv 5 4) = YKK.getr regs (Z_to_bv 5 4) /\
  YKK.getr regs1 (Z_to_bv 5 9) = w64 audio /\
  YKK.getr regs1 (Z_to_bv 5 18) = w64 ns /\ YKK.getr regs1 (Z_to_bv 5 19) = w64 nch /\
  YKK.getr regs1 (Z_to_bv 5 20) = w64 (3 * (nch * ns)) /\
  YKK.getr regs1 (Z_to_bv 5 22) = w64 pcm /\ YKK.getr regs1 (Z_to_bv 5 23) = w64 (nch * ns) /\
  YKK.getr regs1 (Z_to_bv 5 24) = w64 ASAN_K /\
  YKK.getr regs1 (Z_to_bv 5 25) = YKK.getr regs (Z_to_bv 5 25) /\
  YKK.getr regs1 (Z_to_bv 5 26) = YKK.getr regs (Z_to_bv 5 26) /\
  YKK.getr regs1 (Z_to_bv 5 27) = YKK.getr regs (Z_to_bv 5 27).

Ltac kp_by HP n K := etransitivity; [apply (HP n); unfold acallee_saved; lia | exact K].

Lemma hd_kept_pres : forall r1 r2, hd_kept r1 -> aregs_preserved r1 r2 -> hd_kept r2.
Proof.
intros r1 r2 (K2 & K3 & K4 & K9 & K18 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K27) HP.
unfold hd_kept.
split; [kp_by HP 2 K2|]. split; [kp_by HP 3 K3|]. split; [kp_by HP 4 K4|]. split; [kp_by HP 9 K9|].
split; [kp_by HP 18 K18|]. split; [kp_by HP 19 K19|]. split; [kp_by HP 20 K20|]. split; [kp_by HP 22 K22|].
split; [kp_by HP 23 K23|]. split; [kp_by HP 24 K24|]. split; [kp_by HP 25 K25|]. split; [kp_by HP 26 K26|].
kp_by HP 27 K27.
Qed.

Ltac kx X K := apply X; [cbn [In]; lia | exact K].

(* A run that leaves the kept registers alone keeps hd_kept. *)
Lemma hd_kept_run : forall r1 (R F : bvmap 5 word) pc fc rv m ro ms',
  hd_kept r1 -> ms_eqv (MS R F pc fc rv m ro) ms' ->
  (forall n, In n [2; 3; 4; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] ->
     YKK.getr R (Z_to_bv 5 n) = YKK.getr r1 (Z_to_bv 5 n)) ->
  hd_kept (ms_regs ms').
Proof.
intros r1 R F pc fc rv m ro ms' HK EQV HE.
assert (X : forall n v, In n [2; 3; 4; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] ->
  YKK.getr r1 (Z_to_bv 5 n) = v -> YKK.getr (ms_regs ms') (Z_to_bv 5 n) = v).
{ intros n v Hn Hv. rewrite (crtA_ms_reg R F pc fc rv m ro ms' (Z_to_bv 5 n) EQV).
  - rewrite (HE n Hn). exact Hv.
  - cbn [In] in Hn. repeat (destruct Hn as [<- | Hn]; [reflexivity|]). destruct Hn. }
destruct HK as (K2 & K3 & K4 & K9 & K18 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K27).
unfold hd_kept.
split; [kx X K2|]. split; [kx X K3|]. split; [kx X K4|]. split; [kx X K9|].
split; [kx X K18|]. split; [kx X K19|]. split; [kx X K20|]. split; [kx X K22|].
split; [kx X K23|]. split; [kx X K24|]. split; [kx X K25|]. split; [kx X K26|].
kx X K27.
Qed.

(* ---- facts of the entry ---- *)

Lemma hd_nn : 2 <= nch <= 127 /\ 1 <= ns <= 12 /\ 1 <= nch * ns <= 480.
Proof. hd_pre. split; [exact Hnch|]. split; [exact Hns|]. nia. Qed.

Lemma hd_sp_rng : YM05.alloc_ceiling + DEC_CRT_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof.
hd_pre.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hc & Hlo & Hhi & H47 & _) & _).
lia.
Qed.

Lemma hd_sp0_16 : sp0 mod 16 = 0.
Proof.
hd_pre. destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H16 & _) & _). exact H16.
Qed.

Lemma hd_cost :
  0 <= mo_malloc MT (4 * (nch * ns)) /\ 0 <= mo_malloc MT (8 * nch) /\ 0 <= mo_malloc MT (3 * (nch * ns)) /\
  mo_malloc MT (4 * (nch * ns)) + mo_malloc MT (8 * nch) + mo_malloc MT (3 * (nch * ns)) <= T.
Proof.
hd_pre. pose proof hd_nn as (_ & _ & Hnn).
pose proof (mo_malloc_nonneg MT MTL (4 * (nch * ns)) ltac:(lia)).
pose proof (mo_malloc_nonneg MT MTL (8 * nch) ltac:(lia)).
pose proof (mo_malloc_nonneg MT MTL (3 * (nch * ns)) ltac:(lia)).
pose proof (mo_free_nonneg MT MTL).
unfold dec_crt_cost in Hcost. lia.
Qed.

Lemma hd_spZ1 : forall r1, hd_kept r1 -> spZ r1 = spZ regs + -96.
Proof.
intros r1 (K2 & _). pose proof hd_sp_rng as [Hs1 Hs2]. pose proof asan_consts as (C1 & _).
change (spZ r1) with (bv_unsigned (YKK.getr r1 (Z_to_bv 5 2))). rewrite K2. unfold w64, CRT_FRAME.
rewrite unsigned_lit; [lia|]. unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hs1. lia.
Qed.

Lemma hd_gptp : forall r1, hd_kept r1 ->
  YKK.getr r1 (Z_to_bv 5 3) = w64 (as_gp B) /\ YKK.getr r1 (Z_to_bv 5 4) = w64 (as_tp B).
Proof.
intros r1 (K2 & K3 & K4 & _). hd_pre.
split; [rewrite K3; exact Hgp | rewrite K4; exact Htp].
Qed.

(* ---- facts of the inner journal ---- *)

Lemma hd_win : forall lyX SX WX mX mdX k1, JI lyX SX WX mX mdX k1 ->
  forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent (w_H WX) mX a.
Proof.
intros lyX SX WX mX mdX k1 HJ1.
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). exact Hpres.
Qed.

Lemma hd_AR : forall lyX SX WX mX mdX k1, JI lyX SX WX mX mdX k1 -> AR segs B lyX SX WX mX mdX.
Proof. intros lyX SX WX mX mdX k1 HJ1. destruct HJ1 as (HAR & _). exact HAR. Qed.

(* ly_bot (YG0f.v:63, ly_top - kStackSpan) is kept by the inner journal: its layout_le keeps ly_top. *)
Lemma hd_bot : forall lyX SX WX mX mdX k1, JI lyX SX WX mX mdX k1 -> ly_bot lyX = ly_bot lyc.
Proof.
intros lyX SX WX mX mdX k1 HJ1. destruct HJ1 as (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). unfold ly_bot. rewrite Etop. reflexivity.
Qed.

Lemma hd_nev : forall lyX SX WX mX mdX k1, JI lyX SX WX mX mdX k1 -> k1 <= 2 -> st_nev SX < EV_MAX.
Proof.
intros lyX SX WX mX mdX k1 HJ1 Hk. hd_pre.
destruct HJ1 as (_ & _ & _ & _ & _ & _ & Hn1 & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & Hn0 & _).
unfold DEC_CRT_EV in Hnev. lia.
Qed.

Lemma hd_bb : forall lyX SX l, ablocks B lyX SX = ablocks B lyc Sc ++ l ->
  blocks_bytes SX = blocks_bytes Sc + bsum l.
Proof.
intros lyX SX l E. rewrite (blocks_bytes_bsum B lyX SX), E, bsum_app, <- (blocks_bytes_bsum B lyc Sc).
reflexivity.
Qed.

(* ---- what a call keeps ---- *)

(* The frame [sp - 96, sp) lies above the callee's window [sp - 96 - ASTACK, sp - 96). *)
Lemma hd_frame_call : forall W1 m1 W2 m2 lyX SX (E : Z -> Prop),
  crtA_frame regs m1 ->
  (forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent (w_H W1) m1 a) ->
  (forall a, spZ regs - DEC_CRT_STK <= a < spZ regs -> apresent (w_H W2) m2 a) ->
  @acall_kept rc segs B lyX SX W1 m1 W2 m2 (spZ regs + -96 - ASTACK) (spZ regs + -96) E ->
  crtA_frame regs m2.
Proof.
intros W1 m1 W2 m2 lyX SX E HF H1 H2 (K1 & _).
pose proof hd_sp_rng as [Hs1 Hs2]. pose proof asan_consts as (C1 & _).
apply (crtA_frame_eq regs m1 m2 HF). intros a Ha. unfold CRT_FRAME in Ha.
unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *.
apply (crtA_byte_eq (w_H W1) (w_H W2) m1 m2 a); [apply H1; lia | apply H2; lia | apply K1; lia].
Qed.

(* The read-only bytes the callees read keep their view: acall_kept's image clause, whose two side conditions
   are crtA_ro_scoped. *)
Lemma hd_rom_call : forall W1 m1 W2 m2 lyX SX slo shi (E : Z -> Prop),
  crtA_rom_on RO_RD W1 m1 -> @acall_kept rc segs B lyX SX W1 m1 W2 m2 slo shi E -> crtA_rom_on RO_RD W2 m2.
Proof.
intros W1 m1 W2 m2 lyX SX slo shi E HR (_ & _ & K3 & _) a Hin Ha.
hd_pre. destruct (Hsc a Hin) as [N1 N2].
rewrite K3; [exact (HR a Hin Ha) | exact (crtA_rom_img a Ha) | exact N1 | exact N2].
Qed.

(* ---- the walk, backwards from the cut ---- *)

(* At CRT_RET_CALLOC: the cut. *)
Lemma hd_atC : forall ly1 S1 W1 regs1 m1 md1 P Q R,
  JI ly1 S1 W1 m1 md1 3 -> frames S1 = frames Sc ->
  mo_le MT Sc S1 (crtA_acc3 MT nch ns) ->
  crtA_frame regs m1 -> crtA_rom_on RO_RD W1 m1 ->
  ablocks B ly1 S1 = ((ablocks B lyc Sc ++ [(P, 4 * (nch * ns))]) ++ [(Q, 8 * nch)]) ++ [(R, 3 * (nch * ns))] ->
  4096 <= P -> 4096 <= Q -> 4096 <= R ->
  hd_kept regs1 -> YKK.getr regs1 (Z_to_bv 5 8) = w64 P -> YKK.getr regs1 (Z_to_bv 5 21) = w64 Q ->
  YKK.getr regs1 (Z_to_bv 5 10) = w64 R ->
  SRr segs W1 (@cfg_at fx segs (CRT_AT 0x88) regs1 m1 md1) POST.
Proof.
intros ly1 S1 W1 regs1 m1 md1 P Q R HJ1 Hfr Hle HF HR EB HP HQ HRr HK G8 G21 G10.
destruct HK as (K2 & K3 & K4 & K9 & K18 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K27).
apply (CUT STK sp0 FP ly Se W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch
         ly1 S1 W1 m1 md1 regs1 P Q R HPRE).
- unfold crtA_mid. split; [exact HJ1|]. split; [exact Hfr|]. split; [exact Hle|]. split; [exact HF | exact HR].
- unfold crtA_regs.
  split; [exact K2|]. split; [exact K3|]. split; [exact K4|]. split; [exact G8|]. split; [exact K9|].
  split; [exact K18|]. split; [exact K19|]. split; [exact K20|]. split; [exact G21|]. split; [exact K23|].
  split; [exact K24 | exact K27].
- unfold crtA_regs_preloop. split; [exact K22|]. split; [exact K25 | exact K26].
- exact G10.
- exact HFRM.
- unfold crtA_blocks3. split; [|lia].
  rewrite EB, <- !app_assoc. cbn [app].
  eapply perm_trans; [apply Permutation_app_comm|]. cbn [app].
  eapply perm_trans; [apply perm_swap|]. eapply perm_trans; [apply perm_skip; apply perm_swap|].
  apply perm_swap.
Qed.

(* At CRT_RET_MALLOC2 = CRT_AT 0x70: crt_seg3_F, then calloc(3 nch ns, 1). *)
Lemma hd_at70 : forall ly1 S1 W1 regs1 m1 md1 P Q,
  JI ly1 S1 W1 m1 md1 2 -> frames S1 = frames Sc ->
  mo_le MT Sc S1 (mo_malloc MT (4 * (nch * ns)) + mo_malloc MT (8 * nch)) ->
  crtA_frame regs m1 -> crtA_rom_on RO_RD W1 m1 ->
  ablocks B ly1 S1 = (ablocks B lyc Sc ++ [(P, 4 * (nch * ns))]) ++ [(Q, 8 * nch)] -> 4096 <= P -> 4096 <= Q ->
  hd_kept regs1 -> YKK.getr regs1 (Z_to_bv 5 8) = w64 P -> YKK.getr regs1 (Z_to_bv 5 10) = w64 Q ->
  SRr segs W1 (@cfg_at fx segs (CRT_AT 0x70) regs1 m1 md1) POST.
Proof.
intros ly1 S1 W1 regs1 m1 md1 P Q HJ1 Hfr1 Hle1 HF1 HR1 EB1 HP1 HQ1 HK1 G8 G10.
hd_pre.
pose proof hd_nn as (Hn1 & Hn2 & Hnn). pose proof hd_sp_rng as [Hsp1 Hsp2].
pose proof asan_consts as (C1 & _). pose proof hd_cost as (Mc1 & Mc2 & Mc3 & Msum).
pose proof HK1 as (K2 & K3 & K4 & K9 & K18 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K27).
eapply crtA_run.
{ unfold LCK.ms_of_regs. eapply crt_seg3_F with (nn := nch * ns); [exact K20 | exact K23 | lia]. }
intros ms' md' (ms0 & Hms0 & EQV) SBM. subst ms0.
try change (PropExec.seg_rom rsegs) with (YKK.seg_rom decodesegs0) in EQV.
rewrite (crtA_ms_shape _ _ _ _ EQV).
assert (HK2 : hd_kept (ms_regs ms')).
{ apply (hd_kept_run regs1 _ _ _ _ _ _ _ ms' HK1 EQV).
  intros n Hn. cbn [In] in Hn. repeat (destruct Hn as [<- | Hn]; [reflexivity|]). destruct Hn. }
assert (G8' : YKK.getr (ms_regs ms') (Z_to_bv 5 8) = w64 P)
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); [reflexivity | exact G8]).
assert (G21 : YKK.getr (ms_regs ms') (Z_to_bv 5 21) = w64 Q)
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); [reflexivity | exact G10]).
assert (G10' : YKK.getr (ms_regs ms') (Z_to_bv 5 10) = w64 (3 * (nch * ns)))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
assert (G11 : YKK.getr (ms_regs ms') (Z_to_bv 5 11) = w64 1)
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
assert (G1 : YKK.getr (ms_regs ms') (Z_to_bv 5 1) = w64 (CRT_AT 0x88))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
(* the run writes nothing: the inner journal at the new model *)
assert (HJ1' : JI ly1 S1 W1 m1 md' 2).
{ exact (@ajournal_exec rc dec_A_sink_head segs B LAWS crtA_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md'
           (fun _ => False) HJ1 (fun x _ => eq_refl) (mem_grows_refl _) (fun x _ => eq_refl) SBM
           (fun a Ha => False_ind _ Ha)). }
(* P is a heap block, below sp *)
assert (HinP : In (P, 4 * (nch * ns)) (ablocks B ly1 S1))
  by (rewrite EB1; apply in_or_app; left; apply in_or_app; right; left; reflexivity).
destruct (al_blocks segs B LAWS ly1 S1 W1 m1 md' P _ (hd_AR _ _ _ _ _ _ HJ1') HinP) as (_ & _ & HPc & _).
assert (Hreq : 0 < req_size (4 * (nch * ns))) by (unfold req_size; destruct (Z.eqb_spec (4 * (nch * ns)) 0); lia).
assert (Hs0 : s0Z (ms_regs ms') = P).
{ change (s0Z (ms_regs ms')) with (bv_unsigned (YKK.getr (ms_regs ms') (Z_to_bv 5 8))). rewrite G8'.
  unfold w64. apply unsigned_lit. lia. }
assert (Hra' : raZ (ms_regs ms') = CRT_AT 0x88) by (apply hd_raZ; [exact G1 | lia]).
assert (Hch2 : chain_pre ly1 (aview segs (w_H W1) m1) (ms_regs ms') []).
{ apply crtA_chain_pre_low.
  - rewrite Hra'. crt_val (CRT_AT 0x88). lia.
  - rewrite Hs0, (hd_spZ1 _ HK2). unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. lia. }
assert (Htr2 : In (ctrace0 DEC_A_calloc_ra0 (ms_regs ms') []) (as_universe B)).
{ rewrite crtA_ctrace0, Hra'. exact (proj1 (proj2 Hfix)). }
assert (BB : blocks_bytes S1 = blocks_bytes Sc + (4 * (nch * ns) + (8 * nch + 0))).
{ rewrite (hd_bb ly1 S1 [(P, 4 * (nch * ns)); (Q, 8 * nch)]); [reflexivity|].
  rewrite EB1, <- app_assoc. reflexivity. }
assert (Hmo2 : mo_ok MT S1 (mo_malloc MT (3 * (nch * ns) * 1))).
{ rewrite Z.mul_1_r. apply (mok_station MT Sc S1 T _ _ MTL Hmo Hle1); lia. }
assert (Pnev : st_nev S1 < EV_MAX) by exact (hd_nev _ _ _ _ _ _ HJ1' ltac:(lia)).
assert (Plive : blocks_bytes S1 + 3 * (nch * ns) * 1 <= LIVE_MAX)
  by (rewrite BB; unfold DEC_CRT_LIVE in Hlive; lia).
assert (Pdep : ly_bot ly1 + DEC_CALLOC_DEPTH < spZ (ms_regs ms')).
{ rewrite (hd_bot _ _ _ _ _ _ HJ1'), (hd_spZ1 _ HK2). unfold DEC_CRT_FRAME in HDEPTH. lia. }
assert (Pmax : 3 * (nch * ns) * 1 <= DEC_CALLOC_MAX) by (unfold DEC_CALLOC_MAX; lia).
refine (SRr_bind segs W1 _ _ POST
  (ACALLOC fx W1 (ms_regs ms') m1 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 md' 2
     (3 * (nch * ns)) 1 (-96) (w64 (CRT_AT 0x88)) [] HJ1' Pdep G10' G11 ltac:(lia) ltac:(lia)
     ltac:(unfold MALLOC_MAX; lia) Pmax Plive (hd_spZ1 _ HK2) eq_refl ltac:(lia)
     ltac:(unfold DEC_CRT_STK, DEC_CRT_FRAME; lia) (proj1 (hd_gptp _ HK2)) (proj2 (hd_gptp _ HK2)) G1 hd_ret88
     Pnev Hch2 Htr2 Hmo2) _).
intros W2 c2 Hwle (ly2 & S2 & regs2 & m2 & md2 & R & -> & HJ2 & HP2 & H10' & Hfr2 & HR4 & EB2 & HZ & HKEPT & Hle2).
rewrite Z.mul_1_r in EB2, Hle2.
apply (hd_atC ly2 S2 W2 regs2 m2 md2 P Q R).
- exact HJ2.
- rewrite Hfr2. exact Hfr1.
- unfold crtA_acc3. exact (mle_station MT Sc S1 S2 _ _ MTL Hle1 Hle2).
- exact (hd_frame_call W1 m1 W2 m2 ly1 S1 _ HF1 (hd_win _ _ _ _ _ _ HJ1') (hd_win _ _ _ _ _ _ HJ2) HKEPT).
- exact (hd_rom_call W1 m1 W2 m2 ly1 S1 _ _ _ HR1 HKEPT).
- rewrite EB2, EB1. reflexivity.
- exact HP1.
- exact HQ1.
- exact HR4.
- exact (hd_kept_pres _ _ HK2 HP2).
- kp_by HP2 8 G8'.
- kp_by HP2 21 G21.
- exact H10'.
Qed.

(* At CRT_RET_MALLOC1 = CRT_AT 0x64: crt_seg2_F (s0 := P), then malloc(8 nch). *)
Lemma hd_at64 : forall ly1 S1 W1 regs1 m1 md1 P,
  JI ly1 S1 W1 m1 md1 1 -> frames S1 = frames Sc ->
  mo_le MT Sc S1 (mo_malloc MT (4 * (nch * ns))) ->
  crtA_frame regs m1 -> crtA_rom_on RO_RD W1 m1 ->
  ablocks B ly1 S1 = ablocks B lyc Sc ++ [(P, 4 * (nch * ns))] -> 4096 <= P ->
  hd_kept regs1 -> YKK.getr regs1 (Z_to_bv 5 10) = w64 P ->
  SRr segs W1 (@cfg_at fx segs (CRT_AT 0x64) regs1 m1 md1) POST.
Proof.
intros ly1 S1 W1 regs1 m1 md1 P HJ1 Hfr1 Hle1 HF1 HR1 EB1 HP1 HK1 G10.
hd_pre.
pose proof hd_nn as (Hn1 & Hn2 & Hnn). pose proof hd_sp_rng as [Hsp1 Hsp2].
pose proof asan_consts as (C1 & _). pose proof hd_cost as (Mc1 & Mc2 & Mc3 & Msum).
pose proof HK1 as (K2 & K3 & K4 & K9 & K18 & K19 & K20 & K22 & K23 & K24 & K25 & K26 & K27).
eapply crtA_run.
{ unfold LCK.ms_of_regs. eapply crt_seg2_F with (nch := nch); [exact K19 | lia]. }
intros ms' md' (ms0 & Hms0 & EQV) SBM. subst ms0.
try change (PropExec.seg_rom rsegs) with (YKK.seg_rom decodesegs0) in EQV.
rewrite (crtA_ms_shape _ _ _ _ EQV).
assert (HK2 : hd_kept (ms_regs ms')).
{ apply (hd_kept_run regs1 _ _ _ _ _ _ _ ms' HK1 EQV).
  intros n Hn. cbn [In] in Hn. repeat (destruct Hn as [<- | Hn]; [reflexivity|]). destruct Hn. }
assert (G8 : YKK.getr (ms_regs ms') (Z_to_bv 5 8) = w64 P)
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); [reflexivity | exact G10]).
assert (G10' : YKK.getr (ms_regs ms') (Z_to_bv 5 10) = w64 (8 * nch))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
assert (G1 : YKK.getr (ms_regs ms') (Z_to_bv 5 1) = w64 (CRT_AT 0x70))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
assert (HJ1' : JI ly1 S1 W1 m1 md' 1).
{ exact (@ajournal_exec rc dec_A_sink_head segs B LAWS crtA_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md'
           (fun _ => False) HJ1 (fun x _ => eq_refl) (mem_grows_refl _) (fun x _ => eq_refl) SBM
           (fun a Ha => False_ind _ Ha)). }
assert (HinP : In (P, 4 * (nch * ns)) (ablocks B ly1 S1))
  by (rewrite EB1; apply in_or_app; right; left; reflexivity).
destruct (al_blocks segs B LAWS ly1 S1 W1 m1 md' P _ (hd_AR _ _ _ _ _ _ HJ1') HinP) as (_ & _ & HPc & _).
assert (Hreq : 0 < req_size (4 * (nch * ns))) by (unfold req_size; destruct (Z.eqb_spec (4 * (nch * ns)) 0); lia).
assert (Hs0 : s0Z (ms_regs ms') = P).
{ change (s0Z (ms_regs ms')) with (bv_unsigned (YKK.getr (ms_regs ms') (Z_to_bv 5 8))). rewrite G8.
  unfold w64. apply unsigned_lit. lia. }
assert (Hra' : raZ (ms_regs ms') = CRT_AT 0x70) by (apply hd_raZ; [exact G1 | lia]).
assert (Hch2 : chain_pre ly1 (aview segs (w_H W1) m1) (ms_regs ms') []).
{ apply crtA_chain_pre_low.
  - rewrite Hra'. crt_val (CRT_AT 0x70). lia.
  - rewrite Hs0, (hd_spZ1 _ HK2). unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. lia. }
assert (Htr2 : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms') []) (as_universe B)).
{ rewrite crtA_trace0, Hra'. exact (proj1 Hfix). }
assert (BB : blocks_bytes S1 = blocks_bytes Sc + (4 * (nch * ns) + 0)).
{ rewrite (hd_bb ly1 S1 [(P, 4 * (nch * ns))]); [reflexivity | exact EB1]. }
assert (Hmo2 : mo_ok MT S1 (mo_malloc MT (8 * nch)))
  by (apply (mok_station MT Sc S1 T _ _ MTL Hmo Hle1); lia).
assert (Pnev : st_nev S1 < EV_MAX) by exact (hd_nev _ _ _ _ _ _ HJ1' ltac:(lia)).
assert (Plive : blocks_bytes S1 + 8 * nch <= LIVE_MAX) by (rewrite BB; unfold DEC_CRT_LIVE in Hlive; lia).
change CRT_MALLOC with (decode_sigma DS___interceptor_trampoline_malloc). rewrite <- HMPC.
refine (SRr_bind segs W1 _ _ POST
  (AMALLOC fx W1 (ms_regs ms') m1 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] ly1 S1 md' 1
     (8 * nch) (-96) (w64 (CRT_AT 0x70)) [] HJ1' G10' ltac:(unfold MALLOC_MAX; lia) Plive
     (hd_spZ1 _ HK2) eq_refl ltac:(lia) ltac:(unfold DEC_CRT_STK, DEC_CRT_FRAME; lia)
     (proj1 (hd_gptp _ HK2)) (proj2 (hd_gptp _ HK2)) G1 hd_ret70 Pnev Hch2 Htr2 Hmo2) _).
intros W2 c2 Hwle (ly2 & S2 & regs2 & m2 & md2 & Q & -> & HJ2 & HP2 & H10' & Hfr2 & HQ & EB2 & HKEPT & Hle2).
apply (hd_at70 ly2 S2 W2 regs2 m2 md2 P Q).
- exact HJ2.
- rewrite Hfr2. exact Hfr1.
- exact (mle_station MT Sc S1 S2 _ _ MTL Hle1 Hle2).
- exact (hd_frame_call W1 m1 W2 m2 ly1 S1 _ HF1 (hd_win _ _ _ _ _ _ HJ1') (hd_win _ _ _ _ _ _ HJ2) HKEPT).
- exact (hd_rom_call W1 m1 W2 m2 ly1 S1 _ _ _ HR1 HKEPT).
- rewrite EB2, EB1. reflexivity.
- exact HP1.
- exact HQ.
- exact (hd_kept_pres _ _ HK2 HP2).
- kp_by HP2 8 G8.
- exact H10'.
Qed.

(* At CRT_ENTRY: the inner journal, crt_seg1_F (the prologue), then malloc(4 nch ns). *)
Lemma hd_entry : SRr segs W (@cfg_at fx segs CRT_ENTRY regs memc mdc) POST.
Proof.
hd_pre.
pose proof hd_nn as (Hn1 & Hn2 & Hnn). pose proof hd_sp_rng as [Hsp1 Hsp2].
pose proof asan_consts as (C1 & _). pose proof hd_cost as (Mc1 & Mc2 & Mc3 & Msum).
pose proof hd_sp0_16 as H16.
pose proof HJ as HJx. destruct HJx as (HAR & _).
(* 1. the inner journal at the entry *)
assert (JI0 : JI lyc Sc W memc mdc 0).
{ apply (@ajournal_sub_init rc dec_A_sink_head segs B STK sp0 FP ly Se W0 mem0 md0 own lyc Sc W memc mdc k
           DEC_CRT_STK (spZ regs) [] (spZ regs - sp0) HJ);
    [lia | rewrite Zminus_mod, Hal, H16; reflexivity | lia
    | unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK; lia | unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia]. }
pose proof (hd_win _ _ _ _ _ _ JI0) as Hpres0.
pose proof JI0 as JI0x.
destruct JI0x as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47' & _ & _ & Htop') & _).
assert (Haud : 0 <= audio < 2 ^ 64).
{ destruct (al_blocks segs B LAWS lyc Sc W memc mdc bA nA HAR HbA) as (_ & H4 & Hc & _).
  assert (nA <= req_size nA) by (unfold req_size; destruct (Z.eqb_spec nA 0); lia). lia. }
assert (Hpcm : 0 <= pcm < 2 ^ 64).
{ destruct (al_blocks segs B LAWS lyc Sc W memc mdc bP nP HAR HbP) as (_ & H4 & Hc & _).
  assert (nP <= req_size nP) by (unfold req_size; destruct (Z.eqb_spec nP 0); lia). lia. }
assert (E10 : YKK.getr regs (Z_to_bv 5 10) = Z_to_bv 64 audio) by exact H10.
assert (E11 : YKK.getr regs (Z_to_bv 5 11) = Z_to_bv 64 pcm) by exact H11.
assert (E12 : YKK.getr regs (Z_to_bv 5 12) = Z_to_bv 64 nch) by exact H12.
assert (E13 : YKK.getr regs (Z_to_bv 5 13) = Z_to_bv 64 ns) by exact H13.
(* 2. the prologue *)
eapply crtA_run.
{ unfold LCK.ms_of_regs. rewrite E10, E11, E12, E13.
  eapply crt_seg1_F with (audio := audio) (pcm := pcm) (nch := nch) (ns := ns) (lo := spZ regs - DEC_CRT_STK).
  all: try change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs).
  - apply (crtA_stk_present (w_H W)); [unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in *; lia | lia | exact Hpres0].
  - unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK; lia.
  - exact (dec_cells_asan B HCELLS lyc Sc W memc mdc (w_Hoff W) HAR).
  - unfold AsanKA.off_stk. change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs). left.
    crt_val MIDEND. crt_val GOT_CELL_K. unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. lia.
  - exact Hn1.
  - exact Hn2.
  - exact Haud.
  - exact Hpcm.
  - apply crtA_rng_vis; [unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1; lia | lia |].
    intros i Hi.
    assert (Hx : spZ regs - DEC_CRT_STK <= spZ regs - 96 + i < spZ regs)
      by (unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK; lia).
    exact (proj1 (Hpres0 _ Hx)).
  - apply crtA_rng_vis; [crt_val GOT_CELL_K; lia | crt_val GOT_CELL_K; lia |].
    intros i Hi. apply (crt_covers_visible (w_H W) GOT_CELL_K 8 i (w_Hoff W)); [crt_seg | exact Hi | crt_top].
  - apply crtA_rng_vis; [crt_val CELL_K; lia | crt_val CELL_K; lia |].
    intros i Hi. apply (crt_covers_visible (w_H W) CELL_K 8 i (w_Hoff W)); [crt_seg | exact Hi | crt_top]. }
intros ms' md' (ms0 & (m1 & Hms0 & MU & WM & ST1 & FR) & EQV) SBM. subst ms0.
change (bv_unsigned (YKK.getr regs (Z_to_bv 5 2))) with (spZ regs) in MU, FR.
try change (PropExec.seg_rom rsegs) with (YKK.seg_rom decodesegs0) in EQV.
rewrite (crtA_ms_shape _ _ _ _ EQV).
assert (HK1 : hd_kept (ms_regs ms')).
{ unfold hd_kept. repeat match goal with |- _ /\ _ => split end;
    apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity. }
assert (G10 : YKK.getr (ms_regs ms') (Z_to_bv 5 10) = w64 (4 * (nch * ns)))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
assert (G1 : YKK.getr (ms_regs ms') (Z_to_bv 5 1) = w64 (CRT_AT 0x64))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
assert (G8 : YKK.getr (ms_regs ms') (Z_to_bv 5 8) = YKK.getr regs (Z_to_bv 5 8))
  by (apply (crtA_reg_of _ _ _ _ _ _ _ _ _ _ EQV); reflexivity).
(* the inner journal after the frame write *)
assert (HJ1 : JI lyc Sc W m1 md' 0).
{ apply (@ajournal_exec rc dec_A_sink_head segs B LAWS crtA_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md'
           (fun a => spZ regs - 96 <= a < spZ regs) JI0).
  - intros x Hx. unfold mrestrict. rewrite (MU x); [reflexivity|]. cbn [outside]. split; [exact Hx | exact I].
  - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 96)) as [Hl|Hl];
      [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
    assert (Hw : wview rsegs m1 x <> None).
    { refine (WM x _). unfold wview. destruct (memc x) as [b|] eqn:Em;
        [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
    unfold wview in Hw. destruct (m1 x) as [b|] eqn:Em1; [discriminate|]. try rewrite Em1 in Hw. exfalso.
    rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
    intros Him. pose proof (crtA_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow.
    unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. lia.
  - intros x Hx.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 96)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|apply (MU x); cbn [outside]; split; [lia | exact I]].
    exfalso.
    assert (Hxr : spZ regs - DEC_CRT_STK <= bv_unsigned x < spZ regs)
      by (unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK; lia).
    pose proof (proj1 (Hpres0 _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
  - exact SBM.
  - intros a Ha. cbv beta in Ha. left. unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK. lia. }
(* the scoped read-only view after the run: the run writes only the frame *)
assert (HR1 : crtA_rom_on RO_RD W m1).
{ intros a Hin Ha. rewrite <- (Hrom a Hin Ha). apply aview_eq_of. unfold mrestrict.
  pose proof (crtA_segs_low a (crtA_rom_img a Ha)) as Hlow. unfold kLowMemEnd in Hlow.
  rewrite (MU (Z_to_bv 64 a)); [reflexivity|]. cbn [outside]. rewrite unsigned_lit by lia.
  unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. split; [lia | exact I]. }
assert (HF1 : crtA_frame regs m1) by exact FR.
(* 3. malloc(4 nch ns): the entry chain, read at the new memory *)
assert (Hch1 : chain_pre lyc (aview segs (w_H W) m1) (ms_regs ms') ch).
{ apply (achain_chain_pre lyc _ (spZ regs) (s0Z regs) ch (ms_regs ms')).
  - apply (achain_kept lyc (aview segs (w_H W) memc) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. apply F1; lia.
  - rewrite (hd_spZ1 _ HK1). unfold DEC_CRT_STK, DEC_CRT_FRAME, ASTACK in Hsp1. lia.
  - change (s0Z (ms_regs ms')) with (bv_unsigned (YKK.getr (ms_regs ms') (Z_to_bv 5 8))). rewrite G8. reflexivity.
  - rewrite (hd_raZ _ _ G1) by lia. crt_val (CRT_AT 0x64). lia. }
assert (Htr1 : In (call_trace0 (pc_malloc_ra0 (as_code B)) (ms_regs ms') ch) (as_universe B)).
{ rewrite crtA_trace0, (hd_raZ _ _ G1) by lia. exact Htm. }
assert (Hmo1 : mo_ok MT Sc (mo_malloc MT (4 * (nch * ns)))) by (apply (mo_ok_le MT MTL Sc _ T Hmo); lia).
assert (Pnev : st_nev Sc < EV_MAX) by exact (hd_nev _ _ _ _ _ _ HJ1 ltac:(lia)).
assert (Plive : blocks_bytes Sc + 4 * (nch * ns) <= LIVE_MAX) by (unfold DEC_CRT_LIVE in Hlive; lia).
change CRT_MALLOC with (decode_sigma DS___interceptor_trampoline_malloc). rewrite <- HMPC.
refine (SRr_bind segs W _ _ POST
  (AMALLOC fx W (ms_regs ms') m1 DEC_CRT_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc md' 0
     (4 * (nch * ns)) (-96) (w64 (CRT_AT 0x64)) ch HJ1 G10 ltac:(unfold MALLOC_MAX; lia) Plive
     (hd_spZ1 _ HK1) eq_refl ltac:(lia) ltac:(unfold DEC_CRT_STK, DEC_CRT_FRAME; lia)
     (proj1 (hd_gptp _ HK1)) (proj2 (hd_gptp _ HK1)) G1 hd_ret64 Pnev Hch1 Htr1 Hmo1) _).
intros W2 c2 Hwle (ly2 & S2 & regs2 & m2 & md2 & P & -> & HJ2 & HP2 & H10' & Hfr2 & HP4 & EB & HKEPT & Hle1).
apply (hd_at64 ly2 S2 W2 regs2 m2 md2 P).
- exact HJ2.
- exact Hfr2.
- exact Hle1.
- exact (hd_frame_call W m1 W2 m2 lyc Sc _ HF1 (hd_win _ _ _ _ _ _ HJ1) (hd_win _ _ _ _ _ _ HJ2) HKEPT).
- exact (hd_rom_call W m1 W2 m2 lyc Sc _ _ _ HR1 HKEPT).
- exact EB.
- exact HP4.
- exact (hd_kept_pres _ _ HK1 HP2).
- exact H10'.
Qed.
End Entry.

(* The entry piece: from CRT_ENTRY to the cut crtA_at_calloc. *)
Theorem crtA_head : crtA_at_calloc B MT RO_RD ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch,
    crtA_pre B MT RO_RD STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch ->
    frm_zero (@fp_csr fx) ->
    ly_bot lyc + DEC_CALLOC_DEPTH + DEC_CRT_FRAME < spZ regs ->
    SRr segs W (@cfg_at fx segs CRT_ENTRY regs memc mdc)
      (dec_crt_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs nch ns).
Proof.
intros CUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs audio pcm nch ns bA nA bP nP T ch HPRE HFRM
  HDEPTH.
eapply hd_entry; eassumption.
Qed.
End Head.
