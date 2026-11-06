(* check_state_data_cgW: the caller-journal walk of check_state_data in image B (fuzz_transport.asan-ubsan, entry
   0x857cc = transportb_sigma TB_check_state_data), and the theorem of lib/B/Prog/check_state_data_cg.v. Image A's
   twin is lib/A/Prog/check_state_data_cgW.v: the same walk at image B's names (TMAP_B, TB_OW, transportb_sigma,
   lib/B/Prog/DgnTransportBCg.v, DgnTransportBCgRun.v); image B's extra branches (the alignment test of p and the
   pointer tests of &OW.dn[g]) are closed inside the runs of lib/B/Prog/check_state_data_seg_run.v.

   The walk, from the contract's premises:
     1. an INNER journal at the entry state (YCbq.v ajournal_sub_init; stack window
        [spZ regs - CSDATA_STK, spZ regs), no footprint, no frame of its own);
     2. the premises are read as the inputs of the two footprint runs of lib/B/Prog/check_state_data_seg_run.v: the
        72 bytes of the notice at p (garr8 at the visible bytes of its read range), the shadow byte 0 of every
        granule inside them, the world relation at the machine's view of raw memory, the shadow byte 0 of OW's
        granules (the record's zero-shadow row, trans_csdata_cells), and the two runtime cells of the shadow base
        (DgnTransportBCgRun.v decode_cells_asan);
     3. each run is carried into SRr by DgnTransportBCgRun.v decode_run, and the inner journal is re-established
        across it by YCbq.v ajournal_exec (the run writes only the 32 bytes of its own frame, which lie in the
        journal's stack window);
     4. the bcmp call is cut by YCbq.v aj_bcmp_at at the statement's abcmp_realizes premise: the compared ranges
        are the notice's body and OW.dn[g].body, both outside the call's 2 * ESTACK window (decode_off_win), and
        the answer is 0 because the model's beq_bytes makes the two ranges agree byte for byte;
     5. the inner journal and the caller's compose by YC85.v ajournal_sub_tok, the kept bytes are YCbq.v
        acall_kept_of_journal of the inner journal (no footprint, no written range), the meter is unchanged
        (YC5d.v mle_start), the frames and the blocks are the call state's, and the post's world fact is the
        model's Bw' = Bw. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun YC85.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB check_state_wake_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_data_seg_run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TImg.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.LeafCgKit.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TWm := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWLm := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TCm := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TIm := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module DSp := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

(* ---- the model's Some, read as the facts the walk needs (lib/TModel/TCb.v check_state_data_m) ---- *)

Lemma csw_m_some : forall Fr B0 nn B1,
  TCm.check_state_data_m Fr B0 nn = Some (B1, tt) ->
  B1 = B0 /\ TWm.GOT_ndata B0 < TWm.OW_ndata B0 /\ 0 <= TWm.GOT_ndata B0 < 2 /\
  TIm.n_body_len nn = TCm.OW_dn_len B0 (TWm.GOT_ndata B0) /\
  TIm.n_body_len nn <= Z.of_nat (length (TIm.n_body nn)) /\
  TIm.n_counter nn = TCm.OW_dn_counter B0 (TWm.GOT_ndata B0) /\
  TIm.n_retry nn = TCm.OW_dn_retry B0 (TWm.GOT_ndata B0) /\
  exists db, TCm.frame_read Fr (TCm.OW_dn_body B0 (TWm.GOT_ndata B0)) (TIm.n_body_len nn) = Some db /\
             TWm.zs (firstn (Z.to_nat (TIm.n_body_len nn)) (TIm.n_body nn)) = TWm.zs db.
Proof.
  intros Fr B0 nn B1 H. unfold TCm.check_state_data_m in H. cbv zeta in H. revert H.
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E1 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E2 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E3 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (match ?x with Some _ => _ | None => None end) = _ -> _ => destruct x as [db|] eqn:E4 end;
    cbv beta iota; [|intros HH; discriminate HH].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E5 end;
    cbv beta iota; [intros HH; discriminate HH|].
  lazymatch goal with |- (if ?c then None else _) = _ -> _ => destruct c eqn:E6 end;
    cbv beta iota; [intros HH; discriminate HH|].
  intros H. injection H as HB.
  apply orb_false_iff in E1. destruct E1 as [E1a E1b]. apply Z.leb_gt in E1a. apply Z.leb_gt in E1b.
  apply Z.ltb_ge in E2. apply negb_false_iff in E3. apply Z.eqb_eq in E3. apply Z.ltb_ge in E5.
  apply orb_false_iff in E6. destruct E6 as [E6 E6c]. apply orb_false_iff in E6. destruct E6 as [E6a E6b].
  apply negb_false_iff in E6a. apply negb_false_iff in E6b. apply negb_false_iff in E6c.
  apply Z.eqb_eq in E6b. apply Z.eqb_eq in E6c.
  unfold TCm.beq_bytes in E6a. destruct (list_eq_dec Z.eq_dec _ _) as [Ez|Ez]; [|discriminate E6a].
  split; [symmetry; exact HB|]. split; [lia|]. split; [lia|]. split; [exact E3|]. split; [lia|].
  split; [exact E6b|]. split; [exact E6c|]. exists db. split; [first [exact E4 | reflexivity] | exact Ez].
Qed.

(* With no current heap frame, only the empty read of the model succeeds. *)
Lemma csw_frame_none : forall q len db, TCm.frame_read None q len = Some db -> db = [] /\ len = 0.
Proof.
  intros q len db HR. unfold TCm.frame_read in HR. revert HR.
  destruct (len =? 0) eqn:E0; intros HR; [|discriminate HR].
  apply Z.eqb_eq in E0. injection HR as <-. split; [reflexivity | exact E0].
Qed.

(* What the model read out of the current heap frame is a slice of that frame's bytes. *)
Lemma csw_frame_some : forall fr q len db, TCm.frame_read (Some fr) q len = Some db -> 0 < len ->
  0 <= q - TIm.tf_addr fr /\ q - TIm.tf_addr fr + len <= Z.of_nat (length (TIm.tf_bytes fr)) /\
  db = TWm.sub (TIm.tf_bytes fr) (q - TIm.tf_addr fr) (Z.to_nat len).
Proof.
  intros fr q len db HR Hl. unfold TCm.frame_read in HR. revert HR.
  replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  destruct ((q - TIm.tf_addr fr <? 0) || (len <? 0) ||
            (Z.of_nat (length (TIm.tf_bytes fr)) <? q - TIm.tf_addr fr + len))%bool eqn:E; intros HR;
    [discriminate HR|].
  injection HR as <-.
  apply orb_false_iff in E. destruct E as [E E3]. apply orb_false_iff in E. destruct E as [E1 _].
  apply Z.ltb_ge in E1. apply Z.ltb_ge in E3.
  split; [lia|]. split; [lia | reflexivity].
Qed.

(* The i-th byte of the model's byte list, as a value. *)
Lemma csw_nth_map_bz : forall (l : list byte) i, (i < length l)%nat ->
  nth i (map DSp.bz l) 0 = DSp.bz (nth i l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [map nth length] in *. apply IH. lia.
Qed.

Lemma csw_b8_bz : forall b : byte, Z_to_bv 8 (YO0f.le_byte (DSp.bz b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N 8) with 256 in Hbr. unfold YO0f.le_byte, DSp.bz.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma csw_bz_range : forall b : byte, 0 <= DSp.bz b < 256.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. unfold DSp.bz. exact R.
Qed.

(* The bytes of a list, read through the overlay at visible addresses, as the raw memory of the runs. *)
Lemma csw_bytes_of_garr : forall (W : world tfibsegs) mem A (L : list byte),
  0 <= A -> A + Z.of_nat (length L) <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat (length L) -> w_H W (Z_to_bv 64 a) = false) ->
  garr8 tfibsegs (mrestrict (w_H W) mem) A (map DSp.bz L) ->
  bytes_at rsegs mem A L.
Proof.
  intros W mem A L H0 H1 HV HG.
  split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  assert (Hi' : (i < length (map DSp.bz L))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [HV1 _].
  specialize (HV1 0%nat ltac:(lia)). rewrite Z.add_0_r in HV1.
  assert (Hv : w_H W (Z_to_bv 64 (A + Z.of_nat i)) = false) by (apply HV; lia).
  assert (Em : mrd rsegs mem (wa (A + Z.of_nat i)) = YP09.mbyte tfibsegs (mrestrict (w_H W) mem) (A + Z.of_nat i))
    by (unfold mrd, wa, YP09.mbyte, mrestrict; rewrite Hv; reflexivity).
  rewrite Em, HV1, (nth_error_nth' L (Z_to_bv 8 0) Hi), (csw_nth_map_bz L i Hi).
  f_equal. apply csw_b8_bz.
Qed.

(* A byte of such a range, as the overlay reads it. *)
Lemma csw_garr_view : forall (W : world tfibsegs) mem A (L : list byte) i,
  (i < length L)%nat -> garr8 tfibsegs (mrestrict (w_H W) mem) A (map DSp.bz L) ->
  aview tfibsegs (w_H W) mem (A + Z.of_nat i) = Some (DSp.bz (nth i L (Z_to_bv 8 0))).
Proof.
  intros W mem A L i Hi HG.
  assert (Hi' : (i < length (map DSp.bz L))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [HV1 _].
  specialize (HV1 0%nat ltac:(lia)). rewrite Z.add_0_r in HV1.
  rewrite (csw_nth_map_bz L i Hi) in HV1.
  unfold aview. rewrite HV1. cbn [option_map].
  pose proof (csw_bz_range (nth i L (Z_to_bv 8 0))) as Hr.
  f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256) by lia. reflexivity.
Qed.

(* nth_error through firstn and through the model's sub. *)
Lemma csw_nth_error_firstn : forall {X} (l : list X) n i, (i < n)%nat ->
  nth_error (firstn n l) i = nth_error l i.
Proof.
  intros X l. induction l as [|a l IH]; intros n i Hi.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. cbn [firstn]. destruct i as [|i]; [reflexivity|].
    cbn [nth_error]. apply IH. lia.
Qed.

Lemma csw_nth_sub : forall (l : list byte) k n i, 0 <= k -> (i < n)%nat ->
  nth_error (TWm.sub l k n) i = nth_error l (Z.to_nat k + i).
Proof.
  intros l k n i Hk Hi. unfold TWm.sub. rewrite csw_nth_error_firstn by exact Hi.
  apply TWLm.nth_skipn.
Qed.

Lemma csw_nth_of_error : forall {X} (l : list X) i (b d : X), nth_error l i = Some b -> nth i l d = b.
Proof.
  intros X l. induction l as [|a l IH]; intros i b d H; [destruct i; discriminate|].
  destruct i as [|i]; cbn [nth_error nth] in *; [injection H as <-; reflexivity | exact (IH i b d H)].
Qed.

(* Every byte of a payload of the world is visible: it lies in a loaded segment of the image. *)
Lemma csw_tw_vis : forall (W : world tfibsegs) x, tw_in TMAP_B x -> w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x (o & b & nn & Hin & Hx). apply decode_vis_seg. apply (trans_g_img x).
  unfold W_journalG.inG. apply Exists_exists. exists (b, nn).
  split; [exact (TMAP_B_in_G o b nn Hin)|]. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* The statement's world relation, at the machine's view of raw memory. *)
Lemma csw_tw_mrd : forall (W : world tfibsegs) mem Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) mem) Bw -> tw_at TMAP_B (csw_view mem) Bw.
Proof.
  intros W mem Bw H. apply (tw_kept TMAP_B (aview tfibsegs (w_H W) mem) (csw_view mem) Bw H).
  intros x Hx. unfold csw_view. symmetry. exact (decode_aview_mrd W mem x (csw_tw_vis W x Hx)).
Qed.

(* Two memories that agree under the overlay at a visible byte agree under mrd. *)
Lemma csw_mrd_of_aview : forall (W : world tfibsegs) m m' a,
  w_H W (Z_to_bv 64 a) = false ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof.
  intros W m m' a Hv E.
  rewrite (decode_aview_mrd W m' a Hv), (decode_aview_mrd W m a Hv) in E.
  destruct (mrd rsegs m' (wa a)) as [b1|]; destruct (mrd rsegs m (wa a)) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* bytes_at at a later memory that agrees on the range's bytes. *)
Lemma csw_bytes_keep : forall m m' A (L : list byte),
  (forall i, (i < length L)%nat -> mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))) ->
  bytes_at rsegs m A L -> bytes_at rsegs m' A L.
Proof.
  intros m m' A L E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (E i Hi). exact (H i Hi).
Qed.

(* Present bytes make a writable stack range (lib/Lib/Frame.v stk). *)
Lemma csw_stk_present : forall (H : word -> bool) m lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> apresent H m a) -> stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 Hp. split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (Hp a Ha) as [_ [b Hb]]. unfold wa. split.
  - unfold wview. rewrite Hb. discriminate.
  - exists b. unfold mrd. rewrite Hb. reflexivity.
Qed.

(* The shadow byte of a granule inside a read range is 0: the byte at offset 7 of the granule lies in the range,
   and saddr_ok of a byte at offset 7 leaves only the shadow value 0. *)
Lemma csw_shadow_zero : forall (W : world tfibsegs) mem q nn x,
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF q nn -> q <= x -> x + 8 <= q + nn ->
  w_H W (Z_to_bv 64 (x / 8 + ACells.ASAN_K)) = false /\
  mrd rsegs mem (wa (x / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0).
Proof.
  intros W mem q nn x Hra H1 H2.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
  destruct (Hra (8 * (x / 8) + 7) ltac:(lia)) as (s & Hs & Hok).
  assert (Ediv : (8 * (x / 8) + 7) / 8 = x / 8).
  { replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.div_add by lia.
    rewrite (Z.div_small 7 8) by lia. lia. }
  assert (Emod : (8 * (x / 8) + 7) mod 8 = 7).
  { replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.mod_add by lia.
    apply Z.mod_small. lia. }
  assert (Es : s = 0) by (unfold saddr_ok in Hok; rewrite Emod in Hok; lia).
  assert (Ea : shadow_of_addr SHADOW_OFF (8 * (x / 8) + 7) = x / 8 + ACells.ASAN_K).
  { unfold shadow_of_addr, SHADOW_OFF, ACells.ASAN_K. rewrite Ediv. lia. }
  rewrite Ea, Es in Hs.
  destruct (decode_aview_some W mem _ 0 Hs) as (Hvis & b & Hb & Eb).
  split; [exact Hvis|]. rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Eb. reflexivity.
Qed.

(* The shadow byte of a granule of OW's payload is 0: the record's zero-shadow row (trans_csdata_cells). *)
Lemma csw_zsh {rc : YM05.RunCeil} : forall (B : asyms) ly' S' (W' : world tfibsegs) mem md T,
  trans_csdata_cells B ->
  @AR rc tfibsegs B ly' S' W' mem md -> T mod 8 = 0 -> TB_OW <= T -> T + 8 <= TB_OW + TWm.SZ_OW ->
  w_H W' (Z_to_bv 64 (T / 8 + ACells.ASAN_K)) = false /\
  mrd rsegs mem (wa (T / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0).
Proof.
  intros B ly' S' W' mem md T HCSD HAR H8 H1 H2.
  pose proof (decode_zshadow_rd B ly' S' W' mem md TB_OW (TB_OW + TWm.SZ_OW) T HAR H8 H1 H2 HCSD) as Hv.
  destruct (decode_aview_some W' mem _ 0 Hv) as (Hvis & b & Hb & Eb).
  replace (T / 8 + ACells.ASAN_K) with (ACells.shadow_addr T) by (unfold ACells.shadow_addr; reflexivity).
  split; [exact Hvis|]. rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Eb. reflexivity.
Qed.

(* Where a read range lies: the bounds and the application-memory range the bcmp contract needs. The heap-block
   case of an EMPTY range is the one trans_src_ok_rd does not cover (it needs 0 < n). *)
Lemma csw_src_bnd {rc : YM05.RunCeil} : forall (B : asyms), AR_laws tfibsegs B ->
  forall lyc' Sc' (W' : world tfibsegs) mem mdc' q nn,
  @AR rc tfibsegs B lyc' Sc' W' mem mdc' -> trans_src_ok B lyc' Sc' W' mem q nn -> 0 <= nn ->
  0 <= q /\ q + nn <= 2 ^ 63 /\ amem_range q nn.
Proof.
  intros B LAWS lyc' Sc' W' mem mdc' q nn HAR HS Hn.
  destruct (Z.eq_dec nn 0) as [->|Hne].
  - destruct HS as [(bA & nA & Hin & H1 & H2) | (_ & Hrd)].
    + destruct (al_blocks _ _ LAWS lyc' Sc' W' mem mdc' bA nA HAR Hin) as (_ & H4096 & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      pose proof (amem_range_of_block tfibsegs B LAWS lyc' Sc' W' mem mdc' bA nA q 0 HAR Hin
        ltac:(lia) ltac:(lia)) as HM.
      pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
      unfold amem_range in HM. split; [lia|]. split; [unfold kLowMemEnd, kHighMemEnd in *; lia|]. exact HM.
    + destruct Hrd as (_ & _ & _ & Hm & H0 & H63). split; [exact H0|]. split; [exact H63 | exact Hm].
  - pose proof (trans_src_ok_rd B LAWS lyc' Sc' W' mem mdc' q nn HAR HS ltac:(lia))
      as (_ & _ & _ & Hm & H0 & H63).
    split; [exact H0|]. split; [exact H63 | exact Hm].
Qed.

(* ---- the theorem ---- *)

(* The registers the epilogue restores (callee-saved from the frame and the kept ones) are the caller's. *)
Lemma csw_pres_ret {fx : YKK.FPState} : forall (regs : bvmap 5 word)
    (spx r10 r11 r12 r13 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  bv_unsigned spx = spZ regs ->
  aregs_preserved regs
    (mkR (YKK.getr regs 1) spx (YKK.getr regs 3) (YKK.getr regs 4) x5 x6 x7
         (YKK.getr regs 8) (YKK.getr regs 9) r10 r11 r12 r13 x14 x15 x16 x17
         (YKK.getr regs 18) (YKK.getr regs 19) (YKK.getr regs 20) (YKK.getr regs 21)
         (YKK.getr regs 22) (YKK.getr regs 23) (YKK.getr regs 24) (YKK.getr regs 25)
         (YKK.getr regs 26) (YKK.getr regs 27) x28 x29 x30 x31).
Proof.
  intros regs spx r10 r11 r12 r13 x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 Hsp r Hr.
  unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r; try reflexivity.
  apply bv_eq. exact Hsp.
Qed.

(* Lift register preservation through ms_eqv. *)
Lemma csw_pres_eqv {fx : YKK.FPState} : forall (regs R F : bvmap 5 word) pc fc rv m ro ms',
  ms_eqv (MS R F pc fc rv m ro) ms' -> aregs_preserved regs R -> aregs_preserved regs (ms_regs ms').
Proof.
  intros regs R F pc fc rv m ro ms' EQV HP r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst r;
    (rewrite (decode_ms_reg R F pc fc rv m ro ms' _ EQV) by reflexivity);
    apply HP; unfold acallee_saved; lia.
Qed.

Theorem transport_check_state_data_cg_holds {fx : YKK.FPState} {rc : YM05.RunCeil}
    (B : asyms) (MT : ameter_ops) : @transport_check_state_data_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HCSD LAWS MTL ABCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 HAL HWLO HWHI HNTC HTFR HWORLD HMODEL HSRCB HOFFB HBL32 HNEV.
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  (* ---- what the journal says ---- *)
  assert (HAR : AR tfibsegs B lyc Sc W memc mdc) by (destruct HJ as (H & _); exact H).
  assert (HSTK : astk_ok STK ly sp0)
    by (destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
  assert (HPRES : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a)
    by (destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _); exact H).
  assert (HSPR : YM05.alloc_ceiling + CSDATA_STK <= spZ regs /\ spZ regs <= 2 ^ 47)
    by (destruct HSTK as (H16 & Hstk0 & Hceil & Hlo & Hhi & H47 & _); lia).
  destruct HSPR as [SP1 SP2].
  unfold CSDATA_STK, CSDATA_FRAME, ESTACK in SP1, HWLO.
  (* ---- the model ---- *)
  destruct (csw_m_some Fr Bw n Bw' HMODEL) as (EBw & MLT & MG & MLEN & MBODY & MCNT & MRTY & db & MDB & MZS).
  unfold TCm.OW_dn_len, TCm.A_OW_dn_len, TCm.OW_dn_counter, TCm.A_OW_dn_counter,
    TCm.OW_dn_retry, TCm.A_OW_dn_retry in MLEN, MCNT, MRTY.
  (* ---- the notice ---- *)
  destruct HNTC as (HP0 & HP8 & HSRCP & HOFFP & NB & GNB & LNB & _ & _ & _ & _ & _ & _ & E56 & E64 & E68
                    & GBODY & SBODY & OBODY & _).
  unfold decode_off_win, NTC_SIZE in HOFFP.
  pose proof (trans_src_ok_rd B LAWS lyc Sc W memc mdc p NTC_SIZE HAR HSRCP ltac:(unfold NTC_SIZE; lia))
    as RDP.
  destruct RDP as (RPv & RPa & RPh & RPm & RP0 & RP63).
  unfold NTC_SIZE in RPv, RPa, RPh, RPm, RP63.
  assert (HPHI : p + 72 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemEnd in RPm; lia).
  (* the 72 bytes of the notice, as raw memory *)
  assert (VISP : forall a, p <= a < p + Z.of_nat (length NB) -> w_H W (Z_to_bv 64 a) = false).
  { intros a Ha. destruct (aview tfibsegs (w_H W) memc a) as [v|] eqn:Ev;
      [exact (decode_aview_vis W memc a v Ev) | exfalso; apply (RPv a ltac:(lia)); exact Ev]. }
  assert (BNB : bytes_at rsegs memc p NB)
    by (apply (csw_bytes_of_garr W memc p NB ltac:(lia) ltac:(rewrite LNB; lia) VISP GNB)).
  (* ---- the world and the runtime cells ---- *)
  assert (HW : tw_at TMAP_B (csw_view memc) Bw) by exact (csw_tw_mrd W memc Bw HWORLD).
  assert (HCELLSM : ACells.asan_cells memc)
    by exact (decode_cells_asan B HCELLS lyc Sc W memc mdc (@w_Hoff tfibsegs W) HAR).
  destruct HCELLSM as (BCELL & BGOTC & _).
  (* ---- the shadow bytes ---- *)
  destruct (csw_shadow_zero W memc p 72 (p + 48) RPa ltac:(lia) ltac:(lia)) as [VS48 SH48].
  destruct (csw_shadow_zero W memc p 72 (p + 56) RPa ltac:(lia) ltac:(lia)) as [VS56 SH56].
  destruct (csw_shadow_zero W memc p 72 (p + 64) RPa ltac:(lia) ltac:(lia)) as [VS64 SH64].
  destruct (csw_zsh B lyc Sc W memc mdc (TB_OW + (256 + 24 * TWm.GOT_ndata Bw)) HCSD HAR
    ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW, TWm.SZ_OW; lia)) as [VSDB SHDB].
  destruct (csw_zsh B lyc Sc W memc mdc (TB_OW + (256 + 24 * TWm.GOT_ndata Bw) + 8) HCSD HAR
    ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW, TWm.SZ_OW; lia)) as [VSDL SHDL].
  destruct (csw_zsh B lyc Sc W memc mdc (TB_OW + (256 + 24 * TWm.GOT_ndata Bw) + 16) HCSD HAR
    ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW; lia) ltac:(unfold TB_OW, TWm.SZ_OW; lia)) as [VSDC SHDC].
  (* ---- the footprint ---- *)
  assert (RNGFR : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (spZ regs + -32) 32).
  { apply (decode_rng W); [lia | lia|]. intros b Hb. exact (proj1 (HPRES b ltac:(lia))). }
  assert (RNGGOTC : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) ACells.GOT_CELL_K 8).
  { apply (decode_rng W); [unfold ACells.GOT_CELL_K; lia | unfold ACells.GOT_CELL_K; lia|].
    intros b Hb. apply decode_vis_seg.
    apply (decode_covers_img ACells.GOT_CELL_K 8 b); [vm_compute; reflexivity | exact Hb]. }
  assert (RNGCELL : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) ACells.CELL_K 8).
  { apply (decode_rng W); [unfold ACells.CELL_K; lia | unfold ACells.CELL_K; lia|].
    intros b Hb. apply decode_vis_seg.
    apply (decode_covers_img ACells.CELL_K 8 b); [vm_compute; reflexivity | exact Hb]. }
  assert (VISG : forall b nn' a, In (b, nn') TransportGB.G_HARNESS_B -> b <= a < b + nn' ->
                 w_H W (Z_to_bv 64 a) = false).
  { intros b nn' a Hin Ha. apply decode_vis_seg. apply (trans_g_img a).
    unfold W_journalG.inG. apply Exists_exists. exists (b, nn').
    split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia. }
  assert (RNGGOT : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) (TB_GOT + 220) 4).
  { apply (decode_rng W); [unfold TB_GOT; lia | unfold TB_GOT; lia|].
    intros b Hb. apply (VISG TB_GOT TWm.SZ_GOT b);
      [exact (TMAP_B_in_G TWm.OFF_GOT TB_GOT TWm.SZ_GOT TMAP_B_GOT) | unfold TWm.SZ_GOT; lia]. }
  assert (RNGOW : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) TB_OW 304).
  { apply (decode_rng W); [unfold TB_OW; lia | unfold TB_OW; lia|].
    intros b Hb. apply (VISG TB_OW TWm.SZ_OW b);
      [exact (TMAP_B_in_G TWm.OFF_OW TB_OW TWm.SZ_OW TMAP_B_OW) | unfold TWm.SZ_OW; lia]. }
  assert (RNGP : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) p 72).
  { apply (decode_rng W); [lia | lia|]. intros b Hb. apply VISP. rewrite LNB. lia. }
  assert (RNG1 : forall a, w_H W (Z_to_bv 64 a) = false -> 0 <= a -> a + 1 <= 2 ^ 64 ->
                 ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) a 1).
  { intros a Hv H0 H1. apply (decode_rng W); [lia | lia|]. intros b Hb.
    replace b with a by lia. exact Hv. }
  assert (SHB1 : forall x, 0 <= x < 2 ^ 47 -> 0 <= x / 8 + ACells.ASAN_K /\
                 x / 8 + ACells.ASAN_K + 1 <= 2 ^ 64 /\ x / 8 + ACells.ASAN_K + 1 <= 0x10007fff8000).
  { intros x Hx. unfold ACells.ASAN_K. assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos x 8 ltac:(lia)). lia. }
  assert (RS48 : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) ((p + 48) / 8 + ACells.ASAN_K) 1)
    by (destruct (SHB1 (p + 48) ltac:(lia)) as (Q1 & Q2 & _); exact (RNG1 _ VS48 Q1 Q2)).
  assert (RS56 : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) ((p + 56) / 8 + ACells.ASAN_K) 1)
    by (destruct (SHB1 (p + 56) ltac:(lia)) as (Q1 & Q2 & _); exact (RNG1 _ VS56 Q1 Q2)).
  assert (RS64 : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) ((p + 64) / 8 + ACells.ASAN_K) 1)
    by (destruct (SHB1 (p + 64) ltac:(lia)) as (Q1 & Q2 & _); exact (RNG1 _ VS64 Q1 Q2)).
  assert (RSDB : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W)
                   ((TB_OW + (256 + 24 * TWm.GOT_ndata Bw)) / 8 + ACells.ASAN_K) 1)
    by (destruct (SHB1 (TB_OW + (256 + 24 * TWm.GOT_ndata Bw)) ltac:(unfold TB_OW; lia)) as (Q1 & Q2 & _);
        exact (RNG1 _ VSDB Q1 Q2)).
  assert (RSDL : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W)
                   ((TB_OW + (256 + 24 * TWm.GOT_ndata Bw) + 8) / 8 + ACells.ASAN_K) 1)
    by (destruct (SHB1 (TB_OW + (256 + 24 * TWm.GOT_ndata Bw) + 8) ltac:(unfold TB_OW; lia)) as (Q1 & Q2 & _);
        exact (RNG1 _ VSDL Q1 Q2)).
  assert (RSDC : ExecF.rng (LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W)
                   ((TB_OW + (256 + 24 * TWm.GOT_ndata Bw) + 16) / 8 + ACells.ASAN_K) 1)
    by (destruct (SHB1 (TB_OW + (256 + 24 * TWm.GOT_ndata Bw) + 16) ltac:(unfold TB_OW; lia)) as (Q1 & Q2 & _);
        exact (RNG1 _ VSDC Q1 Q2)).
  (* ---- the stack ---- *)
  assert (STKC : stk rsegs memc (spZ regs - 32) (spZ regs))
    by (apply (csw_stk_present (w_H W)); [lia | lia|]; intros a Ha; apply HPRES; lia).
  (* ---- the inner journal ---- *)
  assert (JIN : @ajournal rc YE2k.tfib_sink_head tfibsegs B CSDATA_STK (spZ regs) [] lyc Sc W memc mdc
                  [] lyc Sc W memc mdc 0).
  { destruct HSTK as (Hal16 & _).
    apply (@ajournal_sub_init rc YE2k.tfib_sink_head tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
             CSDATA_STK (spZ regs) [] (spZ regs - sp0) HJ);
      [lia | rewrite Zminus_mod, HAL, Hal16; reflexivity | lia
      | unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia | unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia]. }
  (* the inner journal across one footprint run that writes only the frame *)
  assert (JEXEC : forall (mem1 mem2 : word -> option byte) (md1 md2 : Model),
    @ajournal rc YE2k.tfib_sink_head tfibsegs B CSDATA_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
    munch [(spZ regs + -32, spZ regs)] mem1 mem2 -> wmono rsegs mem1 mem2 ->
    same_but_materialized md1 md2 ->
    @ajournal rc YE2k.tfib_sink_head tfibsegs B CSDATA_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0).
  { intros mem1 mem2 md1 md2 JI MU WM SBM.
    apply (@ajournal_exec rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             mem2 md2 (fun a => spZ regs + -32 <= a < spZ regs) JI).
    - intros x Hx. unfold mrestrict. destruct (w_H W x) eqn:Eh; [reflexivity|].
      apply MU. cbn [outside]. split; [lia | exact I].
    - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -32)) as [Hl|Hl];
        [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
        [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
      assert (Hw : wview rsegs mem2 x <> None).
      { refine (WM x _). unfold wview. destruct (mem1 x) as [b|] eqn:Em;
          [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
      unfold wview in Hw. destruct (mem2 x) as [b|] eqn:Em1; [discriminate|]. exfalso.
      rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
      intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia.
    - intros x Hh.
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs + -32)) as [Hl|Hl];
        [apply (MU x); cbn [outside]; split; [lia | exact I]|].
      destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh2|Hh2];
        [|apply (MU x); cbn [outside]; split; [lia | exact I]].
      exfalso.
      assert (Hxr : sp0 - STK <= bv_unsigned x < sp0) by lia.
      pose proof (proj1 (HPRES _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
    - exact SBM.
    - intros a Ha. cbv beta in Ha. left. unfold CSDATA_STK, CSDATA_FRAME, ESTACK. lia. }
  (* ---- the first run ---- *)
  assert (GRET : ret_pc (YKK.getr regs (Z_to_bv 5 1)) = YKK.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (G10 : YKK.getr regs (Z_to_bv 5 10) = w64 p) by exact H10.
  assert (HGD : (TWm.GOT_ndata Bw = 0 /\ 256 + 24 * TWm.GOT_ndata Bw = 256) \/
                (TWm.GOT_ndata Bw = 1 /\ 256 + 24 * TWm.GOT_ndata Bw = 280)) by lia.
  assert (ESP2 : bv_unsigned (YKK.getr regs (Z_to_bv 5 2)) = spZ regs) by reflexivity.
  eapply decode_run.
  { unfold LCK.ms_of_regs. rewrite G10.
    eapply (csd_run_call_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memc
              _ p (TWm.GOT_ndata Bw) (256 + 24 * TWm.GOT_ndata Bw) (TWm.OW_ndata Bw) NB Bw HGD);
      [ lia | exact HP8 | lia | exact LNB
      | rewrite ESP2; lia
      | rewrite ESP2; lia
      | exact STKC
      | rewrite ESP2; lia
      | rewrite ESP2; unfold CSDATA_STK, CSDATA_FRAME, ESTACK in HOFFP |- *; lia
      | exact HW | reflexivity | reflexivity | lia
      | rewrite E56; rewrite MLEN; f_equal; lia
      | exact BGOTC | exact BCELL | exact BNB
      | exact SH48 | exact SH56 | exact SHDB | exact SHDL
      | exact RNGFR | exact RNGGOTC | exact RNGCELL | exact RNGGOT | exact RNGOW | exact RNGP
      | exact RS48 | exact RS56 | exact RSDB | exact RSDL ]. }
  intros msT mdT (ms0 & (m1 & r13 & r14 & -> & MU1 & WM1 & ST1 & FR1) & EQVT) SBMT.
  rewrite (decode_ms_shape _ _ _ _ EQVT).
  pose proof (JEXEC memc m1 mdc mdT JIN MU1 WM1 SBMT) as JI1.
  (* ---- the bcmp call ---- *)
  pose proof (tw_len TMAP_B _ Bw HWORLD) as LBw.
  set (g := TWm.GOT_ndata Bw) in *.
  set (d := 256 + 24 * g).
  assert (HDd : d = 256 \/ d = 280) by (unfold d; lia).
  assert (HBL0 : 0 <= TIm.n_body_len n)
    by (rewrite <- E56; pose proof (TWLm.u_at_range NB 56 8); lia).
  pose proof (csw_src_bnd B LAWS lyc Sc W memc mdc (TW.u_at NB 48 8) (Z.of_nat (length (TIm.n_body n)))
    HAR SBODY ltac:(lia)) as (XB0 & XB63 & XBm).
  pose proof (csw_src_bnd B LAWS lyc Sc W memc mdc (TCm.OW_dn_body Bw g) (TIm.n_body_len n)
    HAR HSRCB ltac:(lia)) as (YB0 & YB63 & YBm).
  (* the OW body/counter/retry addresses, as world offsets *)
  assert (Eyb : TW.u_at Bw (TW.OFF_OW + d) 8 = TCm.OW_dn_body Bw g)
    by (unfold d, TCm.OW_dn_body, TCm.A_OW_dn_body; f_equal; lia).
  assert (HCeq : TW.u_at NB 64 4 = TW.u_at Bw (TW.OFF_OW + (d + 16)) 4).
  { rewrite E64, MCNT. unfold TCm.OW_dn_counter, TCm.A_OW_dn_counter, d.
    replace (TW.OFF_OW + 256 + 24 * g + 16) with (TW.OFF_OW + (256 + 24 * g + 16)) by lia. reflexivity. }
  assert (HReq : TW.u_at NB 68 2 = TW.u_at Bw (TW.OFF_OW + (d + 20)) 2).
  { rewrite E68, MRTY. unfold TCm.OW_dn_retry, TCm.A_OW_dn_retry, d.
    replace (TW.OFF_OW + 256 + 24 * g + 20) with (TW.OFF_OW + (256 + 24 * g + 20)) by lia. reflexivity. }
  (* the OW counter/retry bytes at memc *)
  assert (LDC : length (TW.sub Bw (TW.OFF_OW + (d + 16)) 4) = 4%nat)
    by (apply TWLm.length_sub; [unfold d; unfold TWm.OFF_OW; lia|];
        rewrite LBw; unfold d, TWm.OFF_OW, TWm.W_LEN; lia).
  assert (LDR : length (TW.sub Bw (TW.OFF_OW + (d + 20)) 2) = 2%nat)
    by (apply TWLm.length_sub; [unfold d; unfold TWm.OFF_OW; lia|];
        rewrite LBw; unfold d, TWm.OFF_OW, TWm.W_LEN; lia).
  pose proof (tw_bytes_at rsegs memc TMAP_B Bw TWm.OFF_OW TB_OW TWm.SZ_OW (d + 16) 4 TMAP_B_ok HW TMAP_B_OW
    ltac:(unfold d; lia) ltac:(unfold d, TWm.SZ_OW; lia)) as BDC.
  pose proof (tw_bytes_at rsegs memc TMAP_B Bw TWm.OFF_OW TB_OW TWm.SZ_OW (d + 20) 2 TMAP_B_ok HW TMAP_B_OW
    ltac:(unfold d; lia) ltac:(unfold d, TWm.SZ_OW; lia)) as BDR.
  (* the bytes of n->body and OW.dn[g].body agree, at memc *)
  assert (BODYEQ : forall i, 0 <= i < TIm.n_body_len n ->
    aview tfibsegs (w_H W) memc (TW.u_at NB 48 8 + i) =
    aview tfibsegs (w_H W) memc (TCm.OW_dn_body Bw g + i)).
  { intros i Hi.
    assert (LHSi : aview tfibsegs (w_H W) memc (TW.u_at NB 48 8 + i)
                 = Some (DSp.bz (nth (Z.to_nat i) (TIm.n_body n) (Z_to_bv 8 0)))).
    { replace (TW.u_at NB 48 8 + i) with (TW.u_at NB 48 8 + Z.of_nat (Z.to_nat i)) by lia.
      exact (csw_garr_view W memc (TW.u_at NB 48 8) (TIm.n_body n) (Z.to_nat i) ltac:(lia) GBODY). }
    destruct Fr as [fr|]; [|exfalso; destruct (csw_frame_none _ _ _ MDB) as [_ E0]; lia].
    destruct HTFR as (Htf0 & Gtf & Stf & Otf).
    destruct (csw_frame_some fr (TCm.OW_dn_body Bw g) (TIm.n_body_len n) db MDB ltac:(lia))
      as (Hoff0 & Hoffb & Hdbeq).
    assert (Hjt : (Z.to_nat (TCm.OW_dn_body Bw g - TIm.tf_addr fr + i) < length (TIm.tf_bytes fr))%nat) by lia.
    assert (RHSi : aview tfibsegs (w_H W) memc (TCm.OW_dn_body Bw g + i)
                 = Some (DSp.bz (nth (Z.to_nat (TCm.OW_dn_body Bw g - TIm.tf_addr fr + i))
                                     (TIm.tf_bytes fr) (Z_to_bv 8 0)))).
    { replace (TCm.OW_dn_body Bw g + i)
        with (TIm.tf_addr fr + Z.of_nat (Z.to_nat (TCm.OW_dn_body Bw g - TIm.tf_addr fr + i))) by lia.
      exact (csw_garr_view W memc (TIm.tf_addr fr) (TIm.tf_bytes fr)
               (Z.to_nat (TCm.OW_dn_body Bw g - TIm.tf_addr fr + i)) Hjt Gtf). }
    rewrite LHSi, RHSi. f_equal.
    assert (Edb : nth_error (TIm.tf_bytes fr) (Z.to_nat (TCm.OW_dn_body Bw g - TIm.tf_addr fr + i))
                = nth_error db (Z.to_nat i)).
    { rewrite Hdbeq.
      rewrite (csw_nth_sub (TIm.tf_bytes fr) (TCm.OW_dn_body Bw g - TIm.tf_addr fr)
                 (Z.to_nat (TIm.n_body_len n)) (Z.to_nat i) ltac:(lia) ltac:(lia)).
      f_equal. lia. }
    assert (Ezs : nth_error (TWm.zs (firstn (Z.to_nat (TIm.n_body_len n)) (TIm.n_body n))) (Z.to_nat i)
                = nth_error (TWm.zs db) (Z.to_nat i)) by (rewrite MZS; reflexivity).
    unfold TWm.zs in Ezs. rewrite !nth_error_map in Ezs.
    rewrite (csw_nth_error_firstn (TIm.n_body n) (Z.to_nat (TIm.n_body_len n)) (Z.to_nat i) ltac:(lia)) in Ezs.
    rewrite <- Edb in Ezs.
    destruct (nth_error (TIm.n_body n) (Z.to_nat i)) as [bx|] eqn:Ex;
      [|exfalso; apply nth_error_None in Ex; lia].
    destruct (nth_error (TIm.tf_bytes fr) (Z.to_nat (TCm.OW_dn_body Bw g - TIm.tf_addr fr + i)))
      as [by_|] eqn:Ey; [|exfalso; apply nth_error_None in Ey; lia].
    cbn [option_map] in Ezs. injection Ezs as Ezs.
    rewrite (csw_nth_of_error (TIm.n_body n) (Z.to_nat i) bx (Z_to_bv 8 0) Ex).
    rewrite (csw_nth_of_error (TIm.tf_bytes fr) _ by_ (Z_to_bv 8 0) Ey).
    unfold DSp.bz. exact Ezs. }
  (* transfer agreement memc -> m1 outside the frame window *)
  assert (TRm1 : forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - 32 \/ spZ regs <= a) ->
    aview tfibsegs (w_H W) m1 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hd'. apply aview_eq_of. unfold mrestrict.
    destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [reflexivity|].
    apply MU1. cbn [outside]. rewrite unsigned_lit by lia. split; [lia | exact I]. }
  (* the body bytes agree at m1 *)
  assert (BODYEQ1 : forall i, 0 <= i < TIm.n_body_len n ->
    aview tfibsegs (w_H W) m1 (TW.u_at NB 48 8 + i) = aview tfibsegs (w_H W) m1 (TCm.OW_dn_body Bw g + i)).
  { intros i Hi. unfold decode_off_win, NTC_SIZE in OBODY. unfold decode_off_win in HOFFB.
    unfold CSDATA_STK, CSDATA_FRAME, ESTACK in OBODY, HOFFB.
    rewrite (TRm1 (TW.u_at NB 48 8 + i) ltac:(lia) ltac:(lia)).
    rewrite (TRm1 (TCm.OW_dn_body Bw g + i) ltac:(lia) ltac:(lia)).
    exact (BODYEQ i Hi). }
  (* register facts at the post-run-1 state *)
  assert (R1T : YKK.getr (ms_regs msT) 1 = Z_to_bv 64 CSD_RET)
    by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; reflexivity).
  assert (R2W : YKK.getr (ms_regs msT) 2 = Z_to_bv 64 (spZ regs + -32))
    by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; reflexivity).
  assert (R2T : spZ (ms_regs msT) = spZ regs + -32).
  { unfold spZ at 1. rewrite R2W. apply unsigned_lit. lia. }
  assert (R3T : YKK.getr (ms_regs msT) 3 = w64 (as_gp B))
    by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; exact HGP).
  assert (R4T : YKK.getr (ms_regs msT) 4 = w64 (as_tp B))
    by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; exact HTP).
  assert (R10T : YKK.getr (ms_regs msT) 10 = w64 (TW.u_at NB 48 8))
    by (rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; reflexivity).
  assert (R11T : YKK.getr (ms_regs msT) 11 = w64 (TCm.OW_dn_body Bw g))
    by (rewrite <- Eyb; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; reflexivity).
  assert (R12T : YKK.getr (ms_regs msT) 12 = w64 (TIm.n_body_len n))
    by (rewrite <- E56; rewrite (decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity; reflexivity).
  (* bounds for the two bcmp ranges *)
  unfold decode_off_win, NTC_SIZE in OBODY. unfold decode_off_win in HOFFB.
  unfold CSDATA_STK, CSDATA_FRAME, ESTACK in OBODY, HOFFB.
  assert (RDXall : (forall a, TW.u_at NB 48 8 <= a < TW.u_at NB 48 8 + TIm.n_body_len n ->
                      aview tfibsegs (w_H W) m1 a <> None) /\
                   range_addressable (aview tfibsegs (w_H W) m1) SHADOW_OFF
                     (TW.u_at NB 48 8) (TIm.n_body_len n) /\
                   (0 < TIm.n_body_len n ->
                      shadow_hull_vis (aview tfibsegs (w_H W) m1) (TW.u_at NB 48 8) (TIm.n_body_len n))).
  { destruct (Z.eq_dec (TIm.n_body_len n) 0) as [E0|E0].
    - rewrite E0. split; [intros a Ha; lia|]. split; [intros xx Hxx; lia | intros HH; lia].
    - assert (RD : decode_rd_ok W m1 (TW.u_at NB 48 8) (TIm.n_body_len n)).
      { apply (trans_rd_ok_sub W m1 (TW.u_at NB 48 8) (Z.of_nat (length (TIm.n_body n)))
          (TW.u_at NB 48 8) (TIm.n_body_len n)); [| lia | lia | lia].
        apply (trans_rd_ok_view W W memc m1 (TW.u_at NB 48 8) (Z.of_nat (length (TIm.n_body n)))).
        - exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc _ _ HAR SBODY ltac:(lia)).
        - intros a Ha. apply TRm1; [lia | lia].
        - intros s Hs. apply TRm1; [unfold kLowMemEnd, kHighShadowEnd in Hs; lia
            | unfold kLowMemEnd, kHighShadowEnd in Hs; lia]. }
      destruct RD as (Rv & Ra & Rh & _).
      split; [exact Rv|]. split; [exact Ra | intros _; exact Rh]. }
  destruct RDXall as (RDXv & RDXa & RDXh).
  assert (RDYall : (forall a, TCm.OW_dn_body Bw g <= a < TCm.OW_dn_body Bw g + TIm.n_body_len n ->
                      aview tfibsegs (w_H W) m1 a <> None) /\
                   range_addressable (aview tfibsegs (w_H W) m1) SHADOW_OFF
                     (TCm.OW_dn_body Bw g) (TIm.n_body_len n) /\
                   (0 < TIm.n_body_len n ->
                      shadow_hull_vis (aview tfibsegs (w_H W) m1) (TCm.OW_dn_body Bw g) (TIm.n_body_len n))).
  { destruct (Z.eq_dec (TIm.n_body_len n) 0) as [E0|E0].
    - rewrite E0. split; [intros a Ha; lia|]. split; [intros xx Hxx; lia | intros HH; lia].
    - assert (RD : decode_rd_ok W m1 (TCm.OW_dn_body Bw g) (TIm.n_body_len n)).
      { apply (trans_rd_ok_view W W memc m1 (TCm.OW_dn_body Bw g) (TIm.n_body_len n)).
        - exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc _ _ HAR HSRCB ltac:(lia)).
        - intros a Ha. apply TRm1; [lia | lia].
        - intros s Hs. apply TRm1; [unfold kLowMemEnd, kHighShadowEnd in Hs; lia
            | unfold kLowMemEnd, kHighShadowEnd in Hs; lia]. }
      destruct RD as (Rv & Ra & Rh & _).
      split; [exact Rv|]. split; [exact Ra | intros _; exact Rh]. }
  destruct RDYall as (RDYv & RDYa & RDYh).
  assert (RDXm : amem_range (TW.u_at NB 48 8) (TIm.n_body_len n))
    by (unfold amem_range in XBm |- *; lia).
  assert (RDX0 : 0 <= TW.u_at NB 48 8) by lia.
  assert (RDX63 : TW.u_at NB 48 8 + TIm.n_body_len n <= 2 ^ 63) by lia.
  assert (RDYm : amem_range (TCm.OW_dn_body Bw g) (TIm.n_body_len n)) by exact YBm.
  assert (RDY0 : 0 <= TCm.OW_dn_body Bw g) by lia.
  assert (RDY63 : TCm.OW_dn_body Bw g + TIm.n_body_len n <= 2 ^ 63) by lia.
  eapply SRr_bind.
  { eapply (@aj_bcmp_at fx rc YE2k.tfib_sink_head tfibsegs B LAWS decode_segs_low
      (transportb_sigma TB___interceptor_trampoline_bcmp) (ABCMP fx) W (ms_regs msT) m1
      CSDATA_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdT 0
      (TW.u_at NB 48 8) (TCm.OW_dn_body Bw g) (TIm.n_body_len n) (-32) (Z_to_bv 64 CSD_RET) JI1).
    - exact R10T.
    - exact R11T.
    - exact R12T.
    - lia.
    - exact RDX0.
    - exact RDX63.
    - exact RDY0.
    - exact RDY63.
    - exact R2T.
    - reflexivity.
    - lia.
    - unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia.
    - exact R3T.
    - exact R4T.
    - exact R1T.
    - apply YK0s.ret_ok_even. vm_compute. reflexivity.
    - intros a Ha. split; [exact (RDXv a Ha)|]. unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia.
    - intros a Ha. split; [exact (RDYv a Ha)|]. unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia.
    - intros a Ha. unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia.
    - intros a Ha. unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia.
    - exact RDXm.
    - exact RDYm.
    - exact RDXa.
    - exact RDXh.
    - exact RDYa.
    - exact RDYh. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & JI2 & HPRES2 & Hv & Hiff & Hview & Happ).
  (* the answer is 0: the two ranges agree byte for byte *)
  assert (HV0 : v = w64 0).
  { apply Hiff. intros i Hi. apply BODYEQ1. lia. }
  (* ---- transfer the run-2 facts to mem2 ---- *)
  assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - 8224 \/ spZ regs <= a) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hd'. rewrite (Hview a Ha ltac:(unfold ESTACK; lia)).
    apply TRm1; [exact Ha | lia]. }
  assert (MG2 : forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - 8224 \/ spZ regs <= a) ->
    w_H W (Z_to_bv 64 a) = false -> mrd rsegs mem2 (wa a) = mrd rsegs memc (wa a))
    by (intros a Ha Hd' Hv'; exact (csw_mrd_of_aview W memc mem2 a Hv' (AG2 a Ha Hd'))).
  (* OW payload bytes are visible *)
  assert (VISOW : forall a, TB_OW <= a < TB_OW + 304 -> w_H W (Z_to_bv 64 a) = false).
  { intros a Ha. apply (csw_tw_vis W a). exists TWm.OFF_OW, TB_OW, TWm.SZ_OW.
    split; [exact TMAP_B_OW | unfold TWm.SZ_OW; lia]. }
  (* bytes_at mem2 for p, OW counter, OW retry *)
  assert (HOWB : 4096 <= TB_OW /\ TB_OW + 304 <= 0x1000000) by (unfold TB_OW; lia).
  assert (HDb : 256 <= d <= 280) by (destruct HDd as [Ed|Ed]; lia).
  assert (BNB2 : bytes_at rsegs mem2 p NB).
  { apply (csw_bytes_keep memc mem2 p NB); [|exact BNB]. intros j Hj. rewrite LNB in Hj.
    apply MG2;
      [ lia
      | unfold CSDATA_STK, CSDATA_FRAME, ESTACK in HOFFP; lia
      | apply VISP; rewrite LNB; lia ]. }
  assert (BDC2 : bytes_at rsegs mem2 (TB_OW + (d + 16)) (TW.sub Bw (TWm.OFF_OW + (d + 16)) 4)).
  { apply (csw_bytes_keep memc mem2 _ _); [|exact BDC]. intros j Hj. rewrite LDC in Hj.
    apply MG2; [lia | lia | apply VISOW; lia]. }
  assert (BDR2 : bytes_at rsegs mem2 (TB_OW + (d + 20)) (TW.sub Bw (TWm.OFF_OW + (d + 20)) 2)).
  { apply (csw_bytes_keep memc mem2 _ _); [|exact BDR]. intros j Hj. rewrite LDR in Hj.
    apply MG2; [lia | lia | apply VISOW; lia]. }
  (* shadow bytes at mem2 *)
  assert (SH642 : mrd rsegs mem2 (wa ((p + 64) / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0)).
  { rewrite MG2; [exact SH64 | | | exact VS64].
    - pose proof (SHB1 (p + 64) ltac:(lia)) as (Q1 & Q2 & _). lia.
    - pose proof (SHB1 (p + 64) ltac:(lia)) as (Q1 & Q2 & Q3). unfold ACells.ASAN_K in *. left. lia. }
  assert (SHDC2 : mrd rsegs mem2 (wa ((TB_OW + d + 16) / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0)).
  { rewrite MG2; [exact SHDC | | | exact VSDC].
    - pose proof (SHB1 (TB_OW + d + 16) ltac:(lia)) as (Q1 & Q2 & _). lia.
    - pose proof (SHB1 (TB_OW + d + 16) ltac:(lia)) as (Q1 & Q2 & Q3). unfold ACells.ASAN_K in *. left. lia. }
  (* the frame, kept across the bcmp call (above its window) *)
  assert (HFRBND : 0 <= spZ regs + -32 /\ spZ regs <= 2 ^ 64) by lia.
  lazymatch type of FR1 with
  | rw_cells _ _ _ ?cs => assert (FR2 : rw_cells rsegs mem2 (spZ regs + -32) cs)
  end.
  { apply (decode_rw_cells_ext m1 mem2 _ _); [|exact FR1]. intros i Hi.
    unfold csd_fr in Hi. cbn [cells_size csize Nat.add] in Hi.
    assert (HPfr : apresent (w_H W) m1 (spZ regs + -32 + i))
      by (destruct JI1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _);
          apply HP; unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia).
    pose proof (Happ _ HPfr) as HPfr2.
    exact (decode_present_eq W m1 mem2 (spZ regs + -32 + i) HPfr HPfr2
             (Hview (spZ regs + -32 + i) ltac:(lia) ltac:(unfold ESTACK; lia))). }
  (* stk mem2 at the empty bottom *)
  assert (STK2 : stk rsegs mem2 (spZ regs - 32) (spZ regs + -32))
    by (split; [lia|]; split; [lia|]; intros a Ha; lia).
  assert (HA0 : YKK.getr regs2 (Z_to_bv 5 10) = w64 0) by (rewrite <- HV0; exact Hv).
  (* ---- the second run ---- *)
  replace (Z_to_bv 64 CSD_RET) with (LCK.w64 CSD_RET) in * by reflexivity.
  eapply decode_run.
  { unfold LCK.ms_of_regs.
    rewrite (HPRES2 2 ltac:(unfold acallee_saved; lia)), (HPRES2 3 ltac:(unfold acallee_saved; lia)),
      (HPRES2 4 ltac:(unfold acallee_saved; lia)), (HPRES2 8 ltac:(unfold acallee_saved; lia)),
      (HPRES2 9 ltac:(unfold acallee_saved; lia)), (HPRES2 18 ltac:(unfold acallee_saved; lia)),
      (HPRES2 19 ltac:(unfold acallee_saved; lia)), (HPRES2 20 ltac:(unfold acallee_saved; lia)),
      (HPRES2 21 ltac:(unfold acallee_saved; lia)), (HPRES2 22 ltac:(unfold acallee_saved; lia)),
      (HPRES2 23 ltac:(unfold acallee_saved; lia)), (HPRES2 24 ltac:(unfold acallee_saved; lia)),
      (HPRES2 25 ltac:(unfold acallee_saved; lia)), (HPRES2 26 ltac:(unfold acallee_saved; lia)),
      (HPRES2 27 ltac:(unfold acallee_saved; lia)).
    rewrite HA0.
    rewrite !(decode_ms_reg _ _ _ _ _ _ _ _ _ EQVT) by reflexivity.
    eapply (csd_run_ret_F _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ mem2 _ p d NB Bw HDd);
      [ lia | exact HP8 | lia | exact LNB | exact LBw
      | (rewrite ESP2; lia)
      | (rewrite ESP2; lia)
      | exact STK2
      | (rewrite ESP2; lia)
      | exact FR2
      | (rewrite ESP2; unfold CSDATA_STK, CSDATA_FRAME, ESTACK in HOFFP;
         destruct HOFFP as [HO|HO]; [left; lia | right; lia])
      | exact HCeq | exact HReq | exact BNB2 | exact BDC2 | exact BDR2
      | exact SH642 | exact SHDC2
      | exact RNGFR | exact RNGOW | exact RNGP | exact RS64 | exact RSDC ]. }
  intros ms3 md3 (ms0' & (r10 & r11 & r12 & spx & -> & Hspx & ST3) & EQV3) SBM3.
  rewrite (decode_ms_shape _ _ _ _ EQV3).
  rewrite GRET.
  (* ---- the close ---- *)
  apply SRr_ret. unfold transport_csdata_post, decode_cg_post.
  exists lyc, Sc, (ms_regs ms3), mem2, md3, 0.
  split; [reflexivity|].
  split; [unfold CSDATA_EV; lia|].
  split.
  { pose proof (ajournal_sub_tok tfibsegs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
      CSDATA_STK (spZ regs) [] [] lyc Sc W mem2 md3 0 HJ
      (JEXEC mem2 mem2 md2 md3 JI2 (munch_refl _ _) (wmono_refl rsegs mem2) SBM3)
      ltac:(unfold CSDATA_STK, CSDATA_FRAME, ESTACK; lia) HWHI
      ltac:(intros a (r & Hr & _); destruct Hr)) as J.
    cbn [app] in J. exact J. }
  split.
  { apply (csw_pres_eqv _ _ _ _ _ _ _ _ _ EQV3).
    apply csw_pres_ret. rewrite Hspx. unfold spZ. reflexivity. }
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { exact (acall_kept_of_journal tfibsegs B decode_segs_low CSDATA_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md3 0 (fun _ => False)
             (JEXEC mem2 mem2 md2 md3 JI2 (munch_refl _ _) (wmono_refl rsegs mem2) SBM3) HAR
             ltac:(intros a (r & Hr & _); destruct Hr)
             ltac:(intros bq mq i Hb _ _; exact Hb)
             sink_closed_nil). }
  split; [exact (mle_start MT Sc MTL)|].
  exact EBw.
Qed.

Print Assumptions transport_check_state_data_cg_holds.
