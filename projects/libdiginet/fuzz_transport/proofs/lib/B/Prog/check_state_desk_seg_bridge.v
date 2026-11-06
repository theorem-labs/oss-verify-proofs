(* check_state_desk_seg_bridge: the facts the walk of check_state_desk in image B (lib/B/Prog/check_state_desk_cgW.v)
   uses to read the contract's premises as the memory bundle csd_mem of lib/B/Prog/check_state_desk_seg_kit.v (image
   B's twin of lib/A/Prog/check_state_desk_seg_bridge.v, over lib/B/Prog/DgnTransportBCg.v and DgnTransportBCgRun.v):
     csd_tw_mrd        the world relation at the machine's view, from the statement's view through aview;
     csd_vis_rd        a byte of a readable range is not hidden;
     csd_bytes_of_garr garr8 of a byte list at visible addresses is that list under mrd;
     csd_shadow0       the shadow byte of a granule inside a readable range is 0;
     csd_shadow_any    the shadow byte of a byte of a readable range is one the instrumented check accepts;
     csd_ro_byte       a TRANS_RO_RD byte reads as the image's, under mrd;
     csd_zsh_byte      a granule of a zero-shadow range of the record has the shadow byte 0;
     csd_view_out      two memories that agree outside a stack window agree under aview there. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCgRun TWorldB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_desk_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module ACells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module DSp := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

Local Notation segs := tfibsegs.

(* ---- the world relation at the machine's view ---- *)

Section Bridge.
Context {rc : YM05.RunCeil}.
Variable B : asyms.

(* Every payload byte of TMAP_B is a byte of a loaded segment (TWorldA.v TMAP_B_in_G, DgnTransportCg.v
   trans_g_img), so the world's view through aview and the machine's view agree there. *)
Lemma csd_tw_mrd : forall (W : world segs) (memc : word -> option byte) (Bw : list byte),
  tw_at TMAP_B (aview segs (w_H W) memc) Bw ->
  tw_at TMAP_B (fun a => option_map (fun x : byte => bv_unsigned x) (mrd rsegs memc (wa a))) Bw.
Proof.
  intros W memc Bw H. apply (tw_kept_rows TMAP_B (aview segs (w_H W) memc)); [exact H|].
  intros o b n i Hin Hi.
  assert (HG : W_journalG.inG TransportGB.G_HARNESS_B (b + i))
    by (unfold W_journalG.inG; apply Exists_exists; exists (b, n);
        split; [exact (TMAP_B_in_G o b n Hin) | unfold in_zr; cbn [fst snd]; lia]).
  symmetry. apply decode_aview_mrd. apply decode_vis_seg. exact (trans_g_img _ HG).
Qed.

(* A byte of a readable range is not hidden. *)
Lemma csd_vis_rd : forall (W : world segs) memc q n a,
  decode_rd_ok W memc q n -> q <= a < q + n -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W memc q n a (Hv & _) Ha.
  destruct (aview segs (w_H W) memc a) as [v|] eqn:Ev; [exact (decode_aview_vis W memc a v Ev)|].
  exfalso. exact (Hv a Ha Ev).
Qed.

(* A visible byte: the machine's view is the walk's view. *)
Lemma csd_mrd_of_mbyte : forall (W : world segs) memc a, w_H W (Z_to_bv 64 a) = false ->
  mrd rsegs memc (wa a) = YP09.mbyte segs (mrestrict (w_H W) memc) a.
Proof. intros W memc a Hv. unfold mrd, wa, YP09.mbyte, mrestrict. rewrite Hv. reflexivity. Qed.

(* garr8 of a byte list at visible addresses is that list under mrd. *)
Lemma csd_bytes_of_garr : forall (W : world segs) memc (A : Z) (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> w_H W (Z_to_bv 64 a) = false) ->
  garr8 segs (mrestrict (w_H W) memc) A (map DSp.bz bs) ->
  bytes_at rsegs memc A bs.
Proof.
  intros W memc A bs H0 H1 HV HG.
  split; [exact H0|]. split; [exact H1|].
  intros i Hi.
  assert (Hi' : (i < length (map DSp.bz bs))%nat) by (rewrite length_map; exact Hi).
  destruct (HG i Hi') as [HV1 HR].
  specialize (HV1 0%nat ltac:(lia)). rewrite Z.add_0_r in HV1.
  rewrite (csd_mrd_of_mbyte W memc (A + Z.of_nat i) ltac:(apply HV; lia)), HV1.
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hi).
  rewrite nth_indep with (d' := DSp.bz (Z_to_bv 8 0)) in HR |- * by (rewrite length_map; exact Hi).
  rewrite map_nth in HR |- *.
  f_equal. unfold DSp.bz in *.
  pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as Rb. unfold bv_modulus in Rb.
  change (2 ^ Z.of_N 8) with 256 in Rb.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !(Z.mod_small _ 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. lia.
Qed.

(* The shadow byte of a granule inside a readable range is 0 (the byte at offset 7 of the granule lies in the
   range, and saddr_ok of a byte at offset 7 leaves only the shadow value 0). *)
Lemma csd_shadow0 : forall (W : world segs) memc q n x,
  decode_rd_ok W memc q n -> q <= x -> x + 8 <= q + n ->
  w_H W (Z_to_bv 64 (x / 8 + ACells.ASAN_K)) = false /\
  mrd rsegs memc (wa (x / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0).
Proof.
  intros W memc q n x (Hv & Hra & Hh & Hm & H0 & H63) H1 H2.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Hmb.
  destruct (Hra (8 * (x / 8) + 7) ltac:(lia)) as (s & Hs & Hok).
  assert (Ediv : (8 * (x / 8) + 7) / 8 = x / 8)
    by (replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia; rewrite Z.div_add by lia;
        rewrite (Z.div_small 7 8) by lia; lia).
  assert (Emod : (8 * (x / 8) + 7) mod 8 = 7)
    by (replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia; rewrite Z.mod_add by lia;
        apply Z.mod_small; lia).
  assert (Es : s = 0) by (unfold saddr_ok in Hok; rewrite Emod in Hok; lia).
  assert (Ea : shadow_of_addr SHADOW_OFF (8 * (x / 8) + 7) = x / 8 + ACells.ASAN_K)
    by (unfold shadow_of_addr, SHADOW_OFF, ACells.ASAN_K; rewrite Ediv; lia).
  rewrite Ea, Es in Hs.
  destruct (decode_aview_some W memc _ 0 Hs) as (Hvis & b & Hb & Eb).
  split; [exact Hvis|]. rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Eb. reflexivity.
Qed.

(* The shadow byte of a byte of a readable range: one the instrumented check accepts. *)
Lemma csd_shadow_any : forall (W : world segs) memc q n x,
  decode_rd_ok W memc q n -> q <= x < q + n ->
  w_H W (Z_to_bv 64 (x / 8 + ACells.ASAN_K)) = false /\
  exists k : byte, mrd rsegs memc (wa (x / 8 + ACells.ASAN_K)) = Some k /\
                   (bv_signed k = 0 \/ x mod 8 < bv_signed k).
Proof.
  intros W memc q n x (Hv & Hra & Hh & Hm & H0 & H63) Hx.
  destruct (Hra x Hx) as (s & Hs & Hok).
  assert (Ea : shadow_of_addr SHADOW_OFF x = x / 8 + ACells.ASAN_K)
    by (unfold shadow_of_addr, SHADOW_OFF, ACells.ASAN_K; lia).
  rewrite Ea in Hs.
  destruct (decode_aview_some W memc _ s Hs) as (Hvis & b & Hb & Eb).
  split; [exact Hvis|]. exists b. split; [exact Hb|].
  unfold saddr_ok in Hok. rewrite (decode_byte_signed b ltac:(lia)). lia.
Qed.

(* A TRANS_RO_RD byte reads as the image's byte under mrd (its segment is loaded, so it is not hidden). *)
Lemma csd_ro_byte : forall (W : world segs) memc a,
  trans_rom_view_rd W memc -> trans_in_ro_rd a ->
  w_H W (Z_to_bv 64 a) = false /\ mrd rsegs memc (wa a) = PropExec.seg_rom rsegs (wa a).
Proof.
  intros W memc a HROM Ha.
  assert (Hvis : w_H W (Z_to_bv 64 a) = false) by (apply decode_vis_seg; exact (trans_ro_img a Ha)).
  split; [exact Hvis|].
  pose proof (HROM a Ha) as E. rewrite (decode_aview_mrd W memc a Hvis) in E.
  change (YKK.seg_rom segs (Z_to_bv 64 a)) with (PropExec.seg_rom rsegs (wa a)) in E.
  destruct (mrd rsegs memc (wa a)) as [b1|]; destruct (PropExec.seg_rom rsegs (wa a)) as [b2|];
    cbn [option_map] in E; try discriminate E; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* A granule of a zero-shadow range of the record has the shadow byte 0 at every AR state. *)
Lemma csd_zsh_byte : forall ly S (W : world segs) memc md (lo hi T : Z),
  @AR rc segs B ly S W memc md -> decode_zshadow_at B lo hi -> T mod 8 = 0 -> lo <= T -> T + 8 <= hi ->
  w_H W (Z_to_bv 64 (T / 8 + ACells.ASAN_K)) = false /\
  mrd rsegs memc (wa (T / 8 + ACells.ASAN_K)) = Some (Z_to_bv 8 0).
Proof.
  intros ly S W memc md lo hi T HAR HZ HT H1 H2.
  pose proof (decode_zshadow_rd B ly S W memc md lo hi T HAR HT H1 H2 HZ) as Hs.
  replace (ACells.shadow_addr T) with (T / 8 + ACells.ASAN_K) in Hs
    by (unfold ACells.shadow_addr; lia).
  destruct (decode_aview_some W memc _ 0 Hs) as (Hvis & b & Hb & Eb).
  split; [exact Hvis|]. rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Eb. reflexivity.
Qed.

(* Two memories that agree outside [lo, hi) agree under aview there. *)
Lemma csd_view_out : forall (W : world segs) (m m' : word -> option byte) (lo hi : Z),
  munch [(lo, hi)] m m' ->
  forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= lo \/ hi <= a) ->
    aview segs (w_H W) m' a = aview segs (w_H W) m a.
Proof.
  intros W m m' lo hi MU a Ha Hd. apply aview_eq_of. unfold mrestrict.
  destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
  apply MU. cbn [outside]. rewrite unsigned_lit by lia. split; [lia | exact I].
Qed.

End Bridge.
