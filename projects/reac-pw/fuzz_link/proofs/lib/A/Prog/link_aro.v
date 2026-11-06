(* reac-pw/fuzz_link, image A: the discharges of link_amem.v apre's last conjunct (`forall a, inFP Wr a ->
   ~ in_roP segs rlo rhi a`) at image A's segments `tfibsegs` (lib/A/AB1v.v, Asan.M.loaded_segments) and its relro
   window [PCAP_RLO, PCAP_RHI) (lib/A/Prog/PcapRelro.v). Each fact is one boolean computed by vm_compute and its
   soundness lemma; a walk at the abstract `pa_segs` reaches them through `pa_segs = tfibsegs`.
   - LA_G_not_ro: no byte of LA_G (the slot journal's program-global ranges, link_aaddr.v: __stderr_FILE + 136,
     g_nl, g_names, long_alias, g_sink, g_said, g_say, ofl_head) is read-only.
   - not_ro_wseg_tfib: an address at or above PCAP_RHI that lies in a writable segment of tfibsegs is not read-only
     (the writable and the non-writable segments of the image do not overlap: tfib_wr_ro_disj).
   Proves no function (kind: segment lemma). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0n YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
Import ListNotations.
Local Open Scope Z_scope.

Lemma LA_G_ro_free :
  forallb (fun r => ro_free_b tfibsegs PCAP_RLO PCAP_RHI (fst r) (fst r + snd r)) LA_G = true.
Proof. vm_compute. reflexivity. Qed.

Lemma LA_G_not_ro : forall a, inG LA_G a -> ~ in_roP tfibsegs PCAP_RLO PCAP_RHI a.
Proof.
  intros a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hin & Hr).
  pose proof LA_G_ro_free as H. rewrite forallb_forall in H.
  apply (not_ro_of_free tfibsegs PCAP_RLO PCAP_RHI (fst r) (fst r + snd r)); [exact (H r Hin) |].
  unfold in_zr in Hr. lia.
Qed.

(* no writable segment of the image overlaps a non-writable one *)
Definition wr_ro_disj_b (segs : list Segment) : bool :=
  forallb (fun s1 => forallb (fun s2 =>
    negb (seg_writable s1) || seg_writable s2 ||
    (Z.of_N (seg_base s1) + Z.of_N (seg_size s1) <=? Z.of_N (seg_base s2)) ||
    (Z.of_N (seg_base s2) + Z.of_N (seg_size s2) <=? Z.of_N (seg_base s1))) segs) segs.

Lemma tfib_wr_ro_disj : wr_ro_disj_b tfibsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma not_ro_wseg_tfib : forall a, PCAP_RHI <= a ->
  (exists s, In s tfibsegs /\ seg_writable s = true /\
     Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s)) ->
  ~ in_roP tfibsegs PCAP_RLO PCAP_RHI a.
Proof.
  intros a Ha (s1 & H1 & W1 & R1) [(s2 & H2 & W2 & R2) | Hw]; [| lia].
  pose proof tfib_wr_ro_disj as H. unfold wr_ro_disj_b in H. rewrite forallb_forall in H.
  specialize (H s1 H1). rewrite forallb_forall in H. specialize (H s2 H2).
  rewrite W1, W2 in H. cbn [negb orb] in H.
  apply orb_true_iff in H as [H | H]; apply Z.leb_le in H; lia.
Qed.
