(* LLVMFuzzerTestOneInput_kit_src_ro: kit lemma K2 of the image-A walk of LLVMFuzzerTestOneInput,
   LLVMFuzzerTestOneInput_segs.v lc_src_ro_stmt. At every cut state each of the 13 read-only ranges the walk hands a
   callee (LLVMFuzzerTestOneInput_st.v lc_ro_ranges) satisfies trans_src_ok by its TRANS_RO_RD disjunct:
   - every byte lies in a range of TRANS_RO_RD (a closed check over the 13 ranges, lc_ro_ranges_rd);
   - trans_sh_any: LLVMFuzzerTestOneInput_st.v lc_sh_any, from the record facts lp_cells and lp_llvmf_cells;
   - decode_rd_ok at the cut state: each byte visible (K1, lc_rom_view_stmt, gives the image view at every TRANS_RO_RD
     byte, and DgnTransportCg.v trans_ro_rd_rom_clean an image byte there), the two shadow facts (trans_sh_any at the
     cut state's AR, which W_journalG.v ajournal_gx_AR reads off lc_core's journal), amem_range and the bounds
     (DgnTransportCg.v trans_ro_rd_bounds at the range's first and last byte).
   K1 is an argument: the composer supplies it from its own kit row. The proof reads nothing of the journal but its
   AR state. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
Import ListNotations.
Open Scope Z_scope.

(* A byte in some range of TRANS_RO_RD, as a boolean. *)
Definition lc_ro_rd_b (z : Z) : bool :=
  existsb (fun r : Z * Z => (fst r <=? z) && (z <? fst r + snd r))%bool TRANS_RO_RD.

(* Every byte of the 13 ranges is in TRANS_RO_RD, and no range is empty (decided by vm_compute). *)
Lemma lc_ro_ranges_rd : forallb (fun r => forallb lc_ro_rd_b (decode_zr_bytes r)) lc_ro_ranges = true.
Proof. vm_compute. reflexivity. Qed.
Lemma lc_ro_ranges_pos : forallb (fun r : Z * Z => 0 <? snd r) lc_ro_ranges = true.
Proof. vm_compute. reflexivity. Qed.

Section src_ro. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Lemma lc_src_ro_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) : lc_src_ro_stmt B MT XL RLO RHI.
Proof.
  intros HP cx ly' S' W' regs' mem' md' e q n HB HC HIn.
  change (In (q, n) lc_ro_ranges) in HIn.
  pose proof (K1 HP cx ly' S' W' regs' mem' md' e HB HC) as HR.
  assert (HAR : @AR rc tfibsegs B ly' S' W' mem' md').
  { destruct HC as [HJ _]. eapply ajournal_gx_AR. exact HJ. }
  pose proof (@lc_sh_any rc B ly' (@lp_cells rc B MT XL RLO RHI HP) (@lp_llvmf_cells rc B MT XL RLO RHI HP)
    (q, n) HIn) as HSH.
  cbn [fst snd] in HSH.
  assert (HRD : forall a, q <= a < q + n -> trans_in_ro_rd a).
  { intros a Ha.
    assert (HE : Exists (in_zr a) lc_ro_ranges).
    { apply Exists_exists. exists (q, n). split; [exact HIn|]. unfold in_zr. cbn [fst snd]. lia. }
    pose proof (decode_zr_enum lc_ro_rd_b lc_ro_ranges a lc_ro_ranges_rd HE) as Hb.
    unfold lc_ro_rd_b in Hb. apply existsb_exists in Hb as [r [Hr Hb]].
    apply andb_true_iff in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    unfold trans_in_ro_rd. apply Exists_exists. exists r. split; [exact Hr|]. unfold in_zr. lia. }
  assert (Hn : 0 < n).
  { pose proof (proj1 (forallb_forall _ lc_ro_ranges) lc_ro_ranges_pos (q, n) HIn) as H.
    cbn [snd] in H. apply Z.ltb_lt in H. exact H. }
  pose proof (trans_ro_rd_bounds q (HRD q ltac:(lia))) as Bq.
  pose proof (trans_ro_rd_bounds (q + n - 1) (HRD (q + n - 1) ltac:(lia))) as Bn.
  unfold trans_src_ok. right. split.
  - right. right. right. split; [exact HRD | exact HSH].
  - destruct (HSH ly' S' W' mem' md' HAR) as [HRA HHV].
    unfold decode_rd_ok.
    split; [|split; [exact HRA|split; [exact HHV|split; [|split]]]].
    + intros a Ha. destruct (trans_ro_rd_rom_clean a (HRD a Ha)) as [_ [b Hb]].
      rewrite (HR a (HRD a Ha)), Hb. cbn [option_map]. discriminate.
    + unfold amem_range, kLowMemEnd. left. lia.
    + lia.
    + change (2 ^ 63) with 9223372036854775808. lia.
Qed.

End src_ro.
