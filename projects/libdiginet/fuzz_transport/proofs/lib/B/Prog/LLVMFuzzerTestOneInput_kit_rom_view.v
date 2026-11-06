(* LLVMFuzzerTestOneInput_kit_rom_view: the kit lemma K1 of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v lc_rom_view_stmt): at every cut state the
   read-only bytes the walk reads (DgnTransportBCg.v TRANS_RO_RD) read as the image (trans_rom_view_rd).

   The proof, for one TRANS_RO_RD byte a:
   1. at the entry, the slot's pre (lc_base: lib/B/YCfn.v tfib_lib_pre_x) has arodata_okS at [RLO, RHI): a byte of a
      non-writable loaded segment or of [RLO, RHI) that is not an owned static and not errno reads as the image. The
      byte a is such a byte: it lies in a non-writable segment or in [TRANS_RLO, TRANS_RHI) (trans_ro_rd_rom_clean),
      and lp_rlo / lp_rhi put [TRANS_RLO, TRANS_RHI) inside [RLO, RHI); it is not an owned static (lp_ro_unowned)
      and not errno (lp_rom_no_errno), by trans_ro_rd_scoped;
   2. the core's G journal (lc_core: ajournal_gx G_HARNESS_B 0 [] from the entry) is the donor's journal (YCbq.v
      ajournal) from a start memory memS that agrees with the entry memory outside G_HARNESS_B (W_journalG.v
      ajournal_g, gagree). Its image clause keeps an image byte (trans_ro_img) that is not an owned static, not errno
      and spared by the journal's frame list (fp_spares_below, at any list: a lies below the stdio head 0x613e68,
      lib/B/YE2k.v A_ofl_head, by trans_ro_rd_bounds);
   3. a is not a byte of G_HARNESS_B (trans_ro_rd_bounds: a < 0xa4000; inG_G_HARNESS_hull: G_HARNESS_B lies at or
      above 0x5ded00), so memS and the entry memory show the same byte at a (W_journalG.v aview_gagree).
   The structure is image A's lib/A/Prog/LLVMFuzzerTestOneInput_kit_rom_view.v; the record's facts, the hull of G and
   the stdio head are image B's. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YK00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
Import ListNotations.
Open Scope Z_scope.

Section kit. Context {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.

Lemma lc_rom_view_ok : lc_rom_view_stmt B MT XL RLO RHI.
Proof.
unfold lc_rom_view_stmt.
intros HP cx ly' S' W' regs' mem' md' e HB HC a Ha.
assert (HRU : trans_ro_rd_unowned B) by (destruct HP; assumption).
assert (HRE : trans_rom_no_errno B) by (destruct HP; assumption).
assert (HRLO : RLO <= TRANS_RLO) by (destruct HP; assumption).
assert (HRHI : TRANS_RHI <= RHI) by (destruct HP; assumption).
clear HP.
(* the entry's arodata_okS (the slot's pre) *)
unfold lc_base, tfib_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HARO & _).
(* the G journal: the donor's journal from memS, memS = the entry memory outside G_HARNESS_B *)
destruct HC as (HJX & _).
destruct HJX as (_ & _ & (memS & HJ & Hag) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G3 & _).
clear HJ.
pose proof (trans_ro_rd_bounds a Ha) as Rb.
destruct (trans_ro_rd_scoped B HRU HRE a Ha) as [Hown Herr].
destruct (trans_ro_rd_rom_clean a Ha) as [Hrom _].
assert (HLT : a < @AOFL_HEAD YE2k.tfib_sink_head).
{ cbn [YCbq.AOFL_HEAD YI16.sk_ofl_head YE2k.tfib_sink_head]. unfold YE2k.A_ofl_head. lia. }
assert (HNG : inGb TransportGB.G_HARNESS_B (bv_unsigned (Z_to_bv 64 a)) = false).
{ rewrite (YK00.u64_lit a ltac:(lia)). apply inGb_false. intro Ga.
  pose proof (inG_G_HARNESS_hull a Ga) as Gh. unfold TransportGB.G_HARNESS_B_LO in Gh. lia. }
rewrite (G3 a (trans_ro_img a Ha) Hown Herr (fp_spares_below _ a HLT)).
rewrite (aview_gagree _ _ _ _ _ a Hag HNG).
apply HARO; [| exact Hown | exact Herr].
destruct Hrom as [Hrom | Hrl]; [left; exact Hrom | right; lia].
Qed.

End kit.
