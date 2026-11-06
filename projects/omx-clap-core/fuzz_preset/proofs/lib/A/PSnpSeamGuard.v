(* The GUARD of the GXA seam at musl vfprintf: GXA's vf_ready_a (lib/CJ/RL/GXA/G_vfprintf_snf.v:219),
   from facts that hold where the harness calls vfprintf.

   vf_ready_a asks, at every store m1 that the walk reaches through the footprint
   W = vf_snf_fp lo q Fp CK D dn (the stack window, the FILE, the cookie, the destination):
   - the format, musl's prefix and each %s argument are still addressable (pf_rng);
   - pc_guard: the three interceptors (memcpy through the snprintf sink, memset, strnlen) are ready
     at each call printf_core makes;
   - sn_write_ready: memcpy is ready at the final flush.

   The first three are ASan shadow facts.  When each interval of W is application memory (all_app),
   a munch over W does not change the shadow (AsanFacts.munch_meta), so the entry facts carry over
   (pf_rng_kept, musl_prefix_kept, args_pf_kept).

   The last two are about the readiness predicates of the interceptors, which arrive later
   (h-rw-ide-4 gives copy_ready and set_ready, RtPrintf.GxStrn gives strn_ready).
   seam_calls_ready is what those predicates must meet: readiness at each store that a munch over W
   reaches from the entry store, at each call geometry of printf_core and the snprintf sink.  Each
   nested munch of the guard is inside W when the stack window holds printf_core's depth below the
   flush call (lo + OUT_DEPTH <= q - 368), so one quantifier over `munch W` covers all of them. *)
(* Modified by Theorem Labs, 2026-10: copied to omx-clap-core/fuzz_preset as lib/A/PSnpSeamGuard.v (image A) from port-fm's lib/A/FMgxaSeamGuard.v (origin/cold/port-fm-rtprintf-param 3e35620c52e) under SEAM-SPLIT R1-R2: module paths fuzz_manifest -> fuzz_preset, RT_IImgA / A_img -> lib/CJ/RL/I/IImgA / N_img_asan, FMgxaSeamCall -> lib/A/PSnpSeamCall. No AR. 0x22e18 here is GXA's sym key (G_vfprintf_snf's vf_ready_a premise), not an address of this image. This file walks no machine step and reads no runtime-option cell (relocation rule 15:22Z). *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpSeamGuard.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require Import
AsanFacts SetCall StrnlenCall CopyCall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require
G_printf_core_common G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpSeamCall.
Import ListNotations.
Open Scope Z_scope.

Module GCF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_core_common.
Module GC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_snfsink.
Module GV := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GXI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.

#[local] Existing Instance N_img_asan.

(* ---- the footprint is application memory ---- *)
Lemma all_app_vf_snf_fp : forall lo q Fp CK D dn,
  app_ivl lo q -> app_ivl Fp (Fp + 232) -> app_ivl CK (CK + 16) -> app_ivl D (D + Z.of_nat dn) ->
  all_app (GV.vf_snf_fp lo q Fp CK D dn).
Proof. intros lo q Fp CK D dn H1 H2 H3 H4. unfold GV.vf_snf_fp. cbn [all_app]. tauto. Qed.

(* the same when the FILE and the cookie lie on the stack above the window (GXA's own premises
   q <= Fp and Fp + 232 <= CK, G_vfprintf_snf.v:211) and the stack is in high application memory *)
Lemma all_app_vf_snf_fp_stack : forall lo q Fp CK D dn,
  HIGHMEM_BEG <= lo -> lo <= q -> q <= Fp -> Fp + 232 <= CK -> CK + 16 <= APPMEM_END ->
  app_ivl D (D + Z.of_nat dn) ->
  all_app (GV.vf_snf_fp lo q Fp CK D dn).
Proof.
  intros lo q Fp CK D dn H1 H2 H3 H4 H5 H6.
  apply all_app_vf_snf_fp; [apply high_stack_app; lia .. | exact H6].
Qed.

(* ---- shadow facts across a munch that keeps the shadow ---- *)
Lemma meta_kept_sym : forall m m' : word -> option byte, meta_kept m m' -> meta_kept m' m.
Proof. intros m m' H a Ha. symmetry. exact (H a Ha). Qed.

Lemma pf_rng_nil : forall m : word -> option byte, pf_rng m 0 0.
Proof.
  intros m. unfold pf_rng, addressable, end_in_app, APPMEM_END.
  split; [apply Z.pow_nonneg; lia|].
  split; [split; [lia|]; split; [lia|]; split; [lia|]; intros i Hi; exfalso; lia|].
  split; [left; reflexivity|]. intros i Hi. exfalso. lia.
Qed.

Lemma args_pf_kept : forall (m m1 : word -> option byte) (slots : list word) (args : list parg),
  meta_kept m m1 -> GV.args_pf m slots args -> GV.args_pf m1 slots args.
Proof.
  intros m m1 slots args MK. revert slots.
  induction args as [|a args IH]; intros slots H; destruct slots as [|w slots]; try exact I.
  destruct H as [H1 H2]. split; [|exact (IH slots H2)].
  destruct a; try exact I. exact (pf_rng_kept _ _ _ _ H1 MK).
Qed.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : YG0f.asyms.
(* the readiness predicates of the three interceptor call contracts (FMgxaSeamCall.v) *)
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.

(* What the interceptors' readiness must meet at musl vfprintf's call with entry store m, stack
   window [lo, q), FILE Fp, cookie CK and destination [D, D + dn): at each store m' that a munch over
   vf_snf_fp reaches from m (so m' keeps m's shadow, given as meta_kept),
   - memcpy, called by the snprintf sink with its frame at sp - 64, copies N bytes to the
     destination or to vfprintf's 80-byte buffer at q - 352, from that buffer, from printf_core's
     stack below q - 368 (with 8 bytes of slack), or from a range addressable in m;
   - memset, called at sp, fills printf_core's stack below q - 368 (with 8 bytes of slack);
   - strnlen, called at sp, reads at most L bytes of a range addressable in m.
   The source and string ranges are stated at the entry store m: m and m' have the same shadow. *)
Definition seam_calls_ready (m : word -> option byte) (q lo Fp CK D : Z) (dn : nat) : Prop :=
  forall m' : word -> option byte,
    munch (GV.vf_snf_fp lo q Fp CK D dn) m m' -> wmono img_segs m m' -> meta_kept m m' ->
    (forall sp Dst P N,
        lo + GC.OUT_DEPTH <= sp -> sp <= q - 368 ->
        (D <= Dst /\ Dst + N <= D + Z.of_nat dn \/ q - 352 <= Dst /\ Dst + N <= q - 352 + GXI.SNF_CAP) ->
        0 <= N ->
        (P = q - 352 /\ N <= GXI.SNF_CAP \/ sp <= P /\ P + N + 8 <= q - 368 \/ pf_rng m P N) ->
        copy_ready m' (sp - 64) Dst P N)
    /\ (forall sp Dst N,
          lo + SET_DEPTH <= sp -> sp <= Dst -> Dst + N + 8 <= q - 368 -> set_ready m' sp Dst N)
    /\ (forall sp S N L buf,
          lo + STRN_DEPTH <= sp -> sp <= q - 368 -> pf_rng m S L ->
          Z.min (strnlen_res N buf + 1) N <= L -> strn_ready m' sp S N buf).

Lemma vf_ready_a_holds :
  forall (m : word -> option byte) (q lo Fp CK D : Z) (dn : nat) (N bufp A VA : Z) (fmt : list Z) (slots : list word)
         (args : list parg),
    A + zlength fmt <= sym 0x22e18 ->
    pf_rng m A (zlength fmt) -> musl_prefix_addressable m -> GV.args_pf m slots args ->
    app_ivl lo q -> app_ivl Fp (Fp + 232) -> app_ivl CK (CK + 16) -> app_ivl D (D + Z.of_nat dn) ->
    lo + GC.OUT_DEPTH <= q - 368 ->
    seam_calls_ready m q lo Fp CK D dn ->
    GV.vf_ready_a (GS.snf_out_ready copy_ready) set_ready strn_ready copy_ready SEAM_INV
      m q lo Fp CK D dn N bufp A VA fmt slots args.
Proof.
  intros m q lo Fp CK D dn N bufp A VA fmt slots args HA PF PRE APF ALO AFP ACK AD GEO READY.
  pose proof (all_app_vf_snf_fp lo q Fp CK D dn ALO AFP ACK AD) as AW.
  unfold GV.vf_ready_a, GV.vf_snf_guard.
  split; [exact HA|].
  intros m1 MU1 WM1.
  pose proof (munch_meta _ _ _ MU1 AW) as MK1.
  pose proof (meta_kept_sym _ _ MK1) as KM1.
  split; [exact (pf_rng_kept _ _ _ _ PF MK1)|].
  split; [exact (musl_prefix_kept _ _ _ PRE MU1 AW)|].
  split; [exact (args_pf_kept _ _ _ _ MK1 APF)|].
  split.
  - (* printf_core's three interceptor calls *)
    unfold GC.pc_guard. intros m2 MU2 WM2.
    assert (MU02 : munch (GV.vf_snf_fp lo q Fp CK D dn) m m2) by (eapply munch_trans; [exact MU1 | exact MU2]).
    assert (WM02 : wmono img_segs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    split; [exact I|]. split; [|split].
    + (* memcpy through the snprintf sink *)
      intros sp S L HS1 HS2 HSRC. unfold GS.snf_out_ready.
      intros m3 Dst P N' MU3 WM3 HDST HN HP.
      assert (MU23 : munch (GV.vf_snf_fp lo q Fp CK D dn) m2 m3).
      { eapply munch_weaken; [|exact MU3].
        unfold sub_fp, sn_write_footprint, GV.vf_snf_fp. cbn [outside]. intros x Hx.
        unfold GC.OUT_DEPTH, SN_WRITE_DEPTH, COPY_DEPTH, GXI.SNF_CAP in *. lia. }
      assert (MU03 : munch (GV.vf_snf_fp lo q Fp CK D dn) m m3) by (eapply munch_trans; [exact MU02 | exact MU23]).
      assert (WM03 : wmono img_segs m m3) by (eapply wmono_trans; [exact WM02 | exact WM3]).
      destruct (READY m3 MU03 WM03 (munch_meta _ _ _ MU03 AW)) as [RC _].
      apply RC; [exact HS1 | exact HS2 | exact HDST | exact HN |].
      destruct HP as [HP|[-> HNL]]; [left; exact HP|right].
      destruct HSRC as [HSRC|HSRC]; [left; lia|right].
      apply (GCF.pf_rng_prefix m S L N'); [exact (pf_rng_kept _ _ _ _ HSRC KM1) | lia].
    + (* memset *)
      intros sp Dst N' H1 H2 H3.
      destruct (READY m2 MU02 WM02 (munch_meta _ _ _ MU02 AW)) as (_ & RS & _).
      exact (RS sp Dst N' H1 H2 H3).
    + (* strnlen *)
      intros sp S N' L buf H1 H2 H3 H4.
      destruct (READY m2 MU02 WM02 (munch_meta _ _ _ MU02 AW)) as (_ & _ & RT).
      exact (RT sp S N' L buf H1 H2 (pf_rng_kept _ _ _ _ H3 KM1) H4).
  - (* memcpy at the final flush, called with the sink's frame at q - 368 *)
    unfold sn_write_ready. intros m2 D' P N' MU2 WM2 HD HN HEND HP.
    assert (MU12 : munch (GV.vf_snf_fp lo q Fp CK D dn) m1 m2).
    { eapply munch_weaken; [|exact MU2].
      unfold sub_fp, sn_write_footprint, GV.vf_snf_fp. cbn [outside]. intros x Hx.
      unfold GC.OUT_DEPTH, SN_WRITE_DEPTH, COPY_DEPTH in *. lia. }
    assert (MU02 : munch (GV.vf_snf_fp lo q Fp CK D dn) m m2) by (eapply munch_trans; [exact MU1 | exact MU12]).
    assert (WM02 : wmono img_segs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    destruct (READY m2 MU02 WM02 (munch_meta _ _ _ MU02 AW)) as [RC _].
    apply RC; [exact GEO | lia | left; lia | exact HN |].
    destruct HP as [HP|[-> HP0]]; [left; exact HP | right; right].
    replace N' with 0 by lia. exact (pf_rng_nil m).
Qed.

End G.
