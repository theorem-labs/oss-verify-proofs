(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): the GUARD of the GXA seam of musl vfprintf on link's
   memory FILE, GXA's vf_mf_guard (lib/CJ/RL/GXA/LinkVfMfA.v), from facts that hold where link's code calls vfprintf.
   The memory-FILE twin of FMgxaSeamGuard.v (vf_ready_a_holds for the vsnprintf FILE).

   vf_mf_guard asks, at every store m1 that the walk reaches through the footprint W = vf_mf_fp lo q f (the stack
   window [lo, q), the FILE's first 232 bytes, the buffer [f + 280, f + 1304)):
   - the format, musl's prefix and each %s argument still addressable (pf_rng): ASan shadow facts, which a munch
     over application memory keeps (AsanFacts.munch_meta), so the entry facts carry over;
   - pc_guard with the memory FILE's out_ready (LinkMfSinkA.mf_out_ready): memcpy ready at __fwritex's room arm,
     whose destination is in the buffer and whose source is printf_core's stack or a range addressable at m1;
     memset and strnlen ready at printf_core's calls.  No flush readiness: saved_buf is 0, so f->write is never
     called on this path.
   seam_calls_ready_mf is what the three readiness predicates must meet for that: readiness at every store a munch
   over W reaches from the entry store.  Each nested munch of the guard (pc_guard's, then mf_out_ready's over
   [(f + 280, f + 1304); (f + 40, f + 48); (sp - SN_WRITE_DEPTH, sp)]) is inside W when the window holds
   printf_core's depth below the call (lo + OUT_DEPTH <= q - 368), so one quantifier over `munch W` covers them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YK11 YM05 YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Import Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require Import
AsanFacts SetCall StrnlenCall CopyCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require
G_printf_core_common G_vfprintf_snf LinkMfSinkA LinkVfMfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMgxaSeamCall FMgxaSeamGuard.
Import ListNotations.
Open Scope Z_scope.

Module GCF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.
Module GC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GV := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GMS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.LinkMfSinkA.
Module GMF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.LinkVfMfA.
Module SG := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamGuard.

#[local] Existing Instance N_img_asan_vf.

(* ---- the footprint is application memory ---- *)
Lemma all_app_vf_mf_fp : forall lo q f,
  app_ivl lo q -> app_ivl f (f + 232) -> app_ivl (f + 280) (f + 1304) -> all_app (GMF.vf_mf_fp lo q f).
Proof. intros lo q f H1 H2 H3. unfold GMF.vf_mf_fp. cbn [all_app]. tauto. Qed.

Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the readiness predicates of the three interceptor call contracts (FMgxaSeamCall.v) *)
Variable copy_ready : (word -> option byte) -> Z -> Z -> Z -> Z -> Prop.
Variable set_ready : (word -> option byte) -> Z -> Z -> Z -> Prop.
Variable strn_ready : (word -> option byte) -> Z -> Z -> Z -> list byte -> Prop.

(* What the interceptors' readiness must meet at musl vfprintf's call on the memory FILE at f, with entry store m
   and stack window [lo, q): at each store m' that a munch over vf_mf_fp reaches from m (so m' keeps m's shadow,
   given as meta_kept),
   - memcpy, called by __fwritex with its frame at sp - 64, copies N bytes into the buffer [f + 280, f + 1304),
     from printf_core's stack below q - 368 (with 8 bytes of slack) or from a range addressable in m;
   - memset, called at sp, fills printf_core's stack below q - 368 (with 8 bytes of slack);
   - strnlen, called at sp, reads at most L bytes of a range addressable in m.
   The source and string ranges are stated at the entry store m: m and m' have the same shadow. *)
Definition seam_calls_ready_mf (m : word -> option byte) (q lo f : Z) : Prop :=
  forall m' : word -> option byte,
    munch (GMF.vf_mf_fp lo q f) m m' -> wmono img_segs m m' -> meta_kept m m' ->
    (forall sp Dst P N,
        lo + GC.OUT_DEPTH <= sp -> sp <= q - 368 ->
        f + 280 <= Dst -> Dst + N <= f + 1304 -> 0 <= N ->
        (sp <= P /\ P + N + 8 <= q - 368 \/ pf_rng m P N) ->
        copy_ready m' (sp - 64) Dst P N)
    /\ (forall sp Dst N,
          lo + SET_DEPTH <= sp -> sp <= Dst -> Dst + N + 8 <= q - 368 -> set_ready m' sp Dst N)
    /\ (forall sp S N L buf,
          lo + STRN_DEPTH <= sp -> sp <= q - 368 -> pf_rng m S L ->
          Z.min (strnlen_res N buf + 1) N <= L -> strn_ready m' sp S N buf).

Lemma vf_mf_guard_holds :
  forall (m : word -> option byte) (q lo f A : Z) (fmt : list Z) (slots : list word) (args : list parg),
    pf_rng m A (zlength fmt) -> musl_prefix_addressable m -> GV.args_pf m slots args ->
    app_ivl lo q -> app_ivl f (f + 232) -> app_ivl (f + 280) (f + 1304) ->
    lo + GC.OUT_DEPTH <= q - 368 ->
    seam_calls_ready_mf m q lo f ->
    GMF.vf_mf_guard set_ready strn_ready copy_ready FMgxaSeamCall.SEAM_INV m q lo f A fmt slots args.
Proof.
  intros m q lo f A fmt slots args PF PRE APF ALO AF AB GEO READY.
  pose proof (all_app_vf_mf_fp lo q f ALO AF AB) as AW.
  unfold GMF.vf_mf_guard.
  intros m1 MU1 WM1.
  pose proof (munch_meta _ _ _ MU1 AW) as MK1.
  pose proof (SG.meta_kept_sym _ _ MK1) as KM1.
  split; [exact (pf_rng_kept _ _ _ _ PF MK1)|].
  split; [exact (musl_prefix_kept _ _ _ PRE MU1 AW)|].
  split; [exact (SG.args_pf_kept _ _ _ _ MK1 APF)|].
  unfold GC.pc_guard. intros m2 MU2 WM2.
  assert (MU02 : munch (GMF.vf_mf_fp lo q f) m m2) by (eapply munch_trans; [exact MU1 | exact MU2]).
  assert (WM02 : wmono img_segs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  split; [exact I|]. split; [|split].
  - (* memcpy at __fwritex's room arm *)
    intros sp S L HS1 HS2 HSRC. unfold GMS.mf_out_ready.
    intros m3 Dst N' MU3 WM3 HD1 HD2 HN.
    assert (MU23 : munch (GMF.vf_mf_fp lo q f) m2 m3).
    { eapply munch_weaken; [|exact MU3].
      unfold sub_fp, GMF.vf_mf_fp. cbn [outside]. intros x Hx.
      unfold GC.OUT_DEPTH, SN_WRITE_DEPTH, COPY_DEPTH in *. lia. }
    assert (MU03 : munch (GMF.vf_mf_fp lo q f) m m3) by (eapply munch_trans; [exact MU02 | exact MU23]).
    assert (WM03 : wmono img_segs m m3) by (eapply wmono_trans; [exact WM02 | exact WM3]).
    destruct (READY m3 MU03 WM03 (munch_meta _ _ _ MU03 AW)) as [RC _].
    apply RC; [exact HS1 | exact HS2 | exact HD1 | exact HD2 | lia |].
    destruct HSRC as [HSRC|HSRC]; [left; lia|right].
    apply (GCF.pf_rng_prefix m S L N'); [exact (pf_rng_kept _ _ _ _ HSRC KM1) | lia].
  - (* memset *)
    intros sp Dst N' H1 H2 H3.
    destruct (READY m2 MU02 WM02 (munch_meta _ _ _ MU02 AW)) as (_ & RS & _).
    exact (RS sp Dst N' H1 H2 H3).
  - (* strnlen *)
    intros sp S N' L buf H1 H2 H3 H4.
    destruct (READY m2 MU02 WM02 (munch_meta _ _ _ MU02 AW)) as (_ & _ & RT).
    exact (RT sp S N' L buf H1 H2 (pf_rng_kept _ _ _ _ H3 KM1) H4).
Qed.

End G.
