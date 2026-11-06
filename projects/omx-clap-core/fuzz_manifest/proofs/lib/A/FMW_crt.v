(* check_round_trip 0x80ea0 (fuzz_manifest.c:253-291), the assembly: check_round_trip_spec (FMH_Fn.v) from the 13
   segments of FMW_crtA..E/X. Straight part: entry -> 0x80f00 (A) -> n = 0: ret (X0) | malloc (B) -> snprintf + names
   (C1) -> snprintf + as_ruled (C2) -> the loop setup (E). The loop over the split points k = 1 .. n - 1 closes by
   induction on n - k: the loop head (L) exits (X) or calls plain (uri + k); plain true -> four reader calls (D1..D4),
   plain false -> L1n; the loop step (I) goes back to the head at k + 1 or exits (X, tail call free). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YM05 YC85 YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AF0l ACej FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_crt0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
FMW_crtA FMW_crtB FMW_crtX FMW_crtC FMW_crtD FMW_crtE.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis FB : FmB B.
Hypothesis IMG : fm_img_facts tfibsegs B.
Hypothesis UNIV : fm_univ B.
Hypothesis AMALLOC : amalloc04_rule tfibsegs B ameter_triv.
Hypothesis AFREE : afree04_rule tfibsegs B ameter_triv.
Hypothesis STRLEN : astrlen_realizes tfibsegs B PC_strlen.
Hypothesis SNP : asnprintf_realizes tfibsegs B PC_snprintf.
Hypothesis NAMES : names_spec tfibsegs B CTX_lv2_locate_manifest_names.
Hypothesis ASR : as_ruled_spec tfibsegs B CTX_as_ruled.
Hypothesis PLAIN : plain_spec tfibsegs B.

(* apply a segment lemma: its section hypotheses and the resume-point premises come from the context *)
Local Ltac seg L := eapply (L B); try eassumption.

(* the exit through the tail call free (0x810ac) *)
Local Lemma crt_exit : forall cx ly S W regs mem md k0 t, crt_base B cx -> crt_X B cx ly S W regs mem md k0 t ->
  SRr tfibsegs W (cfg_at tfibsegs CRT_X regs mem md) (crt_post B cx).
Proof. intros. seg crt_segX. Qed.

(* the loop: from the loop head at split point k, by induction on a bound d of n - k *)
Lemma crt_loop : forall cx t, crt_base B cx ->
  forall (d k : nat), (length (cx_ub cx) - k <= d)%nat ->
  forall ly S W regs mem md k0 m, crt_L B cx ly S W regs mem md k0 t m k ->
  SRr tfibsegs W (cfg_at tfibsegs CRT_L regs mem md) (crt_post B cx).
Proof.
intros cx t HB d. induction d as [|d IH]; intros k Hd ly Sl W regs mem md k0 m HL;
  pose proof HL as (_ & _ & Hk & _); unfold cx_n in Hk.
- exfalso. lia.
- seg crt_segL.
  + intros ly1 S1 W1 regs1 mem1 md1 HX. exact (crt_exit _ _ _ _ _ _ _ _ _ HB HX).
  + intros ly1 S1 W1 regs1 mem1 md1 HL1.
    (* the loop step after split point k, whatever the reader calls made *)
    assert (KI : forall m' ly' S' W' regs' mem' md' k0', crt_I B cx ly' S' W' regs' mem' md' k0' t m' k ->
      SRr tfibsegs W' (cfg_at tfibsegs CRT_L9 regs' mem' md') (crt_post B cx)).
    { intros m' ly' S' W' regs' mem' md' k0' HI. seg crt_segI.
      - intros ly2 S2 W2 regs2 mem2 md2 HL2. exact (IH (S k) ltac:(lia) _ _ _ _ _ _ _ _ HL2).
      - intros ly2 S2 W2 regs2 mem2 md2 HX. exact (crt_exit _ _ _ _ _ _ _ _ _ HB HX). }
    destruct (ManifestModel.plain_name (skipn k (cx_ub cx))) eqn:Ep.
    * seg crt_segD1. intros ly2 S2 W2 regs2 mem2 md2 k2 H2.
      seg crt_segD2. intros ly3 S3 W3 regs3 mem3 md3 k3 H3.
      seg crt_segD3. intros ly4 S4 W4 regs4 mem4 md4 k4 H4.
      seg crt_segD4. intros ly5 S5 W5 regs5 mem5 md5 k5 HI. exact (KI _ _ _ _ _ _ _ _ HI).
    * seg crt_segL1n. intros ly2 S2 W2 regs2 mem2 md2 HI. exact (KI _ _ _ _ _ _ _ _ HI).
Qed.

Theorem check_round_trip_holds : check_round_trip_spec tfibsegs B CTX_check_round_trip.
Proof.
intros ly S W regs mem md ch u ub live peak cnt fail HPRE HCTX H10 Hu Hku Hlu HG HQ Hlive Hev Hbb.
assert (Hf : fail = SIZE_MAXZ) by exact (proj1 HQ). subst fail.
set (cx := mkCX ly S W regs mem md ch u ub live peak cnt).
assert (HB : crt_base B cx)
  by exact (conj HPRE (conj HCTX (conj H10 (conj Hu (conj Hku (conj Hlu (conj HG (conj HQ (conj Hlive (conj Hev Hbb)))))))))).
change (SRr tfibsegs (cx_W cx) (cfg_at tfibsegs A_check_round_trip (cx_regs cx) (cx_mem cx) (cx_md cx)) (crt_post B cx)).
eapply (crt_segA B) with (cx := cx); try eassumption.
intros ly2 S2 W2 regs2 mem2 md2 k2 H2. seg crt_segB.
- intros ly3 S3 W3 regs3 mem3 md3 k3 H3. seg crt_segX0.
- intros ly3 S3 W3 regs3 mem3 md3 k3 t H3. seg crt_segC1.
  intros ly4 S4 W4 regs4 mem4 md4 k4 H4. seg crt_segC2.
  intros ly5 S5 W5 regs5 mem5 md5 k5 H5. seg crt_segE.
  + intros ly6 S6 W6 regs6 mem6 md6 H6. exact (crt_loop cx t HB (length (cx_ub cx)) 1 ltac:(lia) _ _ _ _ _ _ _ _ H6).
  + intros ly6 S6 W6 regs6 mem6 md6 H6. exact (crt_exit _ _ _ _ _ _ _ _ _ HB H6).
Qed.
End W.
