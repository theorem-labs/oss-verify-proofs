(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/ImgBaseAG.v, with its module paths and module names changed; 84 of its 100 lines of code are new or changed and 91 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the memchr wrapper (wrapper_memchr, 0x43060) on the caller's journal, for the walks
   of link's own functions that call it (check_bounds +0x30, text_of +0x21c).

   - aj_gx_memchrM_at: lib/Rt/MemchrDef.v `amemchr_realizesM segs B lo hi pc` (proved on link by lib/A/Rt/RtClosed.v
     `link_memchrM_closed` at lo = 0x10360, hi = 0x10380) lifted onto ajournal_gx with LinkWalk.v aj_gx_art_sm_at
     (window ESTACK), keeping `same_but_materialized` for apost's descriptors and file system.
   - aconsts_of_aro: the contract's `consts_view lo hi` (the image bytes of the word constants musl's memchr reads)
     from apre's `arodata_okP` (YC20.v:46), given that the bytes are read-only image bytes the runtime does not own and
     not errno; `link_mc_ro` proves that of [0x10360, 0x10380) on the image (lib/A/AE39.v mc_in_rom, the owned static
     table of lib/A/AF0m.v PcapSyms, errno 0x631b6c).
   The other memchr form (`amemchr_realizes`, with the whole `rom_view`) asks every read-only byte, which arodata_okP
   gives only outside the runtime's owned statics and errno; the M form needs the 32 bytes only.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import MemchrDef ConstsViewDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m AE39.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.

Lemma aj_gx_memchrM_at : forall lo hi pc, amemchr_realizesM segs B lo hi pc ->
  forall G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n raw,
  gx_ok segs B G ->
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  spZ regsT mod 16 = 0 -> sp0 - STK <= spZ regsT - ESTACK -> spZ regsT <= sp0 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 c -> getr regsT 12 = w64 n ->
  0 <= c < 256 -> 0 <= n < 2 ^ 32 -> 0 < x -> x + n <= 2 ^ 63 ->
  src_ok segs W regsT memT x n -> amem_range x n ->
  range_addressable (aview segs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview segs (w_H W) memT) x n) ->
  consts_view segs lo hi W memT ->
  SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
       ajournal_gx segs B G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (exists kk, first_byte segs W memT x n c kk /\
          getr regs2 10 = (if kk <? n then w64 (x + kk) else w64 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros lo hi pc HC G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x c n raw
  HG HJX H16 Hlo Hhi Hgp Htp Hra Hraw Hx Hc Hn Hc0 Hn0 Hx0 Hxn Hsrc Hamr Hra' Hhull Hcv.
assert (ESTACK = 4096) as Hes by reflexivity.
pose proof (aj_gx_ecall_pre SK segs B ESTACK G XO OUT STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT
  HJX ltac:(lia) H16 Hlo Hhi ltac:(rewrite Hra; exact Hraw) Hgp Htp) as (HPRE & _ & Hwin).
eapply SRr_mono.
{ apply (aj_gx_art_sm_at SK segs B LAWS segs_low ESTACK (fun _ => False) pc G XO OUT W regsT memT STK sp0 FP ly S
    W0 mem md own lyc Sc mdc k raw
    (fun regs' _ => exists kk, first_byte segs W memT x n c kk /\
       getr regs' 10 = (if kk <? n then w64 (x + kk) else w64 0))
    HG HJX ltac:(lia) Hlo Hhi Hra).
  - intros a [].
  - eapply SRr_mono; [exact (HC lyc Sc W regsT memT mdc x c n HPRE Hx Hc Hn Hc0 Hn0 Hx0 Hxn Hsrc Hamr Hra' Hhull Hcv)|].
    cbv beta. intros W2 c2 _ (-> & regs' & mem' & md' & -> & HAR' & HP & Hsm & HK & Hfr & Hpres).
    split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|].
    split; [exact HAR'|]. split; [exact HP|]. split; [exact Hsm|]. split; [exact HK|].
    split; [intros a Ha Hw _; exact (Hfr a Ha Hw)|]. split; [exact Hpres|].
    intros a Ha. apply Hpres. apply Hwin. exact Ha. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HQ & Hfr & Hpres2 & Hsm).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact HJ2|]. split; [exact HP|]. split; [exact HQ|].
split; [intros a Ha Hw; exact (Hfr a Ha Hw (fun H => H))|]. split; [exact Hpres2 | exact Hsm].
Qed.

(* the word constants from apre's arodata_okP *)
Lemma aconsts_of_aro : forall rlo rhi (W : world segs) mem lo hi,
  (forall a, lo <= a < hi -> in_rom segs a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4)) ->
  arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> consts_view segs lo hi W mem.
Proof.
intros rlo rhi W mem lo hi Hc Haro a Ha. destruct (Hc a Ha) as (Hr & Ho & He).
apply Haro; [left; exact Hr | exact Ho | exact He].
Qed.
End a.

(* the 32 bytes of musl memchr's word constants on the image *)
Lemma link_mc_ro : forall B, AF0m.PcapSyms B ->
  forall a, 0x10360 <= a < 0x10380 -> in_rom AB1v.tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\
    ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros B TS a Ha. split; [apply AE39.mc_in_rom; unfold AE39.MC_LO, AE39.MC_HI; exact Ha|].
rewrite (AF0m.ts_owned B TS), (AF0m.ts_errno B TS). split.
- intros O. unfold AF0m.Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & X).
  unfold in_zr in X. cbn [In] in Hr.
  repeat match type of Hr with
  | _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X; lia|]
  | False => destruct Hr
  end.
- unfold AF0m.TFIB_ERRNO. lia.
Qed.
