(* The not-found case of memchr(x, 0, n) (lib/A/Rt/RtString.v amemchr0_nf_realizes, window ESTACK) at
   PC_memchr = 0x45158, the one-instruction trampoline of ___interceptor_memchr. Proved input: lib/A/Rt/Memchr.v
   memchr_icpt_realizesM, the walk of the interceptor and of musl's memchr for any byte c in a1, any n below 2^32
   and a found or a not-found result, over consts_view of musl's word-loop constants 0x10358 .. 0x10378
   (lib/Rt/MemchrDef.v amemchr_realizesM, lib/Rt/ConstsViewDef.v).
   This file instantiates that contract at c = 0 and reads its premises off ours: ecall_pre is the first part of
   ecall_pre_stk; aread_ok over n gives x + n <= 2^63, src_ok (both name the scratch window ESTACK), amem_range,
   range_addressable and shadow_hull_vis; rt_rom_view gives consts_view over the 32 bytes from 0x10358, which lie
   in the first, read-only segment of the image and meet no range of Tfib_owned_static and not the errno cell
   (lib/A/Rt/RtSStrlen.v sl_rom_in, sl_rom_unowned). The walk returns w64 (x + k) or w64 0 for the first zero byte
   at k; our first_byte at k = n says that no byte below n is zero, so k = n and the result is w64 0. The scratch
   window is present after the call because it is present before it (ecall_pre_stk) and the walk keeps every
   present byte present. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Memchr RtSStrlen.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* rt_rom_view gives the walk's consts_view over musl's word-loop constants *)
Lemma mnf_consts : forall B, CmdBSyms B -> forall (W : world tfibsegs) mem,
rt_rom_view tfibsegs B W mem -> consts_view tfibsegs 0x10358 0x10378 W mem.
Proof.
intros B TB W mem HROM a Ha.
destruct (RtSStrlen.sl_rom_unowned B TB a Ha) as [U1 U2].
exact (HROM a (RtSStrlen.sl_rom_in a Ha) U1 U2).
Qed.

(* no zero byte below n (first_byte at k = n) and the walk's first zero at k: k = n *)
Lemma mnf_k : forall (W : world tfibsegs) mem x n k,
first_byte tfibsegs W mem x n 0 n -> first_byte tfibsegs W mem x n 0 k -> k = n.
Proof.
intros W mem x n k (Hn0 & HNZ & _) (Hk0 & _ & HAT).
destruct (Z.lt_ge_cases k n) as [Hlt|Hge]; [|lia].
exfalso. destruct (HNZ k ltac:(lia)) as (b & Hb & Hb0).
rewrite (HAT Hlt) in Hb. injection Hb as Hb. exact (Hb0 (eq_sym Hb)).
Qed.

Theorem cmd_memchr0_nf : forall (B : asyms), AR_laws tfibsegs B -> CmdBSyms B ->
amemchr0_nf_realizes tfibsegs B PC_memchr.
Proof.
intros B LAWS TB ly S W regs mem md x n HPRE G10 G11 G12 Hn Hx HFB HRD HROM.
destruct HPRE as (HEP & Hslo & Hpres).
destruct HRD as (Hx0 & Hxn & _ & Hsrc & Ham & Hra & Hhull).
pose proof (Memchr.memchr_icpt_realizesM B LAWS TB ly S W regs mem md x 0 n HEP G10 G11 G12
ltac:(lia) Hn Hx Hxn Hsrc Ham Hra Hhull (mnf_consts B TB W mem HROM)) as HM.
change PC_memchr with 0x45158.
refine (SRr_mono tfibsegs W _ _ _ HM _).
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HAR' & HKEEP & Hsbm & (k & HFBk & A10) & Hfr & Hpres').
rewrite (mnf_k W mem x n k HFB HFBk), Z.ltb_irrefl in A10.
unfold art_post. split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hc|]. split; [exact HAR'|]. split; [exact HKEEP|]. split; [exact Hsbm|]. split; [exact A10|].
split; [intros a Ha Hs _; exact (Hfr a Ha Hs)|].
split; [exact Hpres'|].
intros a Ha. apply Hpres'. exact (Hpres a Ha).
Qed.

End c.
