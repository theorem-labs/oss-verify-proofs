(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalkIntr.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* Modified by Theorem Labs, 2026-10: cw_writable_kept is the text of writable_keptP in
   proofs/libreac/fuzz_knock/lib/A/APgInit.v:75-83 (origin/ossv/recipes 4b6f0df50aa7), and the call and resume follow
   the same file's lines 282-346 (the __asan_memset call and the state after it), on the concrete image B of
   libdiginet/fuzz_codec's ASan build (tfibsegs, no listing layer). *)
(* The call of a runtime intrinsic (__asan_memcpy at image B 0x51ae8, __asan_memset at 0x51f84) from a walk of
   codec's own code, and the symbolic state after it.
   - The walk's run stops at the intrinsic's entry after the `jal` (ra = the return address, a literal).
   - cw_intrin_call: the intrinsic runs under aintrin_realizes (lib/Reusable/YG0d.v); the caller's journal holds
     after it with the same layout and state, the callee-saved registers are kept, the n bytes at d hold the
     source bytes (OCpy) or x mod 256 (OSet), every other byte outside the stack the runtime uses below sp is kept,
     and the walk resumes at the return address with the regions rs it keeps (each off [d, d + n) and off that
     stack) and the caller-saved registers fresh atoms from kk on (YI04.v st_ok_after_call).
   - cw_region_kept_out: a region whose bytes the call leaves alone is kept in the sense st_ok_after_call needs. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the image-B entries of the two intrinsics *)
Definition CB_MEMCPY : Z := 0x51ae8.
Definition CB_MEMSET : Z := 0x51f84.

Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a byte that stays present stays writable *)
Lemma cw_writable_kept : forall H (m m2 : word -> option byte) a,
(apresent H m a -> apresent H m2 a) -> writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* a region whose bytes are off the zone Zout of a call's writes is kept by the call *)
Lemma cw_region_kept_out : forall E H (m m2 : word -> option byte) (Zout : Z -> Prop) r,
(forall a, 0 <= a < 2 ^ 64 -> ~ Zout a -> aview tfibsegs H m2 a = aview tfibsegs H m a) ->
(forall a, apresent H m a -> apresent H m2 a) ->
(forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r -> 0 <= a < 2 ^ 64 /\ ~ Zout a) ->
r_lo r <= r_wlo r -> r_whi r <= r_hi r ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H m2) r.
Proof.
intros E H m m2 Zout r HK Hp Hr Hlo Hhi. split.
- intros a Ha. destruct (Hr a Ha) as [Ha64 Hz]. apply (mbyte_of_aview tfibsegs). exact (HK a Ha64 Hz).
- intros a Ha. apply cw_writable_kept. exact (Hp a).
Qed.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
(* The call of the intrinsic at pc from a walk stopped at pc after its `jal` (ra = retpc), and the walk's state at
   the return address. The stack window [sp0 - STK, sp0) of the caller's journal holds the ESTACK bytes the
   intrinsic uses below the walk's sp. *)
Lemma cw_intrin_call : forall op pc, aintrin_realizes tfibsegs B op pc ->
forall W E ss ms md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k d x n retpc kk rs Q,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
getr (ms_regs ms) 10 = w64 d -> getr (ms_regs ms) 11 = w64 x -> getr (ms_regs ms) 12 = w64 n ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
sp0 - STK <= spZ (ms_regs ms) - ESTACK -> spZ (ms_regs ms) <= sp0 -> spZ (ms_regs ms) mod 16 = 0 -> sp0 mod 16 = 0 ->
getr (ms_regs ms) 3 = w64 (as_gp B) -> getr (ms_regs ms) 4 = w64 (as_tp B) ->
sr_get (ss_regs ss) 1 = SLit retpc -> 0 <= retpc < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 retpc) ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  ~ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms))) ->
amem_range d n -> range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) d n) ->
(match op with
 | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok tfibsegs W (ms_regs ms) (ms_mem ms) x n /\ (d + n <= x \/ x + n <= d) /\
           amem_range x n /\ range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x n /\
           (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x n)
 | OSet => True end) ->
ss_atoms_lt kk ss = true -> regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt kk rs = true ->
submem rs (ss_mem ss) ->
Forall (fun r => (forall a, base_val E (r_base r) + r_lo r <= a < base_val E (r_base r) + r_hi r ->
   0 <= a < 2 ^ 64 /\ ~ ((d <= a < d + n) \/ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms)))) /\
   r_lo r <= r_wlo r /\ r_whi r <= r_hi r) rs ->
(forall regs2 mem2 md2,
  ajournal tfibsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k ->
  aregs_preserved (ms_regs ms) regs2 -> getr regs2 10 = w64 d ->
  (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem2 (d + i) =
     match op with OCpy => aview tfibsegs (w_H W) (ms_mem ms) (x + i) | OSet => Some (x mod 256) end) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms)) ->
     aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms) a) ->
  (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) ->
  same_but_materialized md md2 ->
  st_ok tfibsegs (havoc E kk (map (getr regs2) CLOB)) (ss_after_call ss rs kk retpc)
    (restrict (w_H W) (mkst regs2 (Z_to_bv 64 retpc) mem2 (seg_rom tfibsegs))) ->
  SRr tfibsegs W (mkCfg (mkst regs2 (Z_to_bv 64 retpc) mem2 (seg_rom tfibsegs)) md2) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros op pc AI W E ss ms md STK sp0 FP ly S W0 mem0 md0 own lyc Sc k d x n retpc kk rs Q
  HS Hpc Hrv HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hwlo Hwhi Hal Hal0 Hgp Htp Hra Hret Hretok Hdest Hamr Hrad Hhull Hsrc
  Hat Hwf Hnc Hmat Hsub Hkeep K.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Ems.
pose proof (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 1%bv HS) as Hr1. rewrite Hra in Hr1. cbn [sv_denot] in Hr1.
assert (ESTACK = 4096) as Hes by reflexivity.
rewrite Ems. rewrite Hpc.
eapply SRr_bind.
{ eapply (aj_intrin_atS tfibsegs B LAWS tfib_segs_low op pc AI W (ms_regs ms) (ms_mem ms)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc md k d x n (spZ (ms_regs ms) - sp0) (Z_to_bv 64 retpc)
    HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn); try lia.
  - rewrite Zminus_mod, Hal, Hal0. reflexivity.
  - exact Hgp.
  - exact Htp.
  - exact Hr1.
  - exact Hretok.
  - intros a Ha. destruct (Hdest a Ha) as [H1 H2]. split; [exact H1|]. replace (sp0 + (spZ (ms_regs ms) - sp0)) with (spZ (ms_regs ms)) by lia. exact H2.
  - exact Hamr.
  - exact Hrad.
  - exact Hhull.
  - exact Hsrc. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hd2 & Heff & Hfr & Hpres & Hsm).
replace (sp0 + (spZ (ms_regs ms) - sp0)) with (spZ (ms_regs ms)) in Hfr by lia.
apply K; try assumption.
pose proof (st_ok_after_call tfibsegs kk E ss (restrict (w_H W) ms) regs2 (mrestrict (w_H W) mem2) rs retpc HS Hrv Hat Hwf Hnc Hmat Hsub Hra)
  as HS2.
rewrite restrict_mkst_fx. apply HS2.
- intros r Hr. exact (HP r Hr).
- rewrite Forall_forall in Hkeep |- *. intros r Hin. destruct (Hkeep r Hin) as (Hb & Hlo & Hhi).
  cbn [ms_mem restrict].
  apply (cw_region_kept_out E (w_H W) (ms_mem ms) mem2 (fun a => (d <= a < d + n) \/ (spZ (ms_regs ms) - ESTACK <= a < spZ (ms_regs ms))) r);
    [ | exact Hpres | exact Hb | exact Hlo | exact Hhi ].
  intros a Ha Hz. apply Hfr; [exact Ha | intros H1; apply Hz; left; exact H1 | intros H1; apply Hz; right; exact H1].
Qed.
End i.
