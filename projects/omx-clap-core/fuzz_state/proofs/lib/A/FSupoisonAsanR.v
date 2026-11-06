(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE2q.v, with its module paths changed, names TfibSyms -> BoxregSyms and its addresses moved to libreac/fuzz_boxreg's ASan build. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/AE2q.v, with its module paths changed; 96 of its 126 lines of code are new or changed and 130 lines of the source are left out. *)
(* fuzz_state image A (fuzz_state.asan): the __asan_memcpy walk under the ARU invariant (lib/A/FSupoison.v), any U
   (POISON-U lane; the statement is lib/A/FSupoisonU.v aintrin_realizesU OCpy at A's PC_memcpy 0x51d20): the walk's
   REGION CONDITION as one named lemma, plus the transfers the walk needs between the two readings of memory.
   Port-from: lib/A/FSupoisonIntrinR.v (image A, the memcpy interceptor walk), restated with AE6k.MC_SCR; text
   unchanged otherwise. The image-free helpers are restated here, not imported from FSupoisonIntrinR, so that this
   file and lib/B/FSupoisonAsanR.v (a working branch 269685bdc74) are one text modulo image modules.

   The walk is S0's lib/A/AE6k.v + AE6l .. AE6s + AE2q.v (U = [] form: AE2q.v:143 asan_memcpy_realizes), ported over
   FSupoison.ecall_preU in lib/A/FSupoisonAsanC.v. The machine runs on mem, where U's shadow bytes read 0xf7; the AR
   that ecall_preU carries holds of FSupoison.unpoison U mem, where they read 0.

   - asan_memcpy_regions_off_ush: every byte that a region of this walk fixes (the stack window [sp - MC_SCR, sp)
     below sp (MC_SCR = 2216, AE6k.v:837), the image's read-only cells icpt_rodata, which include the REAL(memcpy)
     cell 0xa1568 that holds musl memcpy 0x98a20 (AB1w tfib_A_memcpy, AE6k MC_REAL), the shadow bytes of the
     granules of the destination range and of the source range) is outside U's shadow bytes: FSupoison.in_ush U is
     false there. Its premises are premises of aintrin_realizesU itself (ecall_preU, 0 <= d, 0 <= x, the two
     range_addressable), so any real __asan_memcpy call state witnesses them; no new bound is introduced.
   - ro_regions_off: the read-only cells' region_ok, moved from the unpoisoned reading (which AR gives) to the real
     one (which the symbolic state needs). stack_present: the stack window's apresent on the real memory.
   - Which part the walk consumes: the stack and shadow regions are built from the contract's premises, which are
     already stated on aview mem (the real memory), so they need no transfer; only the read-only cells come from AR.
   - The REAL(memcpy) call (AE6k.v mc_tail, `jalr` 0x51e18 to musl memcpy 0x98a20) reads [x, x + n) and writes
     [d, d + n): application memory (amem_range), never shadow, so never a byte of U's shadow; FSupoison.ARU_frame
     takes the write.
   - Bytes the walk READS outside any region: the QuickCheckForUnpoisonedRegion fast path (n <= 64) loads the two
     8-byte aligned shadow words around shadow(p) and shadow(p + n - 1) in __asan_memcpy (A; capstone 5.0.7 on the
     unstripped twin): the source loads `ld` 0x51db8 / 0x51dbc, which AE6k resumes after at 0x51dbc / 0x51dc0
     (q1_*_s3), the destination loads `ld` 0x51e00 / 0x51e04, resumed after at 0x51e04 / 0x51e08 (w1_*_s3); the
     r_q1_*_2 / r_w1_*_2 runs stop at SR_addr there. Such a word can contain a shadow byte of U (a neighbouring
     granule's poisoned head). The walk takes those two words as FRESH atoms read from aview mem and proves both
     branches of the zero test, so it holds for whatever the real memory has there; no premise about those bytes is
     needed, and none is added. The n > 64 path's __asan_region_is_poisoned / mem_is_zero reads (return 0x54d58) lie
     in the shadow span of the range, which this lemma covers. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3c AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require AE6k FSupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14 YI16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* A byte of the image's read-only cells the walk reads (AE2y.v:68 icpt_rodata, one region each). *)
Definition icpt_ro_byte (a : Z) : Prop := exists e, In e icpt_rodata /\ fst (fst e) <= a < fst (fst e) + snd (fst e).
(* A shadow byte of a granule of [p, p + n): the bytes AE6k.v's shreg1 / shregs2 regions fix, and the mem_is_zero
   range inside them. *)
Definition shadow_span (p n a : Z) : Prop := 0 < n /\ SB + p / 8 <= a <= SB + (p + n - 1) / 8.
(* The bytes the __asan_memcpy walk's regions fix: its stack window [sp - MC_SCR, sp) (AE6k.v:837 MC_SCR = 2216; stkS
   and stkD reach sp - MC_STK = sp - 2208), the read-only cells, the source and the destination shadow span. *)
Definition asan_memcpy_fixed (sp d x n a : Z) : Prop :=
  (sp - AE6k.MC_SCR <= a < sp) \/ icpt_ro_byte a \/ shadow_span x n a \/ shadow_span d n a.
Lemma unpoison_off : forall U (mem : word -> option byte) a, 0 <= a < 2 ^ 64 -> FSP.in_ush U a = false ->
  FSP.unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof. intros U mem a Ha E. apply FSP.unpoison_out. rewrite (FSP.wz a Ha). exact E. Qed.
Section r.
Variable B : asyms.
Lemma low_off_ush : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md -> a < SHADOW_OFF ->
  FSP.in_ush U a = false.
Proof.
intros ly S U W mem md a H Ha. destruct (FSP.in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (FSP.ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L & _). lia.
Qed.
Lemma high_off_ush : forall ly S U W mem md a, FSP.ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= a ->
  FSP.in_ush U a = false.
Proof.
intros ly S U W mem md a H Ha. destruct (FSP.in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (FSP.ush_facts tfibsegs B ly S U W mem md a H E) as (_ & _ & L). lia.
Qed.
(* The read-only cells lie in the image, i.e. below the shadow; the bound is kLowMemEnd (YG0f.v:17), never a
   literal, so a relocation of icpt_rodata changes nothing here. *)
Lemma ro_byte_low : forall a, icpt_ro_byte a -> 0 <= a < kLowMemEnd.
Proof.
intros a (e & He & Ha). unfold kLowMemEnd. cbn in He. repeat (destruct He as [<-|He]; [cbn in Ha; lia|]). destruct He.
Qed.
(* A shadow byte of a granule of an addressable range never reads 0xf7, so it is not one of U's: saddr_ok forbids it. *)
Lemma span_off_ush : forall U (W : world tfibsegs) mem p n a, FSP.upoisoned tfibsegs W mem U ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n -> 0 <= p -> shadow_span p n a ->
  FSP.in_ush U a = false.
Proof.
intros U W mem p n a PO HRA Hp (Hn & A1 & A2).
destruct (FSP.in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (PO a E) as P247.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dp. pose proof (Z.mod_pos_bound p 8 ltac:(lia)) as Mp.
pose proof (Z.div_mod (p + n - 1) 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound (p + n - 1) 8 ltac:(lia)) as Mq.
assert (Hb : exists b, p <= b < p + n /\ b / 8 = a - SB).
{ destruct (Z.eq_dec (a - SB) (p / 8)) as [Eg|Eg].
  - exists p. split; [lia | symmetry; exact Eg].
  - exists (8 * (a - SB)). split; [lia|]. rewrite Z.mul_comm. apply Z.div_mul. lia. }
destruct Hb as (b & Hb & Hbg).
destruct (HRA b Hb) as (s & Hs & Hok). unfold shadow_of_addr in Hs. rewrite Hbg in Hs.
replace (SHADOW_OFF + (a - SB)) with a in Hs by (rewrite <- SB_eq; lia).
rewrite P247 in Hs. injection Hs as <-. destruct Hok as [Hz | [_ Hs8]]; lia.
Qed.
(* a Theorem Labs lane's region condition for the __asan_memcpy walk (lib/A/AE6k.v + AE6l .. AE6s + AE2q.v). *)
Lemma asan_memcpy_regions_off_ush : forall ly S U W regs mem md d x n,
  FSP.ecall_preU tfibsegs B ly S U W regs mem md -> 0 <= d -> 0 <= x ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
  forall a, asan_memcpy_fixed (spZ regs) d x n a -> FSP.in_ush U a = false.
Proof.
intros ly S U W regs mem md d x n HPRE Hd Hx HRA HRAX a Ha.
pose proof HPRE as ((HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & HOK & HPO).
assert (HARU : FSP.ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact HOK | exact HPO]]).
destruct Ha as [Hs | [Hro | [Hsx | Hsd]]].
- pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
  pose proof (lo_top ly HLY) as (_ & _ & _ & _ & _ & _ & Lbeg).
  apply (high_off_ush ly S U W mem md a HARU). unfold AE6k.MC_SCR, ESTACK in *. lia.
- apply (low_off_ush ly S U W mem md a HARU). pose proof (ro_byte_low a Hro). unfold SHADOW_OFF, kLowMemEnd in *. lia.
- exact (span_off_ush U W mem x n a HPO HRAX Hx Hsx).
- exact (span_off_ush U W mem d n a HPO HRA Hd Hsd).
Qed.
(* ecall_pre gives the stack window present in unpoison U mem; U is not there, so it is present in the real mem. *)
Lemma stack_present : forall ly S U W regs mem md, FSP.ecall_preU tfibsegs B ly S U W regs mem md ->
  forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a.
Proof.
intros ly S U W regs mem md HPRE a Ha.
pose proof HPRE as ((HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp) & HOK & HPO).
assert (HARU : FSP.ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact HOK | exact HPO]]).
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY.
pose proof (lo_top ly HLY) as (_ & _ & _ & Lhi & _ & _ & Lbeg).
apply (AF0x.apresent_same (w_H W) (FSP.unpoison U mem) mem a); [|exact (HpresE a Ha)].
symmetry. apply unpoison_off; [unfold kHighMemBeg, kHighMemEnd, ESTACK in *; lia|].
apply (high_off_ush ly S U W mem md a HARU). unfold kHighMemBeg, ESTACK in *. lia.
Qed.
Section t.
Hypothesis TB : TfibSyms B.
(* The image's read-only cells from AR (on unpoison U mem), moved to a memory m that agrees with mem on the low
   image: the walk's icpt_rodata region_ok. Port-from: lib/A/AE6k.v:1377-1394 (entD_ro), generalised in m. *)
Lemma ro_regions_off : forall ly S U W mem md E (m : word -> option byte),
  FSP.ARU tfibsegs B ly S U W mem md -> (forall a, icpt_ro_byte a -> FSP.in_ush U a = false) ->
  (forall a, 0 <= a < kLowMemEnd -> m (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  Forall (region_ok tfibsegs E (mrestrict (w_H W) m)) (map ro_region icpt_rodata).
Proof.
intros ly S U W mem md E m HARU OFF MEQ.
pose proof (proj1 (proj1 HARU)) as BM.
pose proof (icpt_rodata_ok B TB ly S (w_H W) (FSP.unpoison U mem) E BM) as F0.
assert (WF : regions_wf (map ro_region icpt_rodata) = true) by (vm_compute; reflexivity).
apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) F0 r Hr) as Hr0.
pose proof (regions_wf_In _ r WF Hr) as Hwf. apply region_wf_facts in Hwf as (_ & _ & Hci).
assert (Hlit : exists e, In e icpt_rodata /\ r = ro_region e) by (apply in_map_iff in Hr as (e & <- & He); exists e; auto).
destruct Hlit as (e & He & ->).
eapply (region_ok_transport tfibsegs E E); [exact Hr0 | reflexivity | | | | exact Hci].
- intros c Hc. unfold ro_region in Hc. cbn [YP09.r_chunks] in Hc. apply in_map_iff in Hc as (cc & <- & _). cbn. reflexivity.
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha.
  assert (Hro : icpt_ro_byte a) by (exists e; split; [exact He | lia]).
  pose proof (ro_byte_low a Hro) as Hlow.
  apply AF0x.mbyte_mrestrict_same. rewrite (MEQ a Hlow). symmetry. apply unpoison_off; [unfold kLowMemEnd in Hlow; lia | exact (OFF a Hro)].
- intros a Ha. unfold ro_region in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia.
Qed.
End t.
End r.
End f.
