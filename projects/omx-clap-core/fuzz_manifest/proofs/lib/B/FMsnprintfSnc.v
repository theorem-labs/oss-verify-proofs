(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copy of A/AE2b.v (fwr_check_srr) re-instanced at the vsnprintf interceptor's WRITE_RANGE check (RC_ENTRY 0x44ea0 -> RC_END 0x44ef8; the shadow loads at 0x44ee8/0x44eec), over code table tbl_vsn (tbl_icpt plus 0x44dfc..0x45114), with x19 = size >= n (slow path `bnez s3`) and x10 = res kept, stated over Poison's ARU (any U); theorem vsn_wr_check_srrU. *)
(* Modified by Theorem Labs, 2026-10: relocated to fm.asan (module paths, addresses, code table over 0x458a0); entered at 0x45a18 (the size >= res + 1 path); icpt_rodata_okU copied from FMpfsU.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGwrc.v; 74 of its 122 lines of code are new or changed and 2714 lines of the source are left out. *)
(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfSnc.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* ARU forms of the memchr interceptor contract that the strnlen walks call (A/YE39.v amemchr0_realizesM with Poison's
   ARU in and out), the not-found form, and the facts the ARU ports of A/AE6x, AE6y, AE7d, AE7e, YE7f share. The range
   premises stay on the real memory `mem`, because the interceptors' shadow checks and musl's loads read it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YE34 YF0l YE3e YE3f YE3g YE6g YE39 YE2p YE3i YE3h YF0m YE22 YF0x YE20 YE2y YE7f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* memchr(x, 0, n) interceptor, NUL found at k with k + 8 <= n: A/YE39.v amemchr0_realizesM with ARU in and out. *)
Definition amemchr0_realizesU (B : asyms) (pc : Z) : Prop :=
forall ly S U W regs mem md x n k,
ecall_preU tfibsegs B ly S U W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 63 -> 0 < x ->
0 <= k -> k + 8 <= n -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
first_byte tfibsegs W mem x n 0 k ->
src_ok tfibsegs W regs mem x (k + 1) -> amem_range x (k + 1) ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x (k + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x (k + 1) ->
(forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview tfibsegs (w_H W) mem a <> None) ->
mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (x + k) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* memchr(x, 0, n) interceptor, no 0 byte among the first n (the %.*s case): it returns NULL and reads exactly
   x .. x + n - 1, so there is no tail-of-granule premise. *)
Definition amemchr0N_realizesU (B : asyms) (pc : Z) : Prop :=
forall ly S U W regs mem md x n,
ecall_preU tfibsegs B ly S U W regs mem md ->
getr regs 10 = w64 x -> getr regs 11 = w64 0 -> getr regs 12 = w64 n -> 1 <= n < 2 ^ 31 -> 0 < x -> x + n <= 2 ^ 63 ->
first_byte tfibsegs W mem x n 0 n ->
src_ok tfibsegs W regs mem x n -> amem_range x n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF x n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) x n ->
mconsts_view W mem ->
SRr tfibsegs W (cfg_at tfibsegs pc regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
ARU tfibsegs B ly S U W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - ESTACK <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* The image constants (icpt_rodata and the interceptors' GOT cells) are cells below SHADOW_OFF, where `unpoison U mem`
   reads `mem`. The same two facts as FMpfsU.v's ro_low / ro_region_low. *)
Definition ro_low (l : list (Z * Z * list (Z * N * Z))) : bool :=
forallb (fun r => forallb (fun c => (0 <=? fst (fst r) + fst (fst c)) &&
(fst (fst r) + fst (fst c) + Z.of_N (snd (fst c)) <=? SHADOW_OFF)) (snd r)) l.
Lemma ro_region_low : forall l E (m m' : word -> option byte), ro_low l = true ->
(forall w : word, bv_unsigned w < SHADOW_OFF -> m' w = m w) ->
Forall (region_ok tfibsegs E m) (map ro_region l) -> Forall (region_ok tfibsegs E m') (map ro_region l).
Proof.
intros l E m m' Hl Hm HF. unfold ro_low in Hl. rewrite forallb_forall in Hl.
rewrite Forall_forall in HF. apply Forall_map. rewrite Forall_forall. intros [[base sz] cs] Hin.
specialize (Hl _ Hin). specialize (HF _ (in_map ro_region _ _ Hin)). cbn [fst snd] in Hl. rewrite forallb_forall in Hl.
destruct HF as (B1 & B2 & Hw & Hc).
unfold ro_region, region_ok in *. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *.
split; [exact B1|]. split; [exact B2|]. split; [intros o Ho; exfalso; lia|].
rewrite Forall_forall in Hc. apply Forall_map. rewrite Forall_forall. intros [[off n] v] Hc'.
specialize (Hl _ Hc'). specialize (Hc _ (in_map (ro_chunk base) _ _ Hc')). cbn [fst snd] in Hl. apply andb_prop in Hl as [L1 L2].
apply Z.leb_le in L1. apply Z.leb_le in L2.
intros i Hi. destruct (Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
unfold ro_chunk, c_len in *. cbn [YP09.c_off YP09.c_val cv_len fst snd] in *.
unfold mbyte in *. rewrite Hm; [exact Hb2|]. unfold SHADOW_OFF in *. rewrite unsigned_lit_small by lia. lia.
Qed.
(* rodata_ok (A/YE34.v) under ARU, for any list of image cells below SHADOW_OFF. *)
Lemma rodata_okU : forall B, TfibSyms B -> forall l ly S U W mem md E, rodata_chk ly l = true -> ro_low l = true ->
ARU tfibsegs B ly S U W mem md -> Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) (map ro_region l).
Proof.
intros B TB l ly S U W mem md E Hc Hl HAR.
apply (ro_region_low l E (mrestrict (w_H W) (unpoison U mem))); [exact Hl | |].
- intros w Hw. unfold mrestrict. rewrite (ARU_mem_low tfibsegs B ly S U W mem md w HAR Hw). reflexivity.
- exact (rodata_ok B TB l ly S (w_H W) (unpoison U mem) E Hc (ARU_ARm tfibsegs B ly S U W mem md HAR)).
Qed.
(* Above the shadow (the stack) the memory is the allocator's too. *)
Lemma ARU_mem_high : forall B ly S U W mem md (w : word), ARU tfibsegs B ly S U W mem md -> kHighMemBeg <= bv_unsigned w ->
unpoison U mem w = mem w.
Proof.
intros B ly S U W mem md w H Hw. apply unpoison_out. destruct (in_ush U (bv_unsigned w)) eqn:E; [|reflexivity].
exfalso. pose proof (ush_facts tfibsegs B ly S U W mem md _ H E) as (_ & _ & L). lia.
Qed.
Lemma ARU_apresent_stack : forall B ly S U W mem md a, ARU tfibsegs B ly S U W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly ->
(apresent (w_H W) (unpoison U mem) a <-> apresent (w_H W) mem a).
Proof.
intros B ly S U W mem md a H Ha.
pose proof (stk_kHighMemBeg B ly S _ (ARU_ARm tfibsegs B ly S U W mem md H)) as [K1 K2].
assert (E : unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ apply (ARU_mem_high B ly S U W mem md _ H). rewrite unsigned_lit_small by (unfold kHighMemBeg, kHighMemEnd in *; lia). lia. }
unfold apresent. rewrite E. reflexivity.
Qed.
(* ecall_preU, with the stack-window presence read on the real memory. *)
Lemma ecall_preU_parts : forall B ly S U W regs mem md, ecall_preU tfibsegs B ly S U W regs mem md ->
ARU tfibsegs B ly S U W mem md /\ ret_ok (getr regs 1) /\ spZ regs mod 16 = 0 /\ ly_stk_lo ly + ESTACK <= spZ regs /\
spZ regs <= ly_stk_hi ly /\ (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
Proof.
intros B ly S U W regs mem md ((HAR & Hra & Hal & Hlo & Hhi & Hp & Hgp & Htp) & OK & PO).
assert (HU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; [exact OK | exact PO]]).
split; [exact HU|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [|split; [exact Hgp | exact Htp]].
intros a Ha. apply (ARU_apresent_stack B ly S U W mem md a HU); [unfold ESTACK in *; lia|]. exact (Hp a Ha).
Qed.
Lemma ecall_preU_intro : forall B ly S U W regs mem md,
ARU tfibsegs B ly S U W mem md -> ret_ok (getr regs 1) -> spZ regs mod 16 = 0 -> ly_stk_lo ly + ESTACK <= spZ regs ->
spZ regs <= ly_stk_hi ly -> (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> ecall_preU tfibsegs B ly S U W regs mem md.
Proof.
intros B ly S U W regs mem md HU Hra Hal Hlo Hhi Hp Hgp Htp. pose proof HU as (HAR & OK & PO).
split; [|split; [exact OK | exact PO]].
split; [exact HAR|]. split; [exact Hra|]. split; [exact Hal|]. split; [exact Hlo|]. split; [exact Hhi|].
split; [|split; [exact Hgp | exact Htp]].
intros a Ha. apply (ARU_apresent_stack B ly S U W mem md a HU); [unfold ESTACK in *; lia|]. exact (Hp a Ha).
Qed.
End c.
