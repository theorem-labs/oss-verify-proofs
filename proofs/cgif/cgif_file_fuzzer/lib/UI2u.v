(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YL0g YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c YL0h UI2t YI09 UI21 UI22 UI0l.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition llvm_specV (pc empty stk : Z) : Prop :=
forall L A regs mem md p n (PAYLOAD : list Z),
fn_pre ubs0_msyms MR stk L A regs mem md ->
st_init_done A = true ->
sink_none ubs0_msyms mem md -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
((n = 0 /\ p = empty) \/ (0 < n /\ In (p, n) (blocks L A))) ->
garr8 ubs0segs mem p PAYLOAD -> Z.of_nat (length PAYLOAD) = n ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR stk (spZ regs) [sink_token] L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\
st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
sink_none ubs0_msyms mem' md' /\
(forall b, In b (blocks L A) -> In b (blocks L' A')) /\
(Fs.fs_sorted (m_fs md) = true ->
ff_key (Fs.fs_lookup (m_fs md) sink_path) PAYLOAD (Fs.fs_lookup (m_fs md') sink_path))).
Definition rfc_specV : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (Bb : list (Z * Z)) (st dst N pdata nb cur : Z) (PAYLOAD : list Z),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
(forall b, In b (blocks L A) -> In b Bb) -> Permutation (blocks Lc Ac) Bb -> In (pdata, nb) Bb ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 10 = Z_to_bv 64 st -> getr regs 11 = Z_to_bv 64 dst -> getr regs 12 = Z_to_bv 64 N ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RFC_STK -> spZ regs <= st -> st + 24 <= sp0 ->
spZ regs <= dst -> dst + 32 <= sp0 -> (st + 24 <= dst \/ dst + 32 <= st) -> st mod 8 = 0 -> dst mod 8 = 0 -> sp0 < 2 ^ 63 ->
1 <= N <= 100000000 -> 0 <= cur <= nb -> 0 < nb ->
word_mem ubs0segs memc st pdata -> word_mem ubs0segs memc (st + 8) nb -> word_mem ubs0segs memc (st + 16) cur ->
garr8 ubs0segs memc pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_read_frameconfig) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res cur2 : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - RFC_STK <= a < spZ regs) -> ~ (dst <= a < dst + 32) -> ~ (st + 16 <= a < st + 24) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\
(forall b m i, In (b, m) Bb -> 0 <= i < m -> mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs memc (b + i)) /\
word_mem ubs0segs mem2 st pdata /\ word_mem ubs0segs mem2 (st + 8) nb /\
word_mem ubs0segs mem2 (st + 16) cur2 /\ cur <= cur2 <= nb /\
((res = 0 /\ exists leak, Permutation (blocks L2 A2) (leak ++ Bb)) \/
(res = 1 /\ exists lpal lpa img fattr fgen delay nlp tidx (LPAL IMG : list Z),
obj_at ubs0segs mem2 dst LAY_FrameConfig [lpal; img; fattr; fgen; delay; nlp; tidx] /\
(Z.land fattr 1 = 0 -> lpal = 0) /\ Z_to_bv 64 lpa = Z_to_bv 64 lpal /\
Permutation (blocks L2 A2) ((img, N) :: (if Z.land fattr 1 =? 0 then [] else [(lpa, 3 * nlp)]) ++ Bb) /\
parse_frameN N (skipn (Z.to_nat cur) PAYLOAD) = (true, (fattr, fgen, delay, tidx, nlp, LPAL, IMG), skipn (Z.to_nat cur2) PAYLOAD) /\
garr8 ubs0segs mem2 img IMG /\ Z.of_nat (length IMG) = N /\
(Z.land fattr 1 <> 0 -> garr8 ubs0segs mem2 lpa LPAL /\ Z.of_nat (length LPAL) = 3 * nlp)))).
Lemma llvm_spec_of_V : forall pc empty stk, llvm_specV pc empty stk -> llvm_spec API pc empty stk.
Proof using.
intros pc empty stk HV L A regs mem md p n HPRE Hid HSN Hsp Ha0 Ha1 Hpn.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HP : exists PAYLOAD, garr8 ubs0segs mem p PAYLOAD /\ Z.of_nat (length PAYLOAD) = n).
{ destruct Hpn as [[-> _] | [Hn Hin]]; [exists []; split; [apply garr8_nil | reflexivity]|].
destruct HPRE as (HH & _).
destruct (garr8_of_present ubs0segs mem p (Z.to_nat n) ltac:(intros a Ha; replace a with (p + (a - p)) by lia;
apply (proj1 (heap_blocks _ _ (aa_laws API) L A mem md p n (a - p) HH Hin ltac:(lia))))) as (l & Hlen & Hl).
exists l. split; [exact Hl | rewrite Hlen; lia]. }
destruct HP as (PAYLOAD & HG & HL).
eapply SR_mono; [exact (HV L A regs mem md p n PAYLOAD HPRE Hid HSN Hsp Ha0 Ha1 Hpn HG HL)|].
cbv beta. intros c' (L' & A' & regs' & mem' & md' & E & HJ & HPr & Hid' & Hr & HSN' & Hbl & _).
exists L', A', regs', mem', md'. repeat (split; [assumption|]). exact Hbl.
Qed.
End d.
End c.
