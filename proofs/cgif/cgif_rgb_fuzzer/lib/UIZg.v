(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h UI3d
UI39 UI2p UI26 UI57 UI58 UI4y UO0e UIZe UIZf.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Definition rl_hdr_post (regs0 : bvmap 5 word) L A mem md (p n : Z) (c' : config) : Prop :=
exists regs1 memc,
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md L A memc md /\
rsaved_ok memc (spZ regs0) regs0 /\
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 128) /\ runtouched_ok regs0 regs1 /\
((n < 14 /\ c' = mkCfg (mkst regs1 (Z_to_bv 64 RL_RET0) memc (seg_rom ubs2segs)) md) \/
(14 <= n /\ c' = mkCfg (mkst regs1 (Z_to_bv 64 RL_MUL) memc (seg_rom ubs2segs)) md /\
exists attr gen loops W H, 0 <= W < 65536 /\ 0 <= H < 65536 /\
word_mem ubs2segs memc (spZ regs0 - 120) p /\ word_mem ubs2segs memc (spZ regs0 - 112) n /\
word_mem ubs2segs memc (spZ regs0 - 104) 14 /\
obj_at ubs2segs memc (spZ regs0 - 72) LAY_RgbConfig [0; 0; 0; attr; gen; loops; W; H])).
Definition ss_hdr0 : sstate :=
mkSS RLLVM sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-128) (-72) (-128) (-72) [] ;
YQ0b.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [] ]
None (mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB) (2^63) 4) ] [] []).
Definition hinv (sp0 : Z) (regs : bvmap 5 word) (p n cur : Z) (m : word -> option byte) : Prop :=
rsaved_ok m sp0 regs /\ word_mem ubs2segs m (sp0 - 120) p /\ word_mem ubs2segs m (sp0 - 112) n /\
word_mem ubs2segs m (sp0 - 104) cur /\
(forall i, 0 <= i < 24 -> mbyte ubs2segs m (sp0 - 72 + i) = Some (Z_to_bv 8 0)) /\
(forall a, sp0 - 48 <= a < sp0 - 32 -> exists b, mbyte ubs2segs m a = Some b).
Lemma hinv_frame0 : forall E sp0 regs p n cur (m m' : word -> option byte),
frame_of E [] m m' -> hinv sp0 regs p n cur m -> hinv sp0 regs p n cur m'.
Proof.
intros E sp0 regs p n cur m m' HF ((R1 & R2 & R3 & R4) & W1 & W2 & W3 & Hz0 & Bs).
assert (Hm : forall a, mbyte ubs2segs m' a = mbyte ubs2segs m a).
{ intros a. unfold mbyte. rewrite HF; [reflexivity|]. intros (r & Hr & _). destruct Hr. }
assert (WK : forall a v, word_mem ubs2segs m a v -> word_mem ubs2segs m' a v).
{ intros a v W i Hi. rewrite Hm. apply W. exact Hi. }
split; [split; [apply WK; exact R1 | split; [apply WK; exact R2 | split; apply WK; assumption]] |].
split; [apply WK; exact W1|]. split; [apply WK; exact W2|]. split; [apply WK; exact W3|].
split; [intros i Hi; rewrite Hm; apply Hz0; exact Hi | intros a Ha; rewrite Hm; apply Bs; exact Ha].
Qed.
Lemma hinv_after_memset : forall sp0 regs p n (m m2 : word -> option byte),
0 <= sp0 - 128 -> sp0 < 2 ^ 63 ->
rsaved_ok m sp0 regs -> word_mem ubs2segs m (sp0 - 120) p -> word_mem ubs2segs m (sp0 - 112) n ->
word_mem ubs2segs m (sp0 - 104) 0 ->
(forall x : word, bv_unsigned x < sp0 - 72 \/ sp0 - 72 + 40 <= bv_unsigned x -> m2 x = m x) ->
(forall i, 0 <= i < 40 -> mbyte ubs2segs m2 (sp0 - 72 + i) = Some (Z_to_bv 8 0)) ->
hinv sp0 regs p n 0 m2.
Proof.
intros sp0 regs p n m m2 H0 H1 (R1 & R2 & R3 & R4) W1 W2 W3 Hout Hz.
assert (WK : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> a + 8 <= sp0 - 72 \/ sp0 - 72 + 40 <= a ->
word_mem ubs2segs m a v -> word_mem ubs2segs m2 a v).
{ intros a v Ha0 Ha1 Hr W. apply word_mem_frame with (m := m); [exact W|]. intros i Hi.
unfold mbyte. rewrite Hout; [reflexivity|]. rewrite unsigned_lit_small by lia. lia. }
split. { split; [|split; [|split]]; (apply WK; [lia | lia | lia | assumption]). }
split. { apply WK; [lia | lia | lia | exact W1]. }
split. { apply WK; [lia | lia | lia | exact W2]. }
split. { apply WK; [lia | lia | lia | exact W3]. }
split. { intros i Hi. apply Hz. lia. }
intros a Ha. exists (Z_to_bv 8 0). replace a with (sp0 - 72 + (a - (sp0 - 72))) by lia. apply Hz. lia.
Qed.
Lemma rd_call : forall sp0 L A mem md memc mdc (rg : bvmap 5 word) regs p n cur dst k,
journal ubs2_msyms MR LIB_STACK_RGB sp0 [] L A mem md L A memc mdc ->
getr rg 2 = Z_to_bv 64 (sp0 - 128) -> getr rg 10 = Z_to_bv 64 (sp0 - 120) ->
getr rg 11 = Z_to_bv 64 dst -> getr rg 12 = Z_to_bv 64 k -> YK0s.ret_ok (getr rg 1) ->
1 <= k <= 4 -> sp0 - 48 <= dst -> dst + k <= sp0 - 32 -> 0 <= cur <= n -> n < 2 ^ 63 ->
(cur + k <= n -> In (p, n) (blocks L A)) ->
hinv sp0 regs p n cur memc ->
SR ubs2segs (mkCfg (mkst rg (Z_to_bv 64 ubs2_A_readdata) memc (seg_rom ubs2segs)) mdc)
(fun c' => exists rg2 mem2,
c' = mkCfg (mkst rg2 (getr rg 1) mem2 (seg_rom ubs2segs)) mdc /\
journal ubs2_msyms MR LIB_STACK_RGB sp0 [] L A mem md L A mem2 mdc /\
regs_preserved rg rg2 /\
((cur + k <= n /\ getr rg2 10 = Z_to_bv 64 0 /\ hinv sp0 regs p n (cur + k) mem2) \/
(n < cur + k /\ getr rg2 10 = Z_to_bv 64 (2 ^ 64 - 1) /\ hinv sp0 regs p n n mem2))).
Proof.
intros sp0 L A mem md memc mdc rg regs p n cur dst k HJ R2 R10 R11 R12 Rra Hk1 Hd0 Hd1 Hc Hn63 Hblk HI.
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HLSv : LIB_STACK_RGB = ltac:(let v := eval vm_compute in LIB_STACK_RGB in exact v)) by reflexivity.
pose proof HJ as (HH & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & H63 & Hstw) & _).
assert (Hspz : spZ rg = sp0 - 128) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
pose proof HI as ((R1 & R3 & R4 & R5) & Wp & Wn & Wc & Hz & Bs).
eapply SR_bind.
{ eapply (ubs2_readdata API IMG LIB_STACK_RGB sp0 [] L A mem md L A memc mdc rg (sp0 - 120) dst k p n cur);
[ exact HJ | exact Rra
| rewrite Hspz; replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16
| rewrite Hspz; unfold RD_STK; lia | rewrite Hspz; lia | lia
| pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16; replace (sp0 - 120) with ((2 * (sp0 / 16) - 15) * 8) by lia; apply Z_mod_mult
| exact R10 | exact R11 | exact R12 | unfold RD_NMAX; lia | lia | lia
| exact Wp | replace (sp0 - 120 + 8) with (sp0 - 112) by lia; exact Wn
| replace (sp0 - 120 + 16) with (sp0 - 104) by lia; exact Wc | intros Hfit ].
specialize (Hblk Hfit).
destruct (blocks_range _ _ LAWS L A memc mdc p n HH Hblk) as [Hp0 Hp1].
rewrite Hspz. unfold RD_STK.
split; [lia|]. split; [lia|]. split.
{ intros i Hi. replace (p + cur + i) with (p + (cur + i)) by lia.
exact (proj1 (heap_blocks _ _ LAWS L A memc mdc p n (cur + i) HH Hblk ltac:(lia))). }
split; [lia|]. split; [lia|]. split.
{ intros i Hi. apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia]. }
split; [intros a Ha; left; lia|].
split; [right; lia|]. split; [right; lia|]. right; lia. }
cbv beta. intros c' (rg2 & mem2 & -> & HJ2 & HP2 & Hcase & Hout).
apply SR_ret. exists rg2, mem2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
rewrite Hspz in Hout. unfold RD_STK in Hout.
assert (WK : forall a v, sp0 - 128 <= a -> a + 8 <= sp0 -> a + 8 <= sp0 - 104 \/ sp0 - 96 <= a ->
a + 8 <= dst \/ dst + k <= a -> word_mem ubs2segs memc a v -> word_mem ubs2segs mem2 a v).
{ intros a v Ha0 Ha1 Ha2 Ha3 W. apply word_mem_frame with (m := memc); [exact W|]. intros i Hi.
apply Hout; [lia | lia | lia | intros [_ Hx]; lia]. }
assert (HZ : forall i, 0 <= i < 24 -> mbyte ubs2segs mem2 (sp0 - 72 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. rewrite Hout; [apply Hz; exact Hi | lia | lia | lia | intros [_ Hx]; lia]. }
destruct Hcase as [(Hfit & R10' & Wc2 & Hcp) | (Hno & R10' & Wc2)].
- left. split; [exact Hfit|]. split; [exact R10'|].
split. { split; [|split; [|split]]; (apply WK; [lia | lia | lia | lia | assumption]). }
split. { apply WK; [lia | lia | lia | lia | exact Wp]. }
split. { apply WK; [lia | lia | lia | lia | exact Wn]. }
split. { replace (sp0 - 104) with (sp0 - 120 + 16) by lia. exact Wc2. }
split. { exact HZ. }
intros a Ha. destruct (Z_lt_ge_dec a dst) as [H1|H1]; [|destruct (Z_lt_ge_dec a (dst + k)) as [H2|H2]].
+ rewrite Hout; [apply Bs; exact Ha | lia | lia | lia | intros [_ Hx]; lia].
+ destruct (proj1 (heap_blocks _ _ LAWS L A memc mdc p n (cur + (a - dst)) HH (Hblk Hfit) ltac:(lia))) as [b Hb].
exists b. replace a with (dst + (a - dst)) by lia. rewrite Hcp by lia. unfold mbyte.
replace (p + cur + (a - dst)) with (p + (cur + (a - dst))) by lia. rewrite Hb. reflexivity.
+ rewrite Hout; [apply Bs; exact Ha | lia | lia | lia | intros [_ Hx]; lia].
- right. split; [exact Hno|]. split; [exact R10'|].
split. { split; [|split; [|split]]; (apply WK; [lia | lia | lia | lia | assumption]). }
split. { apply WK; [lia | lia | lia | lia | exact Wp]. }
split. { apply WK; [lia | lia | lia | lia | exact Wn]. }
split. { replace (sp0 - 104) with (sp0 - 120 + 16) by lia. exact Wc2. }
split. { exact HZ. }
intros a Ha. rewrite Hout; [apply Bs; exact Ha | lia | lia | lia | intros [Hx _]; lia].
Qed.
Lemma hdr_post_ret0 : forall (regs : bvmap 5 word) L A mem md p n s regs1 memc cur,
s = spZ regs ->
journal ubs2_msyms MR LIB_STACK_RGB s [] L A mem md L A memc md ->
hinv s regs p n cur memc ->
getr regs1 2 = Z_to_bv 64 (s - 128) -> runtouched_ok regs regs1 -> n < 14 ->
rl_hdr_post regs L A mem md p n (mkCfg (mkst regs1 (Z_to_bv 64 RL_RET0) memc (seg_rom ubs2segs)) md).
Proof.
intros regs L A mem md p n s regs1 memc cur -> HJ HI R2 RU Hn.
exists regs1, memc. split; [exact HJ|]. split; [exact (proj1 HI)|]. split; [exact R2|]. split; [exact RU|].
left. split; [exact Hn | reflexivity].
Qed.
Lemma val_mem_present4 : forall segs (m : word -> option byte) a,
(forall i, 0 <= i < 4 -> exists b, mbyte segs m (a + i) = Some b) ->
exists v, 0 <= v < 2 ^ 32 /\ val_mem segs m a 4 v.
Proof.
intros segs m a Hp.
destruct (Hp 0 ltac:(lia)) as [b0 M0]. destruct (Hp 1 ltac:(lia)) as [b1 M1].
destruct (Hp 2 ltac:(lia)) as [b2 M2]. destruct (Hp 3 ltac:(lia)) as [b3 M3].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3.
unfold bv_modulus in R0, R1, R2, R3. cbn [Z.of_N] in R0, R1, R2, R3. change (2 ^ 8) with 256 in R0, R1, R2, R3.
set (v := bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))).
exists v. split; [subst v; lia|].
assert (BY : forall (k : nat) (c : byte) (lo hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YP0g.le_byte v 4 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YP0g.le_byte. rewrite (Z.mod_small v) by (cbn; subst v; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|k]]]]; [| | | |lia];
[ change (a + Z.of_nat 0) with (a + 0) | change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat b0 0 (bv_unsigned b1 + 256 * (bv_unsigned b2 + 256 * bv_unsigned b3))); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat b1 (bv_unsigned b0) (bv_unsigned b2 + 256 * bv_unsigned b3)); cbn; subst v; lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat b2 (bv_unsigned b0 + 256 * bv_unsigned b1) (bv_unsigned b3)); cbn; subst v; lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat b3 (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * bv_unsigned b2)) 0); cbn; subst v; lia.
Qed.
Lemma val_mem_present2 : forall segs (m : word -> option byte) a,
(forall i, 0 <= i < 2 -> exists b, mbyte segs m (a + i) = Some b) ->
exists v, 0 <= v < 2 ^ 16 /\ val_mem segs m a 2 v.
Proof.
intros segs m a Hp.
destruct (Hp 0 ltac:(lia)) as [b0 M0]. destruct (Hp 1 ltac:(lia)) as [b1 M1].
pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1.
unfold bv_modulus in R0, R1. cbn [Z.of_N] in R0, R1. change (2 ^ 8) with 256 in R0, R1.
set (v := bv_unsigned b0 + 256 * bv_unsigned b1).
exists v. split; [subst v; lia|].
assert (BY : forall (k : nat) (c : byte) (lo hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YP0g.le_byte v 2 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YP0g.le_byte. rewrite (Z.mod_small v) by (cbn; subst v; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|k]]; [| |lia]; [ change (a + Z.of_nat 0) with (a + 0) | change (Z.of_nat 1) with 1 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat b0 0 (bv_unsigned b1)); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat b1 (bv_unsigned b0) 0); cbn; subst v; lia.
Qed.
Lemma zero_word_val : forall (m : word -> option byte) a o,
(forall i, 0 <= i < 24 -> mbyte ubs2segs m (a + i) = Some (Z_to_bv 8 0)) -> 0 <= o -> o + 8 <= 24 ->
val_mem ubs2segs m (a + o) 8 0.
Proof.
intros m a o Hz Ho1 Ho2 k Hk. unfold YP0g.le_byte.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by (vm_compute; discriminate)).
replace (a + o + Z.of_nat k) with (a + (o + Z.of_nat k)) by lia. apply Hz. lia.
Qed.
Lemma hdr_post_mul : forall (regs : bvmap 5 word) L A mem md p n s regs1 memc,
s = spZ regs ->
journal ubs2_msyms MR LIB_STACK_RGB s [] L A mem md L A memc md ->
hinv s regs p n 14 memc ->
getr regs1 2 = Z_to_bv 64 (s - 128) -> runtouched_ok regs regs1 -> 14 <= n ->
rl_hdr_post regs L A mem md p n (mkCfg (mkst regs1 (Z_to_bv 64 RL_MUL) memc (seg_rom ubs2segs)) md).
Proof.
intros regs L A mem md p n s regs1 memc -> HJ (RS & Wp & Wn & Wc & Hz & Bs) R2 RU Hn.
exists regs1, memc. split; [exact HJ|]. split; [exact RS|]. split; [exact R2|]. split; [exact RU|].
right. split; [exact Hn|]. split; [reflexivity|].
destruct (val_mem_present4 ubs2segs memc (spZ regs - 72 + 24)) as (attr & Ra & Va); [intros i Hi; apply Bs; lia|].
destruct (val_mem_present4 ubs2segs memc (spZ regs - 72 + 28)) as (gen & Rg & Vg); [intros i Hi; apply Bs; lia|].
destruct (val_mem_present2 ubs2segs memc (spZ regs - 72 + 32)) as (loops & Rl & Vl); [intros i Hi; apply Bs; lia|].
destruct (val_mem_present2 ubs2segs memc (spZ regs - 72 + 34)) as (W & RW & VW); [intros i Hi; apply Bs; lia|].
destruct (val_mem_present2 ubs2segs memc (spZ regs - 72 + 36)) as (H & RH & VH); [intros i Hi; apply Bs; lia|].
exists attr, gen, loops, W, H.
split; [lia|]. split; [lia|]. split; [exact Wp|]. split; [exact Wn|]. split; [exact Wc|].
cbn [obj_at LAY_RgbConfig]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
repeat match goal with |- _ /\ _ => split end; try exact I; try assumption.
all: try (apply zero_word_val; [exact Hz | lia | lia]).
all: try (change (2 ^ (8 * 8)) with (2 ^ 64)); try (change (2 ^ (8 * 4)) with (2 ^ 32)); try (change (2 ^ (8 * 2)) with (2 ^ 16)); lia.
Qed.
Ltac rd_step LW HU2 Hcase HS HJ HI dst k kh :=
jrun_to LW ubs2tbl_ok HS HJ ubs2_A_readdata; [apply wr_ok_nil|];
match goal with HF : frame_of _ [] _ _ |- _ => apply (hinv_frame0 _ _ _ _ _ _ _ _ HF) in HI; clear HF end;
let D10 := fresh "D10" in let D11 := fresh "D11" in let D12 := fresh "D12" in let D2 := fresh "D2" in let D1 := fresh "D1" in
jreg HS (10%bv:reg) as D10; jreg HS (11%bv:reg) as D11; jreg HS (12%bv:reg) as D12;
jreg HS (2%bv:reg) as D2; jreg HS (1%bv:reg) as D1;
rewrite HU2 in D10, D11, D2;
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl); cbn [ss_pc];
eapply SR_bind;
[ lazymatch type of HI with hinv ?s0 ?rgs ?pp ?nn ?cc _ => eapply (rd_call s0 _ _ _ _ _ _ _ rgs pp nn cc dst k HJ) end;
[ rewrite D2; f_equal; lia | rewrite D10; f_equal; lia | rewrite D11; f_equal; lia | exact D12
| rewrite D1; apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia
| intros Hf; destruct Hcase as [[Hn1 _]|[_ Hb]]; [lia | exact Hb] | exact HI ]
| cbv beta; clear HJ HI;
let c' := fresh "c" in let rg2 := fresh "rg" in let m3 := fresh "mem" in let HP := fresh "HP" in let Hcs := fresh "Hcs" in
intros c' (rg2 & m3 & -> & HJ & HP & Hcs);
rewrite D1;
let HS2 := fresh "HS" in
jafter_call_keep HS kh rg2 m3 HP (@nil nat) HS2;
match type of HS2 with ?P -> _ => let HK := fresh "HK" in assert (HK : P) by constructor; specialize (HS2 HK); clear HK end;
clear HS D10 D11 D12 D2 D1 HP; rename HS2 into HS;
let Hfit := fresh "Hfit" in let R10 := fresh "R10" in
destruct Hcs as [(Hfit & R10 & HI) | (Hfit & R10 & HI)];
[ try (exfalso; lia); pin_reg HS (10%bv:reg) 0 R10 | try (exfalso; lia); pin_reg HS (10%bv:reg) (2 ^ 64 - 1) R10 ] ].
Lemma rl_header : forall L A (regs : bvmap 5 word) mem md (p n : Z),
fn_pre ubs2_msyms MR LIB_STACK_RGB L A regs mem md ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n ->
((0 <= n <= 1 /\ 0 <= p < 2 ^ 64) \/ (0 < n /\ In (p, n) (blocks L A))) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs)) md) (rl_hdr_post regs L A mem md p n).
Proof.
intros L A regs mem md p n HPRE G10 G11 Hcase.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac.
assert (HLSv : LIB_STACK_RGB = ltac:(let v := eval vm_compute in LIB_STACK_RGB in exact v)) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
set (E := Ereg regs ([] : list word)).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (Hpn : 0 <= p < 2 ^ 64 /\ 0 <= n < 2 ^ 63).
{ destruct Hcase as [[Hn Hp]|[Hn Hb]]; [lia|]. destruct (blocks_range _ _ LAWS L A mem md p n HH Hb). lia. }
assert (HU10 : bv_unsigned (ew E 10) = p) by (rewrite (HE 10%nat 10%bv eq_refl), G10; apply unsigned_lit_small; lia).
assert (HU11 : bv_unsigned (ew E 11) = n) by (rewrite (HE 11%nat 11%bv eq_refl), G11; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs2segs E ss_hdr0 (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs))).
{ unfold ss_hdr0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil]. intros o Ho. apply Hstw. lia.
+ apply (region_ok_stack ubs2segs _ mem 2 sp0); [exact HU2 | lia | lia |]. intros a Ha. apply Hstw. lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2. repeat split; lia.
- cbn [f_atoms map app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2. change (2 ^ 4) with 16. repeat split; try lia; assumption. }
pose proof (journal_init ubs2_msyms MR LIB_STACK_RGB [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 RLLVM) mem (seg_rom ubs2segs))) in HJ. fold sp0 in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
assert (HRS0 : rsaved_ok (ms_mem ms) sp0 regs).
{ unfold rsaved_ok. repeat match goal with |- _ /\ _ => split end;
[ frame_wordI HS 1%nat HU2 HE 1%nat (1%bv:reg) | frame_wordI HS 1%nat HU2 HE 8%nat (8%bv:reg)
| frame_wordI HS 1%nat HU2 HE 9%nat (9%bv:reg) | frame_wordI HS 1%nat HU2 HE 18%nat (18%bv:reg) ]. }
assert (WP0 : word_mem ubs2segs (ms_mem ms) (sp0 - 120) p).
{ replace (sp0 - 120) with (sp0 + -120) by lia.
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-120) (SOff 10 0) sp0 p HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, HU10; reflexivity | lia]. }
assert (WN0 : word_mem ubs2segs (ms_mem ms) (sp0 - 112) n).
{ replace (sp0 - 112) with (sp0 + -112) by lia.
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-112) (SOff 11 0) sp0 n HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2 | cbn [sv_denot]; rewrite Z.add_0_r, HU11; reflexivity | lia]. }
assert (WC0 : word_mem ubs2segs (ms_mem ms) (sp0 - 104) 0).
{ replace (sp0 - 104) with (sp0 + -104) by lia.
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (-104) (SLit 0) sp0 0 HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2 | reflexivity | lia]. }
eapply SR_bind.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset_spec E _ _ LIB_STACK_RGB sp0 [] L A mem md L A _ (sp0 - 72) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 72) with (sp0 + -72) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
pose proof (hinv_after_memset sp0 regs p n _ mem2 ltac:(lia) ltac:(lia) HRS0 WP0 WN0 WC0 Hout2 Hzero2) as HI0.
lazymatch goal with |- SR _ (mkCfg (mkst _ (Z_to_bv 64 ?z) _ _) _) _ =>
jafter_stretch_keep HS 32%nat regs2 mem2 MEMSET_CLOB z (@nil nat) HS2 end.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor. }
clear HS. rename HS2 into HS.
rd_step LAWS HU2 Hcase HS HJ2 HI0 (sp0 - 38) 2 38%nat.
all: rd_step LAWS HU2 Hcase HS HJ2 HI0 (sp0 - 36) 2 54%nat.
all: rd_step LAWS HU2 Hcase HS HJ2 HI0 (sp0 - 48) 4 70%nat.
all: rd_step LAWS HU2 Hcase HS HJ2 HI0 (sp0 - 44) 4 86%nat.
all: rd_step LAWS HU2 Hcase HS HJ2 HI0 (sp0 - 40) 2 102%nat.
2-6: jrun_to LAWS ubs2tbl_ok HS HJ2 RL_RET0; [apply wr_ok_nil|].
1: jrun_to LAWS ubs2tbl_ok HS HJ2 RL_MUL; [apply wr_ok_nil|].
2-6: lazymatch goal with HS : st_ok _ _ ?ss _ |- _ => assert (Hpc : ss_pc ss = RL_RET0) by (vm_compute; reflexivity) end.
1: lazymatch goal with HS : st_ok _ _ ?ss _ |- _ => assert (Hpc : ss_pc ss = RL_MUL) by (vm_compute; reflexivity) end.
all: match goal with HF : frame_of _ [] _ _ |- _ => apply (hinv_frame0 _ _ _ _ _ _ _ _ HF) in HI0; clear HF end.
all: rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl), Hpc; apply SR_ret.
2-6: eapply (hdr_post_ret0 regs L A mem md p n sp0 _ _ _ eq_refl HJ2 HI0);
[ reg_nowF HS ltac:(rewrite HU2; f_equal; lia)
| unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end;
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)
| lia ].
lazymatch type of HI0 with hinv _ _ _ _ ?c _ => replace c with 14 in HI0 by lia end.
eapply (hdr_post_mul regs L A mem md p n sp0 _ _ eq_refl HJ2 HI0);
[ reg_nowF HS ltac:(rewrite HU2; f_equal; lia)
| unfold runtouched_ok; repeat match goal with |- _ /\ _ => split end;
reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity)
| lia ].
Qed.
End S.
End d.
