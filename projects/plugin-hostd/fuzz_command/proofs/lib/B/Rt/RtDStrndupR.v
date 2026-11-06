(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build, and the module destructor's write set XW2 stated with the shadow of the whole image ([0x7fffa000, 0x800b8c00)) instead of the shadow bytes of cgif's three registered globals (fuzz_command registers 180), plus the odr indicator bytes of the four globals that have one (0x5e3c40..0x5e3c42, 0x5e3c80), which __asan_unregister_globals clears. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE23.v, with its module names changed; 275 of its 307 lines of code are new or changed and 1643 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtSRegionDef RtSRegion.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDStrndupTbl RtDStrndupS RtDStrndupP RtDStrndupA RtDStrndupF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* plugin-hostd/fuzz_command's strndup entry on its ASan+UBSan image (fuzz_command.asan-ubsan; the proof of
   lib/A/Rt/RtDStrndupR.v moved by the name-keyed A-to-B address map, the cells as lib/B/YF0m.v holds them) from the
   return of the malloc body (0x457bc) to its own return, as one
   SRr step: the flags and the size class (RtDStrndupP.v), the read check of the [mm] source bytes (inline,
   RtDStrndupS.v, or the range check 0x5a1f8 by its contract RtSRegion.v cmd_region_zero_stk for mm > 64), then
   RtDStrndupF.v snd_fin. The read-only words the stretch loads are const cells of the allocator invariant; the
   shadow of the source comes from the range check premises the caller derives from the live block. *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma snd_const_chk : forall ly,
const_chk ly 0xa5f40 8 0x142768 = true /\ const_chk ly 0x142864 1 1 = true /\ const_chk ly 0x14285d 1 0 = true /\
const_chk ly 0xa5f50 8 0xb0c38 = true /\ const_chk ly 0xb0c38 8 0x7fff8000 = true.
Proof. intros ly. repeat split; vm_compute; reflexivity. Qed.

Lemma val1_rdn : forall (m : word -> option byte) a v, 0 <= v < 256 ->
val_mem tfibsegs m a 1 v -> rdn tfibsegs m (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 v].
Proof.
intros m a v Hv Hm. apply (proj2 (rdn_mbytes tfibsegs m 1 a [Z_to_bv 8 v])). split; [reflexivity|].
intros i Hi. destruct i; [|lia]. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hm 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. rewrite H0.
rewrite (le_byte_small v 1 0) by (cbn; lia). cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
Qed.

(* the shadow of [x, x + m) inside a live block: the block's shadow (AR_shadow_law) makes every byte of
   [p0, p0 + n) addressable *)
Lemma ra_of_block : forall (rd : Z -> option Z) p0 n x m,
block_shadow rd SHADOW_OFF p0 n -> 0 <= p0 -> p0 <= x -> x + m <= p0 + n ->
range_addressable rd SHADOW_OFF x m.
Proof.
intros rd p0 n x m (Hal & Hn & Hb) Hp0 Hx Hxm y Hy.
pose proof (Z.div_mod p0 8 ltac:(lia)) as Dp. rewrite Hal, Z.add_0_r in Dp.
pose proof (Z.div_mod y 8 ltac:(lia)) as Dy. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as My.
pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as Mn.
pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as Dn7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as Mn7.
set (i := y / 8 - p0 / 8).
assert (Hi : 0 <= i < (n + 7) / 8) by (subst i; lia).
exists (if i <? n / 8 then 0 else n mod 8). split.
- unfold shadow_of_addr in *. rewrite <- (Hb i Hi). f_equal. subst i. lia.
- unfold saddr_ok. destruct (Z.ltb_spec i (n / 8)) as [Hl|Hl]; [left; reflexivity|]. right. subst i. lia.
Qed.

Lemma hull_sub : forall (rd : Z -> option Z) p0 n x m, 0 <= p0 -> p0 <= x -> 0 < m -> x + m <= p0 + n ->
shadow_hull_vis rd p0 n -> shadow_hull_vis rd x m.
Proof.
intros rd p0 n x m Hp0 Hx Hm Hxm Hh s Hs. apply Hh. unfold shadow_addr in *.
assert ((SHADOW_OFF + p0 / 8) / 8 <= (SHADOW_OFF + x / 8) / 8) by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert ((SHADOW_OFF + (x + m - 1) / 8) / 8 <= (SHADOW_OFF + (p0 + n - 1) / 8) / 8)
by (apply Z.div_le_mono; [lia|]; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia.
Qed.

(* what the inline check (RtDStrndupS.v) takes, read off range_addressable and shadow_hull_vis *)
Lemma chk_facts : forall H (mem : word -> option byte) x mm, 1 <= mm <= 64 -> 0 < x -> x + mm <= 2 ^ 47 ->
range_addressable (aview tfibsegs H mem) SHADOW_OFF x mm -> shadow_hull_vis (aview tfibsegs H mem) x mm ->
(forall g, g0 x <= g < g1 x (mm - 1) -> rdn tfibsegs (mrestrict H mem) (Z_to_bv 64 (SN_SB + g)) 1%nat = Some [Z_to_bv 8 0]) /\
(exists b : byte, rdn tfibsegs (mrestrict H mem) (Z_to_bv 64 (A1 x (mm - 1))) 1%nat = Some [b] /\
(bv_unsigned b = 0 \/ ((x + (mm - 1)) mod 8 < bv_unsigned b < 8))) /\
(exists bs, rdn tfibsegs (mrestrict H mem) (Z_to_bv 64 (A0 x - A0 x mod 8)) 8%nat = Some bs /\ length bs = 8%nat) /\
(exists bs, rdn tfibsegs (mrestrict H mem) (Z_to_bv 64 (A1 x (mm - 1) - A1 x (mm - 1) mod 8)) 8%nat = Some bs /\ length bs = 8%nat).
Proof.
intros H mem x mm Hmm Hx Hxm Hra Hh.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (x + (mm - 1)) 8 ltac:(lia)) as Dl. pose proof (Z.mod_pos_bound (x + (mm - 1)) 8 ltac:(lia)) as Ml.
assert (Hdl : x / 8 <= (x + (mm - 1)) / 8) by (apply Z.div_le_mono; lia).
assert (Hd47 : (x + (mm - 1)) / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia).
assert (HV : forall a, 0 <= a -> a + 8 <= 2 ^ 64 -> SHADOW_OFF + x / 8 - (SHADOW_OFF + x / 8) mod 8 <= a ->
a + 8 <= SHADOW_OFF + (x + (mm - 1)) / 8 - (SHADOW_OFF + (x + (mm - 1)) / 8) mod 8 + 8 ->
exists bs, rdn tfibsegs (mrestrict H mem) (Z_to_bv 64 a) 8%nat = Some bs /\ length bs = 8%nat).
{ intros a Ha0 Ha1 Ha2 Ha3. destruct (rdn_of_vis (mrestrict H mem) a 8 Ha0 ltac:(lia)) as (bs & Hbs & Lbs & _).
- intros i Hi. apply (proj1 (YF0x.aview_vis H mem (a + i))). apply Hh. unfold shadow_addr.
replace (x + mm - 1) with (x + (mm - 1)) by lia.
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)). pose proof (Z.div_mod (SHADOW_OFF + (x + (mm - 1)) / 8) 8 ltac:(lia)).
cbn [Z.of_nat Pos.of_succ_nat] in Hi. lia.
- exists bs. split; [exact Hbs | exact Lbs]. }
split; [|split; [|split]].
- intros g Hg. unfold g0, g1 in Hg. apply YE2y.aview0_rdn1; [unfold SN_SB; lia|].
apply (YE2y.ra_granule_zero _ x mm g Hra); lia.
- destruct (YE2y.ra_last _ x mm Hra ltac:(lia)) as (b1 & Hb1 & Hs).
replace (x + mm - 1) with (x + (mm - 1)) in Hb1, Hs by lia.
destruct (YE2y.aview_byte_ex H mem _ b1 Hb1) as (b & Eb & -> & _).
exists b. split.
+ apply (proj2 (rdn_mbytes tfibsegs _ 1 _ [b])). split; [reflexivity|]. intros i Hi. destruct i; [|lia].
cbn [nth_error Z.of_nat]. rewrite Z.add_0_r. unfold A1, g1. exact Eb.
+ unfold saddr_ok in Hs. lia.
- apply HV; unfold A0, g0, SN_SB, SHADOW_OFF in *; pose proof (Z.mod_pos_bound (2147450880 + (x + (mm - 1)) / 8) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia));
pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)); pose proof (Z.div_mod (2147450880 + (x + (mm - 1)) / 8) 8 ltac:(lia)); lia.
- apply HV; unfold A1, g1, SN_SB, SHADOW_OFF in *; pose proof (Z.mod_pos_bound (2147450880 + (x + (mm - 1)) / 8) 8 ltac:(lia));
pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia));
pose proof (Z.div_mod (2147450880 + x / 8) 8 ltac:(lia)); pose proof (Z.div_mod (2147450880 + (x + (mm - 1)) / 8) 8 ltac:(lia)); lia.
Qed.
End a.

Section a2.
Lemma same_io_tr : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. auto. Qed.
End a2.

Ltac acs := unfold acallee_saved;
repeat match goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with v end; lia.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.

(* From 0x457bc to the return. [mm n k] = min(n, k + 1) is the size the entry checks. *)
Theorem snd_post : forall ly' S' (W' : world tfibsegs) regs' mem' md' x n k p sp0 (buf : list byte)
(va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : Z),
AR tfibsegs B ly' S' W' mem' md' ->
rt_rom_view tfibsegs B W' mem' ->
2 ^ 44 <= sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> ly_stk_lo ly' + 16384 <= sp0 -> sp0 <= ly_stk_hi ly' ->
(forall a, sp0 - 16368 <= a < sp0 - 2160 -> apresent (w_H W') mem' a) ->
getr regs' 10 = w64 p -> getr regs' 9 = w64 x -> getr regs' 20 = w64 n -> getr regs' 21 = w64 (k + 1) ->
getr regs' 8 = w64 sp0 -> getr regs' 18 = w64 k -> getr regs' 2 = w64 (sp0 - 2160) ->
word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 8) va -> word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 16) vs0 ->
word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 24) vs1 -> word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 32) vs2 ->
word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 40) vs3 -> word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 48) vs4 ->
word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 56) vs5 -> word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 64) vs6 ->
word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 72) vs7 -> word_mem tfibsegs (mrestrict (w_H W') mem') (sp0 - 80) vs8 ->
v_jalr (Z_to_bv 64 va) 0 = Z_to_bv 64 va ->
0 < x -> x + RtDStrndupP.mm n k <= sp0 - 16384 -> 0 <= k <= n -> n < 2 ^ 32 -> k <= Z.of_nat (length buf) -> 0 <= p < 2 ^ 64 ->
(forall a, x <= a < x + RtDStrndupP.mm n k -> aview tfibsegs (w_H W') mem' a <> None) ->
range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF x (RtDStrndupP.mm n k) ->
(0 < RtDStrndupP.mm n k -> shadow_hull_vis (aview tfibsegs (w_H W') mem') x (RtDStrndupP.mm n k)) ->
amem_range x (RtDStrndupP.mm n k) ->
(forall j, (j < Z.to_nat k)%nat -> aview tfibsegs (w_H W') mem' (x + Z.of_nat j) = Some (bv_unsigned (nth j buf NUL))) ->
(p <> 0 -> 0 < p /\ p + k + 1 <= sp0 - 16384 /\ (p + k + 1 <= x \/ x + k <= p) /\
(forall a, p <= a < p + k + 1 -> apresent (w_H W') mem' a /\ ~ aowned B ly' S' a)) ->
SRr tfibsegs W' (cfg_at tfibsegs 0x457bc regs' mem' md')
(fun W'' c'' => W'' = W' /\ exists regs'' mem'' md'',
c'' = cfg_at tfibsegs va regs'' mem'' md'' /\
AR tfibsegs B ly' S' W' mem'' md'' /\ same_io md' md'' /\
getr regs'' 10 = Z_to_bv 64 p /\ getr regs'' 2 = Z_to_bv 64 sp0 /\ getr regs'' 1 = Z_to_bv 64 va /\
getr regs'' 8 = Z_to_bv 64 vs0 /\ getr regs'' 9 = Z_to_bv 64 vs1 /\ getr regs'' 18 = Z_to_bv 64 vs2 /\
getr regs'' 19 = Z_to_bv 64 vs3 /\ getr regs'' 20 = Z_to_bv 64 vs4 /\ getr regs'' 21 = Z_to_bv 64 vs5 /\
getr regs'' 22 = Z_to_bv 64 vs6 /\ getr regs'' 23 = Z_to_bv 64 vs7 /\ getr regs'' 24 = Z_to_bv 64 vs8 /\
(forall r : bv 5, r = 3%bv \/ r = 4%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv -> getr regs'' r = getr regs' r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2232 <= a < sp0 - 2160) -> ~ (p <> 0 /\ p <= a < p + k + 1) ->
aview tfibsegs (w_H W') mem'' a = aview tfibsegs (w_H W') mem' a) /\
(forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem'' a) /\
(p <> 0 -> abytes_at tfibsegs W' mem'' p (firstn (Z.to_nat k) buf ++ [Z_to_bv 8 0]))).
Proof.
intros ly' S' W' regs' mem' md' x n k p sp0 buf va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8
HAR HROM Hsp Hal Hslo Hshi Hpres G10 G9 G20 G21 G8 G18 G2 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 Hret
Hx Hxm Hk Hn Hkb Hp Hvis Hra Hhull Ham Hsrc Hblk.
set (mm0 := RtDStrndupP.mm n k) in *.
assert (MF : 0 <= mm0 <= k + 1 /\ mm0 <= n /\ k <= mm0) by (unfold mm0, RtDStrndupP.mm; lia).
pose (H := w_H W').
assert (Hxn : x + n + 1 <= 2 ^ 63) by lia.
(* the read-only words *)
pose proof (snd_const_chk ly') as (C0 & C1 & C2 & C3 & C4).
pose proof (proj1 HAR) as HM.
assert (F0 : word_mem tfibsegs (mrestrict H mem') 0xa5f40 0x142768)
by (apply (proj1 (val_mem_word_mem tfibsegs _ _ _)); exact (tfib_const_lookup B TB ly' S' H mem' 0xa5f40 8 0x142768 HM (const_chk_sound _ _ _ _ C0))).
assert (F1 : rdn tfibsegs (mrestrict H mem') (Z_to_bv 64 0x142864) 1 = Some [Z_to_bv 8 1])
by (apply val1_rdn; [lia | exact (tfib_const_lookup B TB ly' S' H mem' 0x142864 1 1 HM (const_chk_sound _ _ _ _ C1))]).
assert (F2 : rdn tfibsegs (mrestrict H mem') (Z_to_bv 64 0x14285d) 1 = Some [Z_to_bv 8 0])
by (apply val1_rdn; [lia | exact (tfib_const_lookup B TB ly' S' H mem' 0x14285d 1 0 HM (const_chk_sound _ _ _ _ C2))]).
assert (F3 : word_mem tfibsegs (mrestrict H mem') 0xa5f50 0xb0c38)
by (apply (proj1 (val_mem_word_mem tfibsegs _ _ _)); exact (tfib_const_lookup B TB ly' S' H mem' 0xa5f50 8 0xb0c38 HM (const_chk_sound _ _ _ _ C3))).
assert (F4 : word_mem tfibsegs (mrestrict H mem') 0xb0c38 SN_SB)
by (apply (proj1 (val_mem_word_mem tfibsegs _ _ _)); exact (tfib_const_lookup B TB ly' S' H mem' 0xb0c38 8 0x7fff8000 HM (const_chk_sound _ _ _ _ C4))).
assert (M1 : forall z, munrestrict H mem' (mrestrict H mem') z = mem' z) by (intros z; apply munrestrict_mrestrict_same).
(* every way through the read check reaches 0x45898 *)
assert (REACH : SRr tfibsegs W' (cfg_at tfibsegs 0x457bc regs' mem' md')
(fun W3 c3 => W3 = W' /\ exists regs3 mem3 md3, c3 = cfg_at tfibsegs 0x45898 regs3 mem3 md3 /\
AR tfibsegs B ly' S' W' mem3 md3 /\ same_io md' md3 /\
getr regs3 19 = Z_to_bv 64 p /\ getr regs3 9 = Z_to_bv 64 x /\ getr regs3 18 = Z_to_bv 64 k /\
getr regs3 2 = Z_to_bv 64 (sp0 - 2160) /\
(forall r : bv 5, r = 3%bv \/ r = 4%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv -> getr regs3 r = getr regs' r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2232 <= a < sp0 - 2160) -> aview tfibsegs (w_H W') mem3 a = aview tfibsegs (w_H W') mem' a) /\
(forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem3 a))).
{ unfold cfg_at. change (w64 0x457bc) with (Z_to_bv 64 0x457bc).
destruct (snp_flags (mrestrict H mem') (seg_rom tfibsegs) x n k p sp0 Hx Hxn Hk Hn Hp F0 F1 F2 regs' G10 G9 G20 G21 G8)
as (regs1 & Hms1 & B19 & B20 & B22 & B23 & K1).
fold mm0 in B20.
assert (Q9 : getr regs1 9 = Z_to_bv 64 x) by (rewrite K1 by reg_neq_tac; exact G9).
assert (Q18 : getr regs1 18 = Z_to_bv 64 k) by (rewrite K1 by reg_neq_tac; exact G18).
assert (Q2 : getr regs1 2 = Z_to_bv 64 (sp0 - 2160)) by (rewrite K1 by reg_neq_tac; exact G2).
assert (QK : forall r : bv 5, r = 3%bv \/ r = 4%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv -> getr regs1 r = getr regs' r)
by (intros r Hr; apply K1; destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac).
destruct (Z_lt_le_dec 64 mm0) as [Hbig|Hsm].
- (* 65 bytes and more: the range check *)
destruct (snp_big (mrestrict H mem') (seg_rom tfibsegs) x n k p Hk Hn Hp regs1 ltac:(lia) Q9 B20) as (regs2 & Hms2 & D10 & D11 & D1 & K2).
eapply (SRr_msteps tfibsegs YF0x.Hwx_tfa W'); [rewrite restrict_mkst_fx; eapply msteps_trans; [exact Hms1 | exact Hms2]|].
intros md1 Hsbm1 _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem1 := munrestrict H mem' (mrestrict H mem')) in *.
assert (AV1 : forall a, aview tfibsegs H mem1 a = aview tfibsegs H mem' a) by (intros a; apply aview_same; apply M1).
assert (R2 : getr regs2 2 = Z_to_bv 64 (sp0 - 2160)) by (rewrite K2 by reg_neq_tac; exact Q2).
assert (Hsp2 : YG0d.spZ regs2 = sp0 - 2160) by (unfold YG0d.spZ; rewrite R2; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ apply (cmd_region_zero_stk B LAWS TB 72 ltac:(unfold RGN_SCR; lia) ly' S' W' regs2 mem1 md1 x mm0).
- apply (al_frame _ _ LAWS ly' S' W' mem' md' mem1 md1 HAR).
+ intros a _ _. apply AV1.
+ intros a Hv. rewrite AV1. exact Hv.
+ apply (same_but_materialized_frame md' md1 Hsbm1).
+ apply (same_but_materialized_frame md' md1 Hsbm1).
+ apply (same_but_materialized_frame md' md1 Hsbm1).
+ intros a _ _. apply M1.
- rewrite D1. apply ret_ok_lit; [lia | reflexivity].
- rewrite Hsp2. replace (sp0 - 2160) with (sp0 + (-135) * 16) by lia. rewrite Z_mod_plus_full. exact Hal.
- rewrite Hsp2. lia.
- rewrite Hsp2. lia.
- intros a Ha. rewrite Hsp2 in Ha. apply (apresent_same H mem' mem1 a (M1 _)). apply Hpres. lia.
- exact D10.
- exact D11.
- lia.
- exact Hx.
- split; [lia|]. split; [lia|]. split; [lia|].
split; [intros a Ha; split; [rewrite AV1; apply Hvis; exact Ha | unfold ascratch_stk; rewrite Hsp2; lia]|].
split; [exact Ham|].
split; [eapply range_addressable_agree; [|exact Hra]; intros y Hy; apply AV1|].
intros Hm0 s Hs. rewrite AV1. exact (Hhull Hm0 s Hs).
- apply (rt_rom_view_keep tfibsegs B W' mem' mem1 HROM). intros a _ _ _. apply AV1. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & KP3 & Hsbm3 & A10 & Hfr3 & Hpr3 & _).
assert (KP3' : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs2 r).
{ intros r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply KP3. exact Hr. }
unfold raZ. rewrite D1. rewrite unsigned_lit_small by lia.
eapply (SRr_msteps tfibsegs YF0x.Hwx_tfa W'); [rewrite restrict_mkst_fx; apply snp_ret; exact A10|].
intros md4 Hsbm4 _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem4 := munrestrict H mem3 (mrestrict H mem3)).
assert (M4 : forall z, mem4 z = mem3 z) by (intros z; subst mem4; apply munrestrict_mrestrict_same).
assert (AV4 : forall a, aview tfibsegs H mem4 a = aview tfibsegs H mem3 a) by (intros a; apply aview_same; apply M4).
assert (K2' : forall r : bv 5, r <> 1%bv -> r <> 10%bv -> r <> 11%bv -> acallee_saved (bv_unsigned r) -> getr regs3 r = getr regs1 r).
{ intros r A1 A2 A3 A4. rewrite (KP3' r A4). apply K2; assumption. }
apply SRr_ret. split; [reflexivity|]. exists regs3, mem4, md4.
split; [reflexivity|].
split.
{ apply (al_frame _ _ LAWS ly' S' W' mem3 md3 mem4 md4 HAR3).
+ intros a _ _. apply AV4.
+ intros a Hv. rewrite AV4. exact Hv.
+ apply (same_but_materialized_frame md3 md4 Hsbm4).
+ apply (same_but_materialized_frame md3 md4 Hsbm4).
+ apply (same_but_materialized_frame md3 md4 Hsbm4).
+ intros a _ _. apply M4. }
split; [exact (same_io_tr md' md1 md4 (same_io_sbm _ _ Hsbm1) (same_io_tr md1 md3 md4 (same_io_sbm _ _ Hsbm3) (same_io_sbm _ _ Hsbm4)))|].
split; [rewrite (K2' 19%bv) by (first [reg_neq_tac | acs]); exact B19|].
split; [rewrite (K2' 9%bv) by (first [reg_neq_tac | acs]); exact Q9|].
split; [rewrite (K2' 18%bv) by (first [reg_neq_tac | acs]); exact Q18|].
split; [rewrite (K2' 2%bv) by (first [reg_neq_tac | acs]); exact Q2|].
split.
{ intros r Hr. rewrite <- (QK r Hr). destruct Hr as [->|[->|[->|[->| ->]]]];
(rewrite K2'; [reflexivity | reg_neq_tac | reg_neq_tac | reg_neq_tac | acs]). }
split.
{ intros a Ha Hns. rewrite AV4.
pose proof (Hfr3 a Ha ltac:(unfold ascratch_stk; rewrite Hsp2; lia) (fun HF : False => HF)) as E3. fold H in E3. rewrite E3. apply AV1. }
intros a Hp1. apply (apresent_same H mem3 mem4 a (M4 _)). apply Hpr3. apply (apresent_same H mem' mem1 a (M1 _)). exact Hp1.
- (* at most 64 bytes: the inline check, or nothing to check *)
assert (Hsmall : exists regs2, msteps tfibsegs (mkst regs1 (Z_to_bv 64 0x45850) (mrestrict H mem') (seg_rom tfibsegs))
(mkst regs2 (Z_to_bv 64 0x45898) (mrestrict H mem') (seg_rom tfibsegs)) /\
(forall r : bv 5, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs2 r = getr regs1 r)).
{ destruct (Z.eq_dec mm0 0) as [Hz|Hnz].
+ destruct (snp_zero (mrestrict H mem') (seg_rom tfibsegs) n k p Hp regs1 Hz B20) as (regs2 & Hms2 & K2).
exists regs2. split; [exact Hms2|]. intros r A1 A2 _ _ _. apply K2; assumption.
+ destruct (chk_facts H mem' x mm0 ltac:(lia) Hx ltac:(lia) Hra (Hhull ltac:(lia))) as (GZ & GL & W0 & W1).
exact (snp_small (mrestrict H mem') (seg_rom tfibsegs) x n k p sp0 Hx Hxn Hk Hp Hsp regs1 ltac:(lia) F3 F4 GZ GL W0 W1 Q9 B20). }
destruct Hsmall as (regs2 & Hms2 & K2).
eapply (SRr_msteps tfibsegs YF0x.Hwx_tfa W'); [rewrite restrict_mkst_fx; eapply msteps_trans; [exact Hms1 | exact Hms2]|].
intros md1 Hsbm1 _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem1 := munrestrict H mem' (mrestrict H mem')) in *.
assert (AV1 : forall a, aview tfibsegs H mem1 a = aview tfibsegs H mem' a) by (intros a; apply aview_same; apply M1).
apply SRr_ret. split; [reflexivity|]. exists regs2, mem1, md1.
split; [reflexivity|].
split.
{ apply (al_frame _ _ LAWS ly' S' W' mem' md' mem1 md1 HAR).
+ intros a _ _. apply AV1.
+ intros a Hv. rewrite AV1. exact Hv.
+ apply (same_but_materialized_frame md' md1 Hsbm1).
+ apply (same_but_materialized_frame md' md1 Hsbm1).
+ apply (same_but_materialized_frame md' md1 Hsbm1).
+ intros a _ _. apply M1. }
split; [apply same_io_sbm, Hsbm1|].
split; [rewrite K2 by reg_neq_tac; exact B19|].
split; [rewrite K2 by reg_neq_tac; exact Q9|].
split; [rewrite K2 by reg_neq_tac; exact Q18|].
split; [rewrite K2 by reg_neq_tac; exact Q2|].
split; [intros r Hr; rewrite <- (QK r Hr); apply K2; destruct Hr as [->|[->|[->|[->| ->]]]]; reg_neq_tac|].
split; [intros a _ _; apply AV1|].
intros a Hp1. apply (apresent_same H mem' mem1 a (M1 _)). exact Hp1. }
eapply SRr_bind; [exact REACH|].
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & Hio3 & R19 & R9 & R18 & R2 & RK & Hfr3 & Hpr3).
assert (VK : forall a v, sp0 - 80 <= a -> a + 8 <= sp0 -> word_mem tfibsegs (mrestrict H mem') a v -> word_mem tfibsegs (mrestrict H mem3) a v).
{ intros a v Ha1 Ha2 Hw. apply (proj1 (val_mem_word_mem tfibsegs _ _ _)). apply (proj2 (val_mem_word_mem tfibsegs _ _ _)) in Hw.
apply (YE2y.val_mem_kept H H mem' mem3 a 8 v); [|exact Hw]. intros q Hq. apply Hfr3; lia. }
eapply SRr_mono.
{ apply (snd_fin B LAWS ly' S' W' regs3 mem3 md3 x k p sp0 buf va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 HAR3 Hsp R19 R9 R18 R2
(VK (sp0 - 8) va ltac:(lia) ltac:(lia) V0) (VK (sp0 - 16) vs0 ltac:(lia) ltac:(lia) V1) (VK (sp0 - 24) vs1 ltac:(lia) ltac:(lia) V2)
(VK (sp0 - 32) vs2 ltac:(lia) ltac:(lia) V3) (VK (sp0 - 40) vs3 ltac:(lia) ltac:(lia) V4) (VK (sp0 - 48) vs4 ltac:(lia) ltac:(lia) V5)
(VK (sp0 - 56) vs5 ltac:(lia) ltac:(lia) V6) (VK (sp0 - 64) vs6 ltac:(lia) ltac:(lia) V7) (VK (sp0 - 72) vs7 ltac:(lia) ltac:(lia) V8)
(VK (sp0 - 80) vs8 ltac:(lia) ltac:(lia) V9) Hret Hx ltac:(lia) ltac:(lia)).
- intros j Hj. rewrite (Hfr3 (x + Z.of_nat j)) by lia. apply Hsrc. exact Hj.
- intros Hp0. destruct (Hblk Hp0) as (Q1 & Q2 & Q3 & Q4). split; [exact Q1|]. split; [lia|]. split; [exact Q3|].
intros a Ha. destruct (Q4 a Ha) as [Q5 Q6]. split; [apply Hpr3; exact Q5 | exact Q6]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & Hsbm4 & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & EK & Hfr4 & Hpr4 & Hby).
split; [reflexivity|]. exists regs4, mem4, md4.
split; [reflexivity|]. split; [exact HAR4|].
split; [exact (same_io_tr md' md3 md4 Hio3 (same_io_sbm _ _ Hsbm4))|].
do 12 (split; [assumption|]).
split; [intros r Hr; rewrite (EK r Hr); exact (RK r Hr)|].
split; [intros a Ha Hn1 Hn2; rewrite (Hfr4 a Ha Hn2); exact (Hfr3 a Ha Hn1)|].
split; [intros a Ha; apply Hpr4, Hpr3, Ha|].
exact Hby.
Qed.
End g.
