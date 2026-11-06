(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AE23.v, with its module paths changed, names TfibSyms -> CmdBSyms, its addresses moved to plugin-hostd/fuzz_command's ASan build, and the module destructor's write set XW2 stated with the shadow of the whole image ([0x7fffa000, 0x800b8c00)) instead of the shadow bytes of cgif's three registered globals (fuzz_command registers 180), plus the odr indicator bytes of the four globals that have one (0x5e3c40..0x5e3c42, 0x5e3c80), which __asan_unregister_globals clears. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/AE23.v, with its module names changed; 149 of its 183 lines of code are new or changed and 1641 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtDStrndupTbl RtDStrndupP RtDStrndupQ RtDStrndupA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* plugin-hostd/fuzz_command's strndup entry from 0x4584c to its return, as one SRr step: the copy into the block
   and its terminator when the block is not null (RtDStrndupQ.v), then the epilogue (RtDStrndupP.v). The post says
   what the walk of the whole entry needs: the allocator invariant kept (only the block's bytes change, and they are
   not owned), the bytes of the block, the registers the epilogue restores, and that nothing else moved. *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma apresent_of_aview_hi : forall H (mem : word -> option byte) a, TFIB_IMG_END <= a < 2 ^ 64 ->
aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha Hv. unfold aview, YP09.mbyte, mrestrict in Hv. rewrite (seg_rom_none_high a Ha) in Hv.
unfold apresent. destruct (H (Z_to_bv 64 a)); [cbn in Hv; congruence|]. split; [reflexivity|].
destruct (mem (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | cbn in Hv; congruence].
Qed.
Lemma mrw_out : forall (H : word -> bool) (mem : word -> option byte) (pa : word) bs (z : word),
bv_unsigned pa + Z.of_nat (length bs) <= 2 ^ 64 ->
bv_unsigned z < bv_unsigned pa \/ bv_unsigned pa + Z.of_nat (length bs) <= bv_unsigned z ->
mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) pa bs)) z = mrestrict H mem z.
Proof.
intros H mem pa bs z Hb Hz. unfold mrestrict at 1, munrestrict. destruct (H z) eqn:E; [unfold mrestrict; rewrite E; reflexivity|].
destruct Hz as [Hz|Hz]; [rewrite wbytes_below by assumption | rewrite wbytes_above by assumption]; reflexivity.
Qed.
Lemma mrw_in : forall (H : word -> bool) (mem : word -> option byte) (pa : word) bs (z : word),
bv_unsigned pa + Z.of_nat (length bs) <= 2 ^ 64 ->
bv_unsigned pa <= bv_unsigned z < bv_unsigned pa + Z.of_nat (length bs) -> H z = false ->
mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) pa bs)) z = nth_error bs (Z.to_nat (bv_unsigned z - bv_unsigned pa)).
Proof.
intros H mem pa bs z Hb Hz Hh. unfold mrestrict at 1, munrestrict. rewrite Hh. apply AE2y.wbytes_inside; assumption.
Qed.
Lemma mrw_same : forall (H : word -> bool) (mem : word -> option byte) (pa : word) bs a,
bv_unsigned pa + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= a < 2 ^ 64 ->
~ (bv_unsigned pa <= a < bv_unsigned pa + Z.of_nat (length bs)) ->
aview tfibsegs H (munrestrict H mem (wbytes (mrestrict H mem) pa bs)) a = aview tfibsegs H mem a.
Proof.
intros H mem pa bs a Hb Ha Hn. apply aview_eq_of. apply mrw_out; [exact Hb|]. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma same_io_sbm : forall md md', same_but_materialized md md' -> same_io md md'.
Proof.
intros md md' Hs. rewrite (same_but_materialized_wvb md md' Hs).
destruct md as [f [mp lz mt] io fs pr li ti sg sc]. repeat split; reflexivity.
Qed.
End a.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

Theorem snd_fin : forall ly' S' (W' : world tfibsegs) regs3 mem3 md3 x k p sp0 (buf : list byte)
(va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : Z),
AR tfibsegs B ly' S' W' mem3 md3 ->
2 ^ 44 <= sp0 <= 2 ^ 47 ->
getr regs3 19 = Z_to_bv 64 p -> getr regs3 9 = Z_to_bv 64 x -> getr regs3 18 = Z_to_bv 64 k ->
getr regs3 2 = Z_to_bv 64 (sp0 - 2160) ->
word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 8) va -> word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 16) vs0 ->
word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 24) vs1 -> word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 32) vs2 ->
word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 40) vs3 -> word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 48) vs4 ->
word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 56) vs5 -> word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 64) vs6 ->
word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 72) vs7 -> word_mem tfibsegs (mrestrict (w_H W') mem3) (sp0 - 80) vs8 ->
v_jalr (Z_to_bv 64 va) 0 = Z_to_bv 64 va ->
0 < x -> x + k < 2 ^ 63 -> 0 <= k <= Z.of_nat (length buf) ->
(forall j, (j < Z.to_nat k)%nat -> aview tfibsegs (w_H W') mem3 (x + Z.of_nat j) = Some (bv_unsigned (nth j buf NUL))) ->
(p <> 0 -> 0 < p /\ p + k + 1 <= sp0 - 80 /\ (p + k + 1 <= x \/ x + k <= p) /\
(forall a, p <= a < p + k + 1 -> apresent (w_H W') mem3 a /\ ~ aowned B ly' S' a)) ->
SRr tfibsegs W' (cfg_at tfibsegs 0x4584c regs3 mem3 md3)
(fun W'' c'' => W'' = W' /\ exists regs'' mem'' md'',
c'' = cfg_at tfibsegs va regs'' mem'' md'' /\
AR tfibsegs B ly' S' W' mem'' md'' /\ same_but_materialized md3 md'' /\
getr regs'' 10 = Z_to_bv 64 p /\ getr regs'' 2 = Z_to_bv 64 sp0 /\ getr regs'' 1 = Z_to_bv 64 va /\
getr regs'' 8 = Z_to_bv 64 vs0 /\ getr regs'' 9 = Z_to_bv 64 vs1 /\ getr regs'' 18 = Z_to_bv 64 vs2 /\
getr regs'' 19 = Z_to_bv 64 vs3 /\ getr regs'' 20 = Z_to_bv 64 vs4 /\ getr regs'' 21 = Z_to_bv 64 vs5 /\
getr regs'' 22 = Z_to_bv 64 vs6 /\ getr regs'' 23 = Z_to_bv 64 vs7 /\ getr regs'' 24 = Z_to_bv 64 vs8 /\
(forall r : bv 5, r = 3%bv \/ r = 4%bv \/ r = 25%bv \/ r = 26%bv \/ r = 27%bv -> getr regs'' r = getr regs3 r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (p <> 0 /\ p <= a < p + k + 1) ->
aview tfibsegs (w_H W') mem'' a = aview tfibsegs (w_H W') mem3 a) /\
(forall a, apresent (w_H W') mem3 a -> apresent (w_H W') mem'' a) /\
(p <> 0 -> abytes_at tfibsegs W' mem'' p (firstn (Z.to_nat k) buf ++ [Z_to_bv 8 0]))).
Proof.
intros ly' S' W' regs3 mem3 md3 x k p sp0 buf va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 HAR Hsp G19 G9 G18 G2
V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 Hret Hx Hxk Hk Hsrc Hblk.
pose (H := w_H W').
unfold cfg_at. change (w64 0x4584c) with (Z_to_bv 64 0x4584c).
destruct (Z.eq_dec p 0) as [Hp0|Hp0].
- (* a null block: no copy *)
subst p.
destruct (snp_tail_null (mrestrict H mem3) (seg_rom tfibsegs) sp0 va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 Hsp
V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 regs3 G19 G2)
as (regs' & Hms & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & K).
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W'); [rewrite restrict_mkst_fx; exact Hms|].
intros md'' Hsbm _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem'' := munrestrict H mem3 (mrestrict H mem3)).
assert (M : forall z, mem'' z = mem3 z) by (intros z; subst mem''; apply munrestrict_mrestrict_same).
assert (AV : forall a, aview tfibsegs H mem'' a = aview tfibsegs H mem3 a) by (intros a; apply aview_same; apply M).
apply SRr_ret. split; [reflexivity|]. exists regs', mem'', md''.
split; [unfold cfg_at, w64; rewrite Hret; reflexivity|].
split.
{ apply (al_frame _ _ LAWS ly' S' W' mem3 md3 mem'' md'' HAR).
+ intros a _ _. apply AV.
+ intros a Hv. rewrite AV. exact Hv.
+ apply (same_but_materialized_frame md3 md'' Hsbm).
+ apply (same_but_materialized_frame md3 md'' Hsbm).
+ apply (same_but_materialized_frame md3 md'' Hsbm).
+ intros a _ _. apply M. }
split; [exact Hsbm|].
do 12 (split; [assumption|]).
split; [exact K|].
split; [intros a _ _; apply AV|].
split; [intros a Ha; apply (apresent_same H mem3 mem'' a (M _)); exact Ha|].
intros C; exfalso; exact (C eq_refl).
- (* a block: the copy and its terminator *)
destruct (Hblk Hp0) as (Hp & Hps & Hdj & Hbl).
assert (Hrd : forall j, (j < Z.to_nat k)%nat -> rdn tfibsegs (mrestrict H mem3) (Z_to_bv 64 (x + Z.of_nat j)) 1 = Some [nth j buf NUL]).
{ intros j Hj. apply rdn1_of_aview. apply Hsrc. exact Hj. }
assert (Hpr : forall i, 0 <= i <= k -> YO0d.present (mrestrict H mem3) (p + i)).
{ intros i Hi. destruct (Hbl (p + i) ltac:(lia)) as [[Hh [b Hb]] _]. exists b. unfold mrestrict.
replace (H (Z_to_bv 64 (p + i))) with false by (symmetry; exact Hh). exact Hb. }
destruct (snp_tail_copy (mrestrict H mem3) (seg_rom tfibsegs) sp0 va vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 Hsp
V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 regs3 x k p buf Hp Hps Hx Hxk Hk Hdj Hrd Hpr G19 G9 G18 G2)
as (regs' & Hms & E10 & E2 & E1 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & K).
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W'); [rewrite restrict_mkst_fx; exact Hms|].
intros md'' Hsbm _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (bs := firstn (Z.to_nat k) buf ++ [Z_to_bv 8 0]) in *.
assert (Lbs : Z.of_nat (length bs) = k + 1).
{ subst bs. rewrite length_app, length_firstn. cbn [length]. lia. }
set (mem'' := munrestrict H mem3 (wbytes (mrestrict H mem3) (Z_to_bv 64 p) bs)).
assert (Up : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit_small; lia).
assert (AVo : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + k + 1) -> aview tfibsegs H mem'' a = aview tfibsegs H mem3 a).
{ intros a Ha Hn. subst mem''. apply mrw_same; [rewrite Up; lia | exact Ha | rewrite Up; lia]. }
apply SRr_ret. split; [reflexivity|]. exists regs', mem'', md''.
split; [unfold cfg_at, w64; rewrite Hret; reflexivity|].
split.
{ apply (al_frame _ _ LAWS ly' S' W' mem3 md3 mem'' md'' HAR).
+ intros a Ha Hown. apply AVo; [exact Ha|]. intros Hin. exact (proj2 (Hbl a Hin) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ mem'' a). rewrite (AE2y.aview_mod _ mem3 a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' p) as [L1|L1]; [rewrite AVo by lia; exact Hv|].
destruct (Z_lt_le_dec a' (p + k + 1)) as [L2|L2]; [| rewrite AVo by lia; exact Hv].
destruct (Hbl a' ltac:(lia)) as [[Hh _] _].
unfold aview, YP09.mbyte. fold H. subst mem''.
rewrite (mrw_in H mem3 (Z_to_bv 64 p) bs (Z_to_bv 64 a')); [| rewrite Up; lia | rewrite Up, unsigned_lit_small by lia; lia | exact Hh].
destruct (nth_error bs _) eqn:En; [cbn; discriminate|].
apply nth_error_None in En. rewrite Up, unsigned_lit_small in En by lia. lia.
+ apply (same_but_materialized_frame md3 md'' Hsbm).
+ apply (same_but_materialized_frame md3 md'' Hsbm).
+ apply (same_but_materialized_frame md3 md'' Hsbm).
+ intros a _ Hh. subst mem''. unfold munrestrict. replace (H (w64 a)) with true by (symmetry; exact Hh). reflexivity. }
split; [exact Hsbm|].
do 12 (split; [assumption|]).
split; [exact K|].
split.
{ intros a Ha Hn. apply AVo; [exact Ha|]. intros Hin. apply Hn. split; [exact Hp0 | exact Hin]. }
split.
{ intros a [Hh [b Hb]]. split; [exact Hh|]. subst mem''. unfold munrestrict.
destruct (H (Z_to_bv 64 a)) eqn:E; [exists b; exact Hb|].
destruct (wbytes (mrestrict H mem3) (Z_to_bv 64 p) bs (Z_to_bv 64 a)) as [b'|] eqn:Ew; [exists b'; reflexivity|].
exfalso. refine (wbytes_grows bs (mrestrict H mem3) (Z_to_bv 64 p) (Z_to_bv 64 a) _ Ew).
unfold mrestrict. rewrite E, Hb. discriminate. }
intros _ i Hi. fold bs.
assert (Hi' : Z.of_nat i < k + 1) by lia.
unfold aview, YP09.mbyte. fold H.
destruct (Hbl (p + Z.of_nat i) ltac:(lia)) as [[Hh _] _].
subst mem''. rewrite (mrw_in H mem3 (Z_to_bv 64 p) bs (Z_to_bv 64 (p + Z.of_nat i))).
+ rewrite Up, unsigned_lit_small by lia. replace (p + Z.of_nat i - p) with (Z.of_nat i) by lia.
rewrite Nat2Z.id. rewrite (nth_error_nth' bs (Z_to_bv 8 0)) by exact Hi. reflexivity.
+ rewrite Up. lia.
+ rewrite Up, unsigned_lit_small by lia. lia.
+ exact Hh.
Qed.
End f.
