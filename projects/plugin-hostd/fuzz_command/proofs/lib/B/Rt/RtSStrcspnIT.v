(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: range_addressable_kept_win and shadow_hull_vis_kept_win of cgif_file_fuzzer's lib/YC85.v (as fuzz_command's lib/A/Prog/PaCall.v holds them) copied as ci_ra_kept_win and ci_hull_kept_win, and the kept_out lemmas of lib/A/Prog/PaArt.v adapted, into the shared pieces of the strcspn interceptor walk of plugin-hostd/fuzz_command's ASan build. *)
(* Modified by Theorem Labs, 2026-10: moved from this harness's lib/A/Rt/RtSStrcspnIT.v to plugin-hostd/fuzz_command's ASan+UBSan image (fuzz_command.asan-ubsan), whose ___interceptor_strcspn (0x46ce4) is the ASan image's (0x46c98) word for word modulo pc-relative fields: module paths lib/A to lib/B, and the addresses by the name-keyed A-to-B address map (the trampoline 0x45198, the interceptor 0x46ce4, TryAsanInitFromRtl 0x5f68c, musl strcspn 0x9ee10, internal_strlen 0x69b5c, the range check 0x5a1f8); the comments re-read from that image; the proof text is unchanged. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* Shared pieces of the walk of the strcspn interceptor of plugin-hostd/fuzz_command's ASan+UBSan build (trampoline
   0x45198 -> ___interceptor_strcspn 0x46ce4), measured on the pinned fuzz_command.asan-ubsan: the instruction table, the
   one-load step, the inline check's flag, and the frame lemmas. Most of them are those of the strspn walk
   (lib/A/Rt/RtSStrspnB.v on the ASan image), whose interceptor (0x4685c here) is this one shifted by 0x488. *)

(* The instruction table: the trampoline 0x45198 (`j 0x46ce4`), the interceptor 0x46ce4 (0x488 bytes, 290
   instructions) and TryAsanInitFromRtl 0x5f68c (40 instructions). musl's strcspn 0x9ee10, internal_strlen 0x69b5c
   and the range check 0x5a1f8 are not in it: each symbolic run stops at their entry, and a contract or a lemma
   steps them. *)
Definition ci_ranges : list (Z * nat) := [(0x45198, 1%nat); (0x46ce4, 290%nat); (0x5f68c, 40%nat)].
Definition tbl_ci : ctable := Eval vm_compute in build_ranges ci_ranges TEmpty.
Lemma tbl_ci_eq : tbl_ci = build_ranges ci_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_ci). Qed.
Lemma tbl_ci_ok : table_ok tfibsegs tbl_ci.
Proof. rewrite tbl_ci_eq. apply build_ranges_ok; [unfold ci_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.

(* The shadow bytes of a checked range of at most 64 bytes, as cgif_file_fuzzer's site walks state them
   (A/AE7e.v:74-76): base atom 32 is beg / 8, then t zero bytes and the shadow byte of the last byte (atom 34). *)
Definition shreg1 (t : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YP09.mkChunk SB (CZero t)] else []) ++ [YP09.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).

(* The inline check's AddressIsPoisoned(last) flag, for any expression [lst] of the last byte. *)
Definition qcB_core (lst : sv) (pb : nat) : sv :=
SAlu ALU_AND (SAlu ALU_SLTU (SLit 0) (SOff pb 0))
(SAlu ALU_XOR (SAlu ALU_SLT (SAlu ALU_AND lst (SLit 7)) (SOff pb 0)) (SLit 1)).
Definition qcB_flag (t : nat) (lst : sv) (pb : nat) : sv := SAlu ALU_AND (orz t (qcB_core lst pb)) (SLit 255).

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma qcB_core_zero : forall E lst pb l b1,
U E lst = l -> ew E pb = Z_to_bv 64 b1 -> 0 <= b1 < 256 -> saddr_ok l b1 ->
U E (qcB_core lst pb) = 0.
Proof.
intros E lst pb l b1 Hl Hb Hb1 Hok. unfold qcB_core.
pose proof (U_range E lst) as Rl. unfold M64 in Rl. rewrite Hl in Rl.
assert (Ub : U E (SOff pb 0) = b1) by (apply (U_atom E pb b1 Hb); lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Ub. change (zcanon 0) with 0.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hl, U_SLit, U_SLit, Ub.
change (zcanon 7) with 7. change (zcanon 1) with 1.
rewrite (zcanon_small (Z.land l 7)) by (pose proof (Z_land_upper l 7 ltac:(lia)); lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound l 8 ltac:(lia)) as Hm.
rewrite !swrap64_id by (unfold half64; lia).
destruct Hok as [-> | [Hlt _]].
- cbn. reflexivity.
- replace (0 <? b1) with true by (symmetry; apply Z.ltb_lt; lia).
replace (l mod 8 <? b1) with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.

Lemma qcB_flag_zero : forall E t lst pb l b1,
U E lst = l -> ew E pb = Z_to_bv 64 b1 -> 0 <= b1 < 256 -> saddr_ok l b1 ->
branch_taken BC_EQ (sv_denot E (qcB_flag t lst pb)) (sv_denot E (SLit 0)) = true.
Proof.
intros. rewrite branch_eq_U, U_SLit. unfold qcB_flag. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_orz.
rewrite (qcB_core_zero E lst pb l b1) by assumption. cbn. reflexivity.
Qed.

(* The size-overflow test `not a1,beg; bltu a1,size` with size = len + 1 held as an atom plus one. *)
Lemma br_ovf1_false : forall E (pa pn : nat) d m, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 m ->
0 <= d <= 2 ^ 47 -> 0 <= m -> m + 1 < 2 ^ 32 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 1)) = false.
Proof.
intros E pa pn d m Hd Hm Rd Rm Rm1. rewrite branch_ltu_U, U_not, (U_atom E pa d Hd), (U_atom_off E pn m 1 Hm) by lia.
apply Z.ltb_ge. lia.
Qed.

Lemma br_atom_eq0 : forall E (pa : nat) a, ew E pa = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff pa 0)) (sv_denot E (SLit 0)) = (a =? 0).
Proof. intros E pa a Ha Ra. rewrite branch_eq_U, U_SLit, (U_atom E pa a Ha) by lia. reflexivity. Qed.

(* cgif's icpt_ld8 (A/AE2y.v) for the table of this walk: one 8-byte load whose address the symbolic state
   cannot place, with the loaded word given as an atom of the environment. *)
Lemma ci_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_ci (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof YF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_ci_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfibsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfibsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|exact Hle].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [exact Hbs|].
apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* Every read-only byte of the image lies below the end of the image. *)
Lemma ci_rom_low : forall a, in_rom tfibsegs a -> 0 <= a < TFIB_IMG_END.
Proof.
intros a (sg & Hin & _ & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs))
by exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin).
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez.
assert (Hb0 : 0 <= b) by (subst b; lia). clear Eb Ez.
vm_compute in H. unfold TFIB_IMG_END.
repeat (destruct H as [H|H]; [injection H as <- <-; lia|]). destruct H.
Qed.

Section p.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.

(* AR survives a change of the materialised backing and no change of memory. *)
Lemma ar_same : forall ly S (W : world tfibsegs) mem md mem' md',
AR tfibsegs B ly S W mem md -> (forall z, mem' z = mem z) -> same_but_materialized md md' ->
AR tfibsegs B ly S W mem' md'.
Proof.
intros ly S W mem md mem' md' HAR MEQ Hsbm. pose proof (same_but_materialized_frame md md' Hsbm) as MF.
apply (al_frame _ _ LAWS ly S W mem md mem' md' HAR);
[intros a _ _; apply aview_same; apply MEQ | intros a Hv; erewrite aview_same; [exact Hv | apply MEQ] | | | | exact (YE2y.hs_kept_eq _ _ _ MEQ)];
apply MF.
Qed.

(* AR survives a change of memory inside a present window of the stack. *)
Lemma ar_win : forall ly S (W : world tfibsegs) mem md mem' md' lo hi,
AR tfibsegs B ly S W mem md -> same_but_materialized md md' ->
ly_stk_lo ly <= lo -> hi <= ly_stk_hi ly -> kHighMemBeg <= lo -> hi <= 2 ^ 47 ->
(forall z : word, ~ (lo <= bv_unsigned z < hi) -> mem' z = mem z) ->
(forall a, lo <= a < hi -> apresent (w_H W) mem a) ->
(forall a, lo <= a < hi -> apresent (w_H W) mem' a) ->
AR tfibsegs B ly S W mem' md'.
Proof.
intros ly S W mem md mem' md' lo hi HAR Hsbm Hlo Hhi Hlo2 Hhi2 MEQ P0 P1.
pose proof (same_but_materialized_frame md md' Hsbm) as MF.
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Ha. }
apply (al_frame _ _ LAWS ly S W mem md mem' md' HAR).
- intros a Hr Hown. apply AV; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(lia) Hown).
- intros a Hv. rewrite (YE2y.aview_mod _ mem' a). rewrite (YE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' lo) as [L1|L1]; [rewrite AV by lia; exact Hv|].
destruct (Z_lt_le_dec a' hi) as [L3|L3]; [| rewrite AV by lia; exact Hv].
apply aview_some_of_apresent. apply P1. lia.
- apply MF. - apply MF. - apply MF.
- exact (YE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ P0 ltac:(lia) ltac:(lia)).
Qed.
End p.

(* rt_rom_view survives a change of memory that keeps the view of every byte below [lo], which lies above the image. *)
Lemma rt_rom_view_view : forall B (W : world tfibsegs) mem mem' lo,
TFIB_IMG_END <= lo ->
(forall a, 0 <= a < lo -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
rt_rom_view tfibsegs B W mem -> rt_rom_view tfibsegs B W mem'.
Proof.
intros B W mem mem' lo Hlo AV Hv. apply (rt_rom_view_keep tfibsegs B W mem mem' Hv).
intros a Ha _ _. pose proof (ci_rom_low a Ha) as R. apply AV. lia.
Qed.

(* aread_ok depends on the registers only through the stack pointer. *)
Lemma aread_ok_sp : forall stk (W : world tfibsegs) regs regs' mem x n,
aread_ok tfibsegs stk W regs mem x n -> spZ regs' = spZ regs -> aread_ok tfibsegs stk W regs' mem x n.
Proof.
intros stk W regs regs' mem x n (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hsp.
refine (conj H1 (conj H2 (conj H3 (conj _ (conj H5 (conj H6 H7)))))).
intros a Ha. unfold ascratch_stk. rewrite Hsp. exact (H4 a Ha).
Qed.

(* a prefix of a readable range is readable *)
Lemma ci_shadow_mono : forall x y, x <= y -> shadow_addr x <= shadow_addr y.
Proof. intros x y H. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Lemma ci_hull_sub : forall (rd : Z -> option Z) x n x' n', shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' ->
shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H.
pose proof (ci_shadow_mono x x' H1) as M1. pose proof (ci_shadow_mono (x' + n' - 1) (x + n - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8) by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma aread_ok_prefix : forall stk (W : world tfibsegs) regs mem x n n', aread_ok tfibsegs stk W regs mem x n -> 0 <= n' <= n ->
aread_ok tfibsegs stk W regs mem x n'.
Proof.
intros stk W regs mem x n n' (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hn.
split; [lia|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply H3; lia|].
split; [unfold amem_range in *; lia|]. split; [eapply range_addressable_sub; [exact H5 | lia | lia]|].
intros Hp. apply (ci_hull_sub _ x n x n'); [apply H6; lia | lia | lia | lia].
Qed.

(* The facts a walk reads, carried to a state whose memory agrees outside a stack window [lo, hi) (lib/B/Prog/PaArt.v
   and PaCall.v state the same for the program walks). *)
Definition kept_out (rd rd' : Z -> option Z) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rd' a = rd a.
Lemma ci_ra_kept_win : forall (rd rd' : Z -> option Z) lo hi a n,
(forall s, 0 <= s < 2 ^ 64 -> ~ (lo <= s < hi) -> rd' s = rd s) -> kHighShadowEnd <= lo -> 0 <= a -> a + n <= 2 ^ 47 ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' lo hi a n HK Hlo Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK; unfold shadow_of_addr, SHADOW_OFF, kHighShadowEnd in *.
- split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
- assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma ci_hull_kept_win : forall (rd rd' : Z -> option Z) lo hi a n,
(forall s, 0 <= s < 2 ^ 64 -> ~ (lo <= s < hi) -> rd' s = rd s) -> kHighShadowEnd <= lo -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' lo hi a n HK Hlo Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs) | |]; unfold shadow_addr, SHADOW_OFF, kHighShadowEnd in *.
- pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)). pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)). lia.
- pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.
(* aread_ok at another state: the memory agrees outside [lo, hi), which lies above the range and the shadow, and
   the new scratch window starts at or above lo *)
Lemma aread_ok_kept : forall stk stk' (W : world tfibsegs) regs regs' mem mem' lo hi x n,
kept_out (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') lo hi -> aread_ok tfibsegs stk W regs mem x n ->
(forall a, x <= a < x + n -> ~ (lo <= a < hi)) -> kHighShadowEnd <= lo -> x + n <= 2 ^ 47 ->
(forall a, x <= a < x + n -> ~ (spZ regs' - stk' <= a < spZ regs')) ->
aread_ok tfibsegs stk' W regs' mem' x n.
Proof.
intros stk stk' W regs regs' mem mem' lo hi x n HK (H0 & H1 & H2 & H3 & H4 & H5 & H6) Hx Hk Hx47 Hs.
split; [exact H0|]. split; [exact H1|]. split; [exact H2|]. split.
{ intros a Ha. split; [rewrite (HK a) by (try apply Hx; lia); exact (proj1 (H3 a Ha)) | unfold ascratch_stk; exact (Hs a Ha)]. }
split; [exact H4|]. split.
- exact (ci_ra_kept_win _ _ lo hi x n HK Hk H0 Hx47 H5).
- intros Hn. exact (ci_hull_kept_win _ _ lo hi x n HK Hk H0 Hx47 Hn (H6 Hn)).
Qed.
Lemma astr_at_kept : forall (W : world tfibsegs) mem mem' lo hi p s,
kept_out (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') lo hi -> astr_at tfibsegs W mem p s ->
0 <= p -> p + astr_len s + 1 <= 2 ^ 64 -> (forall a, p <= a < p + astr_len s + 1 -> ~ (lo <= a < hi)) ->
astr_at tfibsegs W mem' p s.
Proof.
intros W mem mem' lo hi p s HK [H1 H2] Hp Hl Hw. split; [|exact H2].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. unfold astr_len in *.
rewrite (HK (p + Z.of_nat i)) by (try apply Hw; lia). exact (H1 i ltac:(rewrite length_app; cbn [length]; lia)).
Qed.
Lemma atail_vis_kept : forall (W : world tfibsegs) mem mem' lo hi e,
kept_out (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') lo hi -> atail_vis tfibsegs W mem e ->
0 <= e -> e - e mod 8 + 8 <= 2 ^ 64 -> (forall a, e < a < e - e mod 8 + 8 -> ~ (lo <= a < hi)) ->
atail_vis tfibsegs W mem' e.
Proof.
intros W mem mem' lo hi e HK H He Hl Hw a Ha. pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
rewrite (HK a) by (try apply Hw; lia). exact (H a Ha).
Qed.
Lemma aguard_ok_kept : forall (W : world tfibsegs) mem mem' lo hi g gd,
kept_out (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) mem') lo hi -> aguard_ok tfibsegs W mem g gd ->
0 <= g -> g + 8 <= lo -> 0 <= gd -> gd + 8 <= lo -> lo < 2 ^ 64 -> aguard_ok tfibsegs W mem' g gd.
Proof.
intros W mem mem' lo hi g gd HK [H1 [c H2]] Hg Hg8 Hd Hd8 Hlo.
split.
- apply (rdword_ext (aview tfibsegs (w_H W) mem)); [|exact H1]. intros i Hi. apply HK; lia.
- exists c. apply (rdword_ext (aview tfibsegs (w_H W) mem)); [|exact H2]. intros i Hi. apply HK; lia.
Qed.

(* the 8-byte word of a byte outside a window whose ends are multiples of 8 is outside the window *)
Lemma tail_out_win : forall e lo hi, lo mod 8 = 0 -> hi mod 8 = 0 -> ~ (lo <= e < hi) ->
forall a, e < a < e - e mod 8 + 8 -> ~ (lo <= a < hi).
Proof.
intros e lo hi Hl Hh He a Ha.
pose proof (Z.div_mod e 8 ltac:(lia)). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod hi 8 ltac:(lia)).
rewrite Hl in *. rewrite Hh in *. intros Hw. apply He.
assert (lo / 8 <= e / 8 < hi / 8) by lia. lia.
Qed.

End f.
(* After a run over read-only regions the memory is the one before it. *)
Ltac ro_mem MEQ :=
lazymatch goal with HF : frame_of _ ?rs ?m0 ?m1, HFr : frame_of _ _ _ _ |- _ =>
let E := fresh "Em" in
pose proof (frame_of_read_only _ rs m0 m1 ltac:(vm_compute; reflexivity) HF) as E; clear HF HFr;
first [ rewrite MEQ in E; clear MEQ; rename E into MEQ | rename E into MEQ ]
end.
(* The model term of a run, named, so that it does not grow over a chain of runs (compile trap #1). *)
Ltac newmd HMD :=
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?X ?m] =>
let mdv := fresh "mdv" in let Hs := fresh "HMDs" in
pose proof (same_but_materialized_trans _ _ _ HMD (with_vm_backing_same m X)) as Hs;
set (mdv := with_vm_backing (m_vm_lazy m) X m) in *; clearbody mdv; clear HMD; rename Hs into HMD
end.
Ltac newmd2 HMD HMD2 :=
lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?X ?m] =>
let mdv := fresh "mdv" in let Hs := fresh "HMDs" in let Hs2 := fresh "HMDs" in
pose proof (same_but_materialized_trans _ _ _ HMD (with_vm_backing_same m X)) as Hs;
pose proof (same_but_materialized_trans _ _ _ HMD2 (with_vm_backing_same m X)) as Hs2;
set (mdv := with_vm_backing (m_vm_lazy m) X m) in *; clearbody mdv;
clear HMD HMD2; rename Hs into HMD; rename Hs2 into HMD2
end.
