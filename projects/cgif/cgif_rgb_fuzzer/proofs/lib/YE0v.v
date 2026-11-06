(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0l YK0s YK0o YQ0k YK1d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ0a YQ04 YQ05 YQ0e YQ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10 YP0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o YA0k.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YE03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE05 YE04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YO01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SB : Z := 0x7fff8000.
Lemma SB_eq : SB = SHADOW_OFF. Proof. img_refl. Qed.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma icpt_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) ->
sym_runN tfxsegs tbl_icpt FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl_icpt tbl_icpt_ok YF8r.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|].
split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Definition ro_chunk (base : Z) (c : Z * N * Z) : YQ0b.chunk := YQ0b.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YQ0b.region :=
YQ0b.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition const_chk {imgk : img} (ly : alayout) (a : Z) (n : N) (v : Z) : bool :=
match cell_lookup (Tfx_const ly) (ANum a) with
| Some (ACell (ANum a') w' (AV (ANum v'))) => (a' =? a) && Nat.eqb w' (N.to_nat n) && (v' =? v)
| _ => false
end.
Lemma const_chk_sound {imgk : img} : forall ly a n v, const_chk ly a n v = true ->
cell_lookup (Tfx_const ly) (ANum a) = Some (ACell (ANum a) (N.to_nat n) (AV (ANum v))).
Proof.
intros ly a n v H. unfold const_chk in H.
destruct (cell_lookup (Tfx_const ly) (ANum a)) as [[e w av]|]; [|img_try (discriminate)].
destruct e; try discriminate. destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. (subst; cbv beta). img_refl.
Qed.
Definition rodata_chk {imgk : img} (ly : alayout) (l : list (Z * Z * list (Z * N * Z))) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
forallb (fun c => const_chk ly (fst (fst r) + fst (fst c)) (snd (fst c)) (snd c)
&& (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r)) l.
Definition icpt_rodata {imgk : img} : list (Z * Z * list (Z * N * Z)) :=
[ ((0xa2cc8 + D_10f0), 8, [(0, 8%N, (0xaae99 + D_10c0))]);
((0xaae98 + D_10c0), 2, [(0, 1%N, 1); (1, 1%N, 1)]);
((0xa2158 + D_10f0), 40, [(0, 8%N, (0xa79b8 + D_10c0)); (8, 8%N, (0xaa1b8 + D_10c0)); (16, 8%N, (0xaaea8 + D_10c0)); (24, 8%N, (0xaaeb0 + D_10c0)); (32, 8%N, (0xaaea0 + D_10c0))]);
((0xaa1b8 + D_10c0), 8, [(0, 8%N, 0x7fff8000)]);
((0xaaea0 + D_10c0), 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
((0xa3ff8 + D_10f0), 16, [(0, 8%N, (0x9b490 + D_10ec)); (8, 8%N, (0x9b894 + D_10ec))]);
((0xa7a00 + D_10c0), 8, [(0, 8%N, 0x1000100000000)]) ].
Lemma icpt_rodata_chk {imgk : img} : forall ly, rodata_chk ly icpt_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Section p. Context {imgk : img}.
Variable B : asyms.
Hypothesis TB : TfxSyms B.
Lemma rodata_ok : forall l ly S (H : word -> bool) mem E,
rodata_chk ly l = true ->
ARm B ly S (aview tfxsegs H mem) -> Forall (region_ok tfxsegs E (mrestrict H mem)) (map ro_region l).
Proof.
intros l ly S H mem E Hc HM. unfold rodata_chk in Hc.
rewrite forallb_forall in Hc. img_apply Forall_map. img_apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
rewrite forallb_forall in Hcs. img_apply Forall_map. img_apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfxsegs E _ 0 (base + off) n (SLit v) v); [img_refl | img_lia | img_lia |].
rewrite Z.add_0_l. img_exact (tfx_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
Qed.
Lemma icpt_rodata_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfxsegs H mem) -> Forall (region_ok tfxsegs E (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros ly S H mem E HM. img_exact (rodata_ok icpt_rodata ly S H mem E (icpt_rodata_chk ly) HM). Qed.
End p.
Lemma ra_granule_zero : forall (rd : Z -> option Z) d n g,
range_addressable rd SHADOW_OFF d n -> d <= 8 * g + 7 < d + n -> 0 <= d -> rd (SB + g) = Some 0.
Proof.
intros rd d n g Hra Hg Hd. destruct (Hra (8 * g + 7) ltac:(img_lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs. replace ((8 * g + 7) / 8) with g in Hs by (img_try (img_apply (Z.div_unique_pos _ 8 g 7); img_lia)).
rewrite SB_eq. destruct Hok as [-> | [Hlt Hs8]]; [img_try (img_exact Hs)|].
exfalso. replace ((8 * g + 7) mod 8) with 7 in Hlt by (img_try (img_apply (Z.mod_unique_pos _ 8 g 7); img_lia)). img_lia.
Qed.
Lemma ra_last : forall (rd : Z -> option Z) d n,
range_addressable rd SHADOW_OFF d n -> 0 < n ->
exists b1, rd (SB + (d + n - 1) / 8) = Some b1 /\ saddr_ok (d + n - 1) b1.
Proof.
intros rd d n Hra Hn. destruct (Hra (d + n - 1) ltac:(img_lia)) as (s & Hs & Hok). exists s. rewrite SB_eq. img_exact (conj Hs Hok).
Qed.
Lemma aview_byte_ex {imgk : img} : forall H mem a v,
aview tfxsegs H mem a = Some v -> exists b : byte, mbyte tfxsegs (mrestrict H mem) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfxsegs (mrestrict H mem) a) as [b|]; [|img_try (discriminate)].
cbn in Hv. injection Hv as <-. exists b. split; [img_refl|]. split; [img_refl|].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H0. cbn in H0. img_lia.
Qed.
Lemma val_mem_of_rdword {imgk : img} : forall H mem a v,
rdword (aview tfxsegs H mem) a = Some v -> val_mem tfxsegs (mrestrict H mem) a 8 v.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfxsegs H mem a) as [b0|] eqn:E0; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 1)) as [b1|] eqn:E1; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 2)) as [b2|] eqn:E2; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 3)) as [b3|] eqn:E3; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 4)) as [b4|] eqn:E4; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 5)) as [b5|] eqn:E5; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 6)) as [b6|] eqn:E6; [|img_try (discriminate)].
destruct (aview tfxsegs H mem (a + 7)) as [b7|] eqn:E7; [|img_try (discriminate)].
injection Hw as <-.
apply aview_byte_ex in E0 as (c0 & M0 & -> & R0). apply aview_byte_ex in E1 as (c1 & M1 & -> & R1).
apply aview_byte_ex in E2 as (c2 & M2 & -> & R2). apply aview_byte_ex in E3 as (c3 & M3 & -> & R3).
apply aview_byte_ex in E4 as (c4 & M4 & -> & R4). apply aview_byte_ex in E5 as (c5 & M5 & -> & R5).
apply aview_byte_ex in E6 as (c6 & M6 & -> & R6). apply aview_byte_ex in E7 as (c7 & M7 & -> & R7).
rewrite ?Z.add_0_r in M0.
set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
assert (Hv : 0 <= v < 2 ^ 64) by (img_try ((subst v; cbv beta); img_lia)).
assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YP0g.le_byte v 8 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YP0g.le_byte. rewrite (Z.mod_small v) by (img_try (cbn; img_lia)).
rewrite Z.shiftr_div_pow2 by img_lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. img_change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [img_try (left; img_lia) | img_lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [img_try (left; img_lia) | img_lia]. }
img_apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |img_lia];
[ img_try (img_change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r)
| img_try (img_change (Z.of_nat 1) with 1) | img_try (img_change (Z.of_nat 2) with 2) | img_try (img_change (Z.of_nat 3) with 3) | img_try (img_change (Z.of_nat 4) with 4)
| img_try (img_change (Z.of_nat 5) with 5) | img_try (img_change (Z.of_nat 6) with 6) | img_try (img_change (Z.of_nat 7) with 7) ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; (subst v; cbv beta); img_lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; (subst v; cbv beta); img_lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; (subst v; cbv beta); img_lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
(bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; (subst v; cbv beta); img_lia.
- rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
(bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; (subst v; cbv beta); img_lia.
- rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
(bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; (subst v; cbv beta); img_lia.
- rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
(bv_unsigned c7)); cbn; (subst v; cbv beta); img_lia.
- rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
0); cbn; (subst v; cbv beta); img_lia.
Qed.
Lemma icpt_ld8 {imgk : img} : forall (W : world tfxsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_icpt (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfxsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfxsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof YF8r.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_icpt_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|img_refl].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfxsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfxsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms rs HS); img_exact Hrs)).
rewrite Hshape. eapply (SRr_step tfxsegs Hwx W); [img_refl | |].
- rewrite restrict_mkst_fx. img_apply (step_ld tfxsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|img_try (img_exact Hle)].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [img_try (img_exact Hbs)|].
img_apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. img_change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. img_change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by img_lia. img_refl.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
img_apply SRr_ret. split; [img_refl|]. eexists _, _. split; [img_refl|]. split; [|img_refl].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (img_try (img_apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; img_change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; img_refl)).
img_apply (st_ok_set_regs tfxsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. img_refl.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [img_refl|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|img_try (constructor)]. cbn [fst snd]. split; [img_try (img_exact Hrd)|].
rewrite getr_same by (img_try (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate)). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
Qed.
Definition MZ_PC {imgk : img} : Z := (0x649b4 + D_2c4).
Definition MZ_CLOB : list (bv 5) := [10%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv].
Definition ss_after_mz (ss : sstate) (rs : smem) (k : nat) (pc : Z) : sstate :=
let s1 := ss_after_stretch ss rs k MZ_CLOB pc in
mkSS (ss_pc s1) (sr_set (ss_regs s1) 10 (SLit 1)) (ss_mem s1) (ss_resv s1) (ss_facts s1).
Lemma mz_entry_eq {imgk : img} : tfx_mem_is_zero_entry = Z_to_bv 64 MZ_PC.
Proof. img_apply bv_eq. img_case; vm_compute. all: img_refl. Qed.
Lemma aview0_rdn1 {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> aview tfxsegs H m a = Some 0 -> rdn tfxsegs (mrestrict H m) (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 0].
Proof.
intros H m a Ha Hv. img_apply (proj2 (rdn_mbytes tfxsegs _ 1 a [Z_to_bv 8 0])). split; [img_refl|].
intros i Hi. replace i with 0%nat by img_lia. rewrite Z.add_0_r. cbn [nth_error].
rewrite (YF8r.aview_byte H m a 0 Hv). img_refl.
Qed.
Lemma icpt_memisz {imgk : img} : forall (W : world tfxsegs) E ss ms md (k : nat) (rs : smem) (beg N spv ra : Z),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = MZ_PC ->
ss_atoms_lt k ss = true -> regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 beg -> sv_denot E (sr_get (ss_regs ss) 11) = Z_to_bv 64 N ->
sv_denot E (sr_get (ss_regs ss) 2) = Z_to_bv 64 spv -> sv_denot E (sr_get (ss_regs ss) 1) = Z_to_bv 64 ra ->
0 <= N <= 2 ^ 40 -> 0 <= beg -> beg + N + 8 <= 2 ^ 64 -> TFX_IMG_END + 8 <= spv < 2 ^ 64 -> 0 <= ra < 2 ^ 64 -> ret_ok (Z_to_bv 64 ra) ->
(beg + N <= spv - 8 \/ spv <= beg) ->
(forall x, spv - 8 <= x < spv -> writable_at tfxsegs (mrestrict (w_H W) (ms_mem ms)) x) ->
(forall a, beg <= a < beg + N -> aview tfxsegs (w_H W) (ms_mem ms) a = Some 0) ->
Forall (fun r => 0 <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r /\ base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= 2 ^ 64 /\
(base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= spv - 8 \/ spv <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r) /\
YQ0b.r_lo r <= YQ0b.r_wlo r /\ YQ0b.r_whi r <= YQ0b.r_hi r) rs ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2, c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) MZ_CLOB)) (ss_after_mz ss rs k ra) (restrict (w_H W) ms2) /\
(forall x : word, ~ (spv - 8 <= bv_unsigned x < spv) -> ms_mem ms2 x = ms_mem ms x) /\
(forall x : word, spv - 8 <= bv_unsigned x < spv -> ms_mem ms2 x <> None)).
Proof.
intros W E ss ms md k rs beg N spv ra HS Hrv Hpc Hat Hwf Hnc Hma Hsub R10 R11 R2 R1 HN Hbeg Hnw Hsp Hra Hret Hdisj Hslot Hz Hoff.
pose proof YF8r.Hwx_tfa as Hwx. unfold TFX_IMG_END in Hsp.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
assert (G10 : getr (ms_regs ms) 10 = Z_to_bv 64 beg) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms 10 HS); img_exact R10)).
assert (G11 : getr (ms_regs ms) 11 = Z_to_bv 64 N) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms 11 HS); img_exact R11)).
assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 spv) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms 2 HS); img_exact R2)).
assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 ra) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms 1 HS); img_exact R1)).
set (m0 := mrestrict (w_H W) (ms_mem ms)).
assert (Hstk : store_ok tfxsegs m0 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 spv) - 8)) 8 = true).
{ rewrite unsigned_lit_small by img_lia. img_apply (store_ok_of_all tfxsegs 8 m0 (Z_to_bv 64 (spv - 8)));
[img_try (rewrite unsigned_lit_small by img_lia; cbn [Z.of_nat Pos.to_nat]; img_lia) | ].
intros x Hx. rewrite unsigned_lit_small in Hx by img_lia. unfold writable_at in Hslot.
specialize (Hslot (bv_unsigned x) ltac:(img_try (cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hx; img_lia))).
rewrite Z_to_bv_bv_unsigned in Hslot. img_exact Hslot. }
destruct (tfx_mem_is_zero m0 (Z_to_bv 64 beg) (Z_to_bv 64 spv) N (seg_rom tfxsegs) (ms_regs ms) (Z_to_bv 64 ra)
HN ltac:(img_try (rewrite unsigned_lit_small by img_lia; img_lia)) ltac:(img_try (rewrite unsigned_lit_small by img_lia; img_lia)) Hstk
ltac:(img_try (rewrite !unsigned_lit_small by img_lia; img_lia))
ltac:(img_try (intros a Ha; rewrite unsigned_lit_small in Ha by img_lia; rewrite <- (Z_to_bv_bv_unsigned 64 a);
img_apply aview0_rdn1; [img_try (pose proof (u64_range a); img_lia) | img_try (img_apply Hz; img_lia)]))
Hret G1 G2 G10 G11) as (regs' & Hms & Hagree & Ha0 & Hsp' & Hra').
rewrite mz_entry_eq in Hms. unfold MZ_PC in Hms.
set (m1 := wbytes m0 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 spv) - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ra))) in Hms.
assert (M1out : forall x : word, ~ (spv - 8 <= bv_unsigned x < spv) -> m1 x = m0 x).
{ intros x Hx. (subst m1; cbv beta). rewrite unsigned_lit_small by img_lia.
assert (L8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 ra))) = 8) by (img_try (rewrite length_N_to_le_bytes; img_refl)).
destruct (Z_lt_le_dec (bv_unsigned x) (spv - 8)) as [L|L].
- img_apply wbytes_below; rewrite ?L8, unsigned_lit_small by img_lia; img_lia.
- img_apply wbytes_above. rewrite ?L8, unsigned_lit_small by img_lia. img_lia. }
all: idtac.
pose proof (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 rs ra MZ_CLOB HS Hrv Hat Hwf Hnc Hma Hsub
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))) as HS2.
rewrite Hshape in HS2. rewrite restrict_mkst_fx in HS2. cbn [ms_regs ms_mem mkst] in HS2.
specialize (HS2 ltac:(img_try (intros r Hr; img_apply Hagree; img_exact (reg_in_false r MZ_CLOB Hr)))).
assert (KEPT : Forall (region_kept tfxsegs E m0 m1) rs).
{ img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hoff r Hr) as (O1 & O2 & O3 & O4 & O5).
img_apply (region_kept_outside tfxsegs E m0 m1 r (spv - 8) 8).
- intros x Hx. img_apply M1out. img_lia.
- (subst m1; cbv beta). img_apply wbytes_grows.
- img_exact O1. - img_lia. - img_exact O2. - img_exact O4. - img_exact O5. }
specialize (HS2 KEPT).
rewrite Hshape. eapply (SRr_msteps_st tfxsegs Hwx W (havoc E k (map (getr regs') MZ_CLOB)) (ss_after_mz ss rs k ra) _ _ md).
- rewrite restrict_mkst_fx. img_exact Hms.
- unfold ss_after_mz. cbv zeta.
img_apply (st_ok_pin_reg _ (ss_after_stretch ss rs k MZ_CLOB ra) _ 10 (SLit 1)); [img_try (img_exact HS2) | img_try (intros H'; discriminate H') |].
cbn [sv_denot ms_regs mkst]. rewrite Ha0. img_refl.
- intros ms' mat' HS' Hvis Hhid Hregs. img_apply SRr_ret. split; [img_refl|]. exists ms', mat'. split; [img_refl|].
rewrite Hregs. split; [img_try (img_exact HS')|]. split.
+ intros x Hx. destruct (w_H W x) eqn:Hh.
* rewrite (Hhid x Hh). img_refl.
* rewrite (Hvis x Hh). cbn [ms_mem mkst]. rewrite (M1out x Hx). (subst m0; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
+ intros x Hx. pose proof (Hslot (bv_unsigned x) Hx) as Wx. unfold writable_at, wview in Wx. rewrite Z_to_bv_bv_unsigned in Wx.
destruct (w_H W x) eqn:Hh.
* exfalso. img_apply Wx. (subst m0; cbv beta). unfold mrestrict. rewrite Hh.
rewrite (tfx_find_segment_none_high (bv_unsigned x)) by (img_try (unfold TFX_IMG_END in *; img_lia)). img_refl.
* rewrite (Hvis x Hh). cbn [ms_mem mkst]. (subst m1 m0; cbv beta).
destruct (mrestrict (w_H W) (ms_mem ms) x) as [b|] eqn:Eb.
2:{ exfalso. img_apply Wx. rewrite (tfx_find_segment_none_high (bv_unsigned x)) by (img_try (unfold TFX_IMG_END in *; img_lia)). img_refl. }
apply (wbytes_grows (word_to_le_bytes 8 (Z_to_bv 64 ra)) (mrestrict (w_H W) (ms_mem ms)) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 spv) - 8)) x).
rewrite Eb. discriminate.
Qed.
Fixpoint orz (t : nat) (c : sv) : sv := match t with O => c | S t' => SAlu ALU_OR (SLit 0) (orz t' c) end.
Definition qc_core (pa pn pb : nat) : sv :=
SAlu ALU_AND (SAlu ALU_SLTU (SLit 0) (SOff pb 0))
(SAlu ALU_XOR (SAlu ALU_SLT (SAlu ALU_AND (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) (SLit 7)) (SOff pb 0)) (SLit 1)).
Definition qc_flag (t : nat) (pa pn pb : nat) : sv := SAlu ALU_AND (orz t (qc_core pa pn pb)) (SLit 255).
Lemma U_orz : forall E t c, U E (orz t c) = U E c.
Proof.
intros E t c. induction t as [|t IH]; [img_refl|]. cbn [orz]. rewrite U_SAlu, IH, U_SLit. cbn [zalu_raw].
img_change (zcanon 0) with 0. rewrite Z.lor_0_l. img_apply zcanon_small. pose proof (U_range E c). unfold M64 in *. img_lia.
Qed.
Lemma U_dn1 : forall E pa pn d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 < n -> d + n <= 2 ^ 63 ->
U E (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) = d + n - 1.
Proof.
intros E pa pn d n Ha Hn Hd Hn0 Hdn.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E pn n Hn) by img_lia. rewrite U_SOff, Ha, unsigned_lit_small by img_lia.
unfold zcanon, M64. destruct (Z.eq_dec d 0) as [->|Hne].
- img_change ((0 + -1) mod 2 ^ 64) with (2 ^ 64 - 1). replace (2 ^ 64 - 1 + n) with ((n - 1) + 1 * 2 ^ 64) by img_lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by img_lia. img_lia.
- rewrite (Z.mod_small (d + -1)) by img_lia. rewrite Z.mod_small by img_lia. img_lia.
Qed.
Lemma qc_core_zero : forall E pa pn pb d n b1,
ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> ew E pb = Z_to_bv 64 b1 ->
0 <= d -> 0 < n -> d + n <= 2 ^ 63 -> 0 <= b1 < 256 -> saddr_ok (d + n - 1) b1 ->
U E (qc_core pa pn pb) = 0.
Proof.
intros E pa pn pb d n b1 Ha Hn Hb Hd Hn0 Hdn Hb1 Hok. unfold qc_core.
assert (Ub : U E (SOff pb 0) = b1) by (img_try (img_apply (U_atom E pb b1 Hb); img_lia)).
pose proof (U_dn1 E pa pn d n Ha Hn Hd Hn0 Hdn) as Us.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Ub. img_change (zcanon 0) with 0.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Us, U_SLit, U_SLit, Ub.
img_change (zcanon 7) with 7. img_change (zcanon 1) with 1.
rewrite (zcanon_small (Z.land (d + n - 1) 7)) by (img_try (pose proof (Z_land_upper (d + n - 1) 7 ltac:(img_lia)); img_lia)).
img_change 7 with (Z.ones 3). rewrite Z.land_ones by img_lia. img_change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)) as Hm.
rewrite !swrap64_id by (img_try (unfold half64; img_lia)).
destruct Hok as [-> | [Hlt _]].
- cbn. img_refl.
- replace (0 <? b1) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia)).
replace ((d + n - 1) mod 8 <? b1) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia)). cbn. img_refl.
Qed.
Lemma qc_flag_zero : forall E t pa pn pb d n b1,
ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> ew E pb = Z_to_bv 64 b1 ->
0 <= d -> 0 < n -> d + n <= 2 ^ 63 -> 0 <= b1 < 256 -> saddr_ok (d + n - 1) b1 ->
branch_taken BC_EQ (sv_denot E (qc_flag t pa pn pb)) (sv_denot E (SLit 0)) = true.
Proof.
intros. rewrite branch_eq_U, U_SLit. unfold qc_flag. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_orz.
rewrite (qc_core_zero E pa pn pb d n b1) by assumption. cbn. img_refl.
Qed.
Lemma rp_b1_zero : forall E pb, ew E pb = Z_to_bv 64 0 ->
branch_taken BC_EQ (sv_denot E (SOff pb 0)) (sv_denot E (SLit 0)) = true.
Proof. intros E pb Hb. rewrite branch_eq_U, U_SLit, (U_atom E pb 0 Hb) by img_lia. img_refl. Qed.
Lemma rp_b1_nonzero : forall E pb b1, ew E pb = Z_to_bv 64 b1 -> 0 < b1 < 256 ->
branch_taken BC_EQ (sv_denot E (SOff pb 0)) (sv_denot E (SLit 0)) = false.
Proof. intros E pb b1 Hb Hr. rewrite branch_eq_U, U_SLit, (U_atom E pb b1 Hb) by img_lia. img_change (zcanon 0) with 0. img_apply (proj2 (Z.eqb_neq b1 0)). img_lia. Qed.
Lemma rp_blt_last : forall E pa pn pb d n b1,
ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> ew E pb = Z_to_bv 64 b1 ->
0 <= d -> 0 < n -> d + n <= 2 ^ 63 -> (d + n - 1) mod 8 < b1 < 8 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) (SLit 7))) (sv_denot E (SOff pb 0)) = true.
Proof.
intros E pa pn pb d n b1 Ha Hn Hb Hd Hn0 Hdn Hlt.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned. fold (U E (SOff pb 0)).
fold (U E (SAlu ALU_AND (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) (SLit 7))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_dn1 E pa pn d n Ha Hn Hd Hn0 Hdn), U_SLit, (U_atom E pb b1 Hb) by img_lia.
img_change (zcanon 7) with 7.
rewrite (zcanon_small (Z.land (d + n - 1) 7)) by (img_try (pose proof (Z_land_upper (d + n - 1) 7 ltac:(img_lia)); img_lia)).
img_change 7 with (Z.ones 3). rewrite Z.land_ones by img_lia. img_change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(img_lia)) as Hm.
rewrite !swrap64_id by (img_try (unfold half64; img_lia)). img_apply Z.ltb_lt. img_lia.
Qed.
Lemma aview_vis_byte {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a,
aview tfxsegs H m a <> None -> exists v, aview tfxsegs H m a = Some v /\ 0 <= v < 256.
Proof.
intros H m a Hv. unfold aview in *. destruct (mbyte tfxsegs (mrestrict H m) a) as [b|]; [|img_try (exfalso; img_apply Hv; img_refl)].
exists (bv_unsigned b). split; [img_refl|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. img_lia.
Qed.
Lemma hull_rdword {imgk : img} : forall (H : word -> bool) (m : word -> option byte) x n h,
shadow_hull_vis (aview tfxsegs H m) x n ->
shadow_addr x / 8 * 8 <= h -> h + 8 <= shadow_addr (x + n - 1) / 8 * 8 + 8 ->
exists q, rdword (aview tfxsegs H m) h = Some q /\ 0 <= q < 2 ^ 64.
Proof.
intros H m x n h Hh Hlo Hhi.
assert (B : forall k, 0 <= k < 8 -> exists v, aview tfxsegs H m (h + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. img_apply aview_vis_byte. img_apply Hh. img_lia. }
destruct (B 0 ltac:(img_lia)) as (v0 & E0 & R0). destruct (B 1 ltac:(img_lia)) as (v1 & E1 & R1).
destruct (B 2 ltac:(img_lia)) as (v2 & E2 & R2). destruct (B 3 ltac:(img_lia)) as (v3 & E3 & R3).
destruct (B 4 ltac:(img_lia)) as (v4 & E4 & R4). destruct (B 5 ltac:(img_lia)) as (v5 & E5 & R5).
destruct (B 6 ltac:(img_lia)) as (v6 & E6 & R6). destruct (B 7 ltac:(img_lia)) as (v7 & E7 & R7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. split; [img_refl|]. img_lia.
Qed.
Lemma wbytes_inside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned a)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [img_try (cbn [length] in Hx; img_lia)|].
cbn [length] in Hnw, Hx. cbn [wbytes].
destruct rest as [|b' rest'].
{ cbn [wbytes length] in *. assert (Heq : bv_unsigned x = bv_unsigned a) by img_lia.
rewrite Heq, Z.sub_diag. replace x with a by (img_try (img_apply bv_eq; img_lia)). rewrite bv_eqb_refl. img_refl. }
cbn [length] in Hnw, Hx.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (img_try (img_apply u_add1; img_lia)).
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- rewrite (wbytes_below (b' :: rest') _ (a + 1) x); [| img_try (cbn [length]; rewrite Hu1; img_lia) | img_try (rewrite Hu1; img_lia)].
rewrite Heq, Z.sub_diag. replace x with a by (img_try (img_apply bv_eq; img_lia)). rewrite bv_eqb_refl. img_refl.
- rewrite (IH _ (a + 1)%bv x) by (img_try (cbn [length]; rewrite Hu1; img_lia)). rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by img_lia.
img_refl.
Qed.
Lemma lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [img_try (rewrite Z.log2_nonpos; img_lia)|]. img_apply (proj1 (Z.log2_lt_pow2 a n ltac:(img_lia))). img_lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by img_lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by img_apply Z.land_comm. rewrite E.
rewrite Z.land_ones by img_lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by img_lia. rewrite Z.mod_add by img_lia. rewrite Z.mod_small by img_lia. img_lia.
Qed.
Lemma U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. img_change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite lxor_ones by img_lia.
img_change (Z.ones 64) with (2 ^ 64 - 1). img_apply zcanon_small. img_lia.
Qed.
Lemma U_and_m8 : forall E v, U E (SAlu ALU_AND v (SLit (-8))) = U E v - U E v mod 8.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. pose proof (U_range E v) as Hr. unfold M64 in Hr.
replace (zcanon (-8)) with (Z.land (Z.ones 64) (- 2 ^ 3)) by (img_try ((img_case; vm_compute); img_refl)).
rewrite Z.land_assoc, Z.land_ones by img_lia. rewrite (Z.mod_small (U E v)) by img_lia. rewrite land_neg_pow2 by img_lia.
img_change (2 ^ 3) with 8. img_apply zcanon_small. pose proof (Z.mod_pos_bound (U E v) 8 ltac:(img_lia)). img_lia.
Qed.
Lemma U_add2 : forall E pa pn d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 <= n -> d + n < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0)) = d + n.
Proof.
intros E pa pn d n Ha Hn Hd Hn0 Hdn. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E pa d Ha), (U_atom E pn n Hn) by img_lia. img_apply zcanon_small. img_lia.
Qed.
Lemma br_ovf_false : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 0)) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn. rewrite branch_ltu_U, U_not, (U_atom E pa d Hd), (U_atom E pn n Hn) by img_lia.
img_apply Z.ltb_ge. img_lia.
Qed.
Lemma br_cls_small : forall E n, ew E 12 = Z_to_bv 64 n -> 1 <= n <= 64 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff 12 (-65))) = false.
Proof.
intros E n Hn Rn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by img_lia.
unfold zcanon, M64. img_change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65).
replace ((n + -65) mod 2 ^ 64) with (n - 65 + 2 ^ 64).
2:{ replace (n + -65) with ((n - 65 + 2 ^ 64) + (-1) * 2 ^ 64) by img_lia. rewrite Z.mod_add by img_lia. symmetry. img_apply Z.mod_small. img_lia. }
cbn [negb]. replace (2 ^ 64 - 65 <? n - 65 + 2 ^ 64) with true by (img_try (symmetry; img_apply Z.ltb_lt; img_lia)). img_refl.
Qed.
Lemma br_cls_zero : forall E, ew E 12 = Z_to_bv 64 0 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff 12 (-65))) = true.
Proof.
intros E Hn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by img_lia.
unfold zcanon, M64. img_change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65). img_change ((0 + -65) mod 2 ^ 64) with (2 ^ 64 - 65).
rewrite Z.ltb_irrefl. img_refl.
Qed.
Lemma br_n_zero : forall E, ew E 12 = Z_to_bv 64 0 ->
branch_taken BC_NE (sv_denot E (SOff 12 0)) (sv_denot E (SLit 0)) = false.
Proof. intros E Hn. rewrite branch_ne_U, U_SLit, (U_atom E 12 0 Hn) by img_lia. img_refl. Qed.
Lemma U_hull_addr : forall E (pg : nat) g0 c, ew E pg = Z_to_bv 64 g0 -> 0 <= g0 -> 0 <= c -> g0 + c + 8 < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff pg c) (SLit (-8))) = Z_to_bv 64 ((g0 + c) / 8 * 8).
Proof.
intros E pg g0 c Hg Hg0 Hc Hhi.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal. change (bv_unsigned (sv_denot E ?v)) with (U E v).
rewrite U_and_m8, (U_atom_off E pg g0 c Hg) by img_lia.
pose proof (Z.div_mod (g0 + c) 8 ltac:(img_lia)). img_lia.
Qed.
Lemma lor_lt_pow2 : forall a b n, 0 < n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
intros a b n Hn Ha Hb. split; [img_try (img_apply Z.lor_nonneg; img_lia)|].
destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [img_try (rewrite E; img_lia)|].
img_apply Z.log2_lt_pow2. { pose proof (Z.lor_nonneg a b). img_lia. }
rewrite Z.log2_lor by img_lia.
img_apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|]; [img_try (rewrite Z.log2_nonpos; img_lia)|]. img_apply Z.log2_lt_pow2; img_lia.
- destruct (Z.eq_dec b 0) as [->|]; [img_try (rewrite Z.log2_nonpos; img_lia)|]. img_apply Z.log2_lt_pow2; img_lia.
Qed.
Lemma br_hull : forall E (p1 p2 : nat) q1 q2, ew E p1 = Z_to_bv 64 q1 -> ew E p2 = Z_to_bv 64 q2 -> 0 <= q1 < 2 ^ 64 -> 0 <= q2 < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SOff p2 0) (SOff p1 0))) (sv_denot E (SLit 0)) = negb (Z.lor q2 q1 =? 0).
Proof.
intros E p1 p2 q1 q2 H1 H2 R1 R2. rewrite branch_ne_U, U_SLit, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E p1 q1 H1), (U_atom E p2 q2 H2) by img_lia. img_change (zcanon 0) with 0.
rewrite zcanon_small; [img_refl|]. img_apply lor_lt_pow2; img_lia.
Qed.
Lemma br_end_low : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 <= n -> d + n <= 2147450879 ->
branch_taken BC_GEU (sv_denot E (SLit 2147450879)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = true.
Proof.
intros E pa pn d n Hd Hn Rd Rn Hdn. rewrite branch_geu_U, U_SLit, (U_add2 E pa pn d n Hd Hn) by img_lia.
img_change (zcanon 2147450879) with 2147450879. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by img_lia. img_refl.
Qed.
Lemma br_end_high : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 <= n -> d + n <= 2 ^ 47 - 1 ->
branch_taken BC_LTU (sv_denot E (SLit 140737488355327)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn Hdn. rewrite branch_ltu_U, U_SLit, (U_add2 E pa pn d n Hd Hn) by img_lia.
img_change (zcanon 140737488355327) with (2 ^ 47 - 1). img_apply Z.ltb_ge. img_lia.
Qed.
Lemma br_beg_lt_end : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 < n -> d + n < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pa 0)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn Hdn. rewrite branch_geu_U, (U_atom E pa d Hd), (U_add2 E pa pn d n Hd Hn) by img_lia.
cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by img_lia. img_refl.
Qed.
Lemma br_sbeg_lt_send : forall E (pu pe : nat) gu ge, ew E pu = Z_to_bv 64 gu -> ew E pe = Z_to_bv 64 ge -> 0 <= gu < ge -> ge + SB < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pu SB)) (sv_denot E (SOff pe SB)) = false.
Proof.
intros E pu pe gu ge Hu He R1 R2. unfold SB in *. rewrite branch_geu_U, (U_atom_off E pu gu 2147450880 Hu), (U_atom_off E pe ge 2147450880 He) by img_lia.
cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by img_lia. img_refl.
Qed.
Lemma val_mem1_of_aview {imgk : img} : forall (H : word -> bool) (m : word -> option byte) a v,
aview tfxsegs H m a = Some v -> val_mem tfxsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by img_lia. rewrite Z.add_0_r.
destruct (aview_vis_byte H m a ltac:(img_try (rewrite Hv; discriminate))) as (v' & Hv' & Hr). rewrite Hv in Hv'. injection Hv' as <-.
rewrite (YF8r.aview_byte H m a v Hv). f_equal. img_apply bv_eq.
rewrite (le_byte_small v 1 0) by (img_try (cbn; img_lia)). cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. img_refl.
Qed.
Lemma U_mz_len : forall E (pu pe : nat) gu ge, ew E pu = Z_to_bv 64 gu -> ew E pe = Z_to_bv 64 ge -> 0 <= gu <= ge -> ge < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff pu 0) (SLit (-1))) (SOff pe 0)) = Z_to_bv 64 (ge - gu).
Proof.
intros E pu pe gu ge Hu He Hle Hhi.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal. change (bv_unsigned (sv_denot E ?v)) with (U E v).
rewrite (U_zev E) by img_refl. cbn [zev svpure].
unfold rho_of. rewrite Hu, He, !unsigned_lit_small by img_lia. rewrite !Z.add_0_r.
cbn [zmd_raw zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small gu), (Z.mod_small ge) by img_lia. img_change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (gu * (2 ^ 64 - 1)) with ((- gu) + gu * 2 ^ 64) by img_lia. rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_l. replace (- gu + ge) with (ge - gu) by img_lia. img_apply Z.mod_small. img_lia.
Qed.
Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. img_apply ret_ok_even. rewrite unsigned_lit_small by img_lia. img_exact He. Qed.
Lemma U_srl3 : forall E v, U E (SAlu ALU_SRL v (SLit 3)) = U E v / 8.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. img_change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 3) with 8. pose proof (U_range E v). unfold M64 in *.
img_apply zcanon_small. split; [img_try (img_apply Z.div_pos; img_lia) | img_try (img_apply Z.div_lt_upper_bound; img_lia)].
Qed.
Lemma icpt_phase_to {imgk : img} : forall (W : world tfxsegs) E stop ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfxsegs tbl_icpt FUEL stop ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfxsegs tbl_icpt tbl_icpt_ok YF8r.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|].
split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Lemma rdn_of_vis {imgk : img} : forall (m : word -> option byte) a (n : nat),
0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, 0 <= i < Z.of_nat n -> mbyte tfxsegs m (a + i) <> None) ->
exists bs, rdn tfxsegs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
forall i, (i < n)%nat -> mbyte tfxsegs m (a + Z.of_nat i) = Some (nth i bs 0%bv).
Proof.
intros m a n Ha Hn Hv.
set (bs := map (fun i => match mbyte tfxsegs m (a + Z.of_nat i) with Some b => b | None => 0%bv end) (seq 0 n)).
assert (L : length bs = n) by (img_try ((subst bs; cbv beta); rewrite length_map, length_seq; img_refl)).
assert (B : forall i, (i < n)%nat -> mbyte tfxsegs m (a + Z.of_nat i) = Some (nth i bs 0%bv)).
{ intros i Hi. (subst bs; cbv beta).
assert (NE : nth_error (map (fun i0 : nat => match mbyte tfxsegs m (a + Z.of_nat i0) with Some b => b | None => 0%bv end) (seq 0 n)) i
= Some (match mbyte tfxsegs m (a + Z.of_nat i) with Some b => b | None => 0%bv end)).
{ rewrite nth_error_map, nth_error_seq. replace (i <? n)%nat with true by (img_try (symmetry; img_apply Nat.ltb_lt; img_exact Hi)). img_refl. }
rewrite (nth_error_nth _ _ _ NE).
destruct (mbyte tfxsegs m (a + Z.of_nat i)) as [b|] eqn:Eb; [img_refl|]. exfalso. img_exact (Hv (Z.of_nat i) ltac:(img_lia) Eb). }
exists bs. split; [|img_try (split; [img_exact L | img_exact B])].
img_apply (proj2 (rdn_mbytes tfxsegs m n a bs)). split; [img_try (img_exact L)|]. intros i Hi. rewrite (B i Hi). symmetry. img_apply nth_error_nth'. img_lia.
Qed.
Lemma writable_at_same {imgk : img} : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at tfxsegs m a -> writable_at tfxsegs m' a.
Proof. intros m m' a He Hw. unfold writable_at, wview in *. rewrite He. img_exact Hw. Qed.
Lemma hidden_not_writable {imgk : img} : forall (W : world tfxsegs) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> w_H W (Z_to_bv 64 a) = true -> ~ writable_at tfxsegs (mrestrict (w_H W) m) a.
Proof.
intros W m a Ha Hh Hw. unfold writable_at, wview, mrestrict in Hw. rewrite Hh in Hw.
pose proof (w_Hoff W (Z_to_bv 64 a) Hh) as Hoff. rewrite Hoff in Hw. img_apply Hw. img_refl.
Qed.
Definition Env (regs : bvmap 5 word) (extra : list Z) : env := Ereg regs (map (Z_to_bv 64) extra).
Lemma Env_reg : forall regs extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env regs extra) i = getr regs r.
Proof. intros regs extra i r Hi. unfold Env. img_apply ew_Ereg_nat. img_exact Hi. Qed.
Lemma Env_x : forall regs extra j z, nth_error extra j = Some z -> ew (Env regs extra) (32 + j) = Z_to_bv 64 z.
Proof.
intros regs extra j z Hj. unfold Env. rewrite (ew_Ereg_extra regs _ j).
revert extra Hj. induction j as [|j IH]; intros [|e l] Hj; cbn in Hj |- *; try discriminate.
- injection Hj as ->. img_refl.
- img_apply IH. img_exact Hj.
Qed.
Definition DROPC (ss : sstate) : sstate := set_facts ss (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))).
Lemma st_ok_dropc {imgk : img} : forall E ss ms, st_ok tfxsegs E ss ms -> st_ok tfxsegs E (DROPC ss) ms.
Proof.
intros E ss ms HS. unfold DROPC. img_apply st_ok_set_facts; [img_try (img_exact HS)|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HA & HC & HL)). split; [img_try (img_exact HA)|]. split; [| img_try (img_exact HL)]. cbn. img_exact I.
Qed.
Lemma br_eq_atoms : forall E (pa pb : nat) a b, ew E pa = Z_to_bv 64 a -> ew E pb = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff pa 0)) (sv_denot E (SOff pb 0)) = (a =? b).
Proof. intros E pa pb a b Ha Hb Ra Rb. rewrite branch_eq_U, (U_atom E pa a Ha), (U_atom E pb b Hb) by img_lia. img_refl. Qed.
Lemma br_geu_atom_add2 : forall E (pb pa pn : nat) b a n, ew E pb = Z_to_bv 64 b -> ew E pa = Z_to_bv 64 a -> ew E pn = Z_to_bv 64 n ->
0 <= b < 2 ^ 64 -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pb 0)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = negb (b <? a + n).
Proof. intros. rewrite branch_geu_U, (U_atom E pb b), (U_add2 E pa pn a n) by (img_try (try assumption; img_lia)). img_refl. Qed.
Lemma br_ltu_atom_add2 : forall E (pb pa pn : nat) b a n, ew E pb = Z_to_bv 64 b -> ew E pa = Z_to_bv 64 a -> ew E pn = Z_to_bv 64 n ->
0 <= b < 2 ^ 64 -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff pb 0)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = (b <? a + n).
Proof. intros. rewrite branch_ltu_U, (U_atom E pb b), (U_add2 E pa pn a n) by (img_try (try assumption; img_lia)). img_refl. Qed.
Definition hs_kept (H : word -> bool) (mem mem' : word -> option byte) : Prop :=
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Lemma in_band_rw_u64 : forall a, in_band_rw a -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. img_lia. Qed.
Lemma hs_kept_win : forall (H : word -> bool) (m0 mem mem' : word -> option byte) (lo hi plo phi : Z),
(forall z : word, ~ (lo <= bv_unsigned z < hi) -> mem' z = mem z) ->
(forall a, plo <= a < phi -> apresent H m0 a) -> plo <= lo -> hi <= phi ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros H m0 mem mem' lo hi plo phi MEQ PRES Hlo Hhi a Ha Hh. pose proof (in_band_rw_u64 a Ha) as Hr.
destruct (Z_lt_le_dec a lo) as [L1|L1]; [img_try (rewrite MEQ; [img_refl | rewrite unsigned_lit_small by img_lia; img_lia])|].
destruct (Z_lt_le_dec a hi) as [L2|L2]; [| img_try (rewrite MEQ; [img_refl | rewrite unsigned_lit_small by img_lia; img_lia])].
exfalso. destruct (PRES a ltac:(img_lia)) as [Hf _]. rewrite Hf in Hh. discriminate.
Qed.
Lemma hs_kept_eq : forall (H : word -> bool) (mem mem' : word -> option byte),
(forall z : word, mem' z = mem z) ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof. intros H mem mem' MEQ a _ _. img_apply MEQ. Qed.
Lemma hs_kept_unrestrict : forall (H : word -> bool) (m mr : word -> option byte),
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> munrestrict H m mr (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros H m mr a _ Hh. unfold munrestrict. rewrite Hh. img_refl. Qed.
Lemma hs_kept_trans : forall (H : word -> bool) (m1 m2 m3 : word -> option byte),
hs_kept H m1 m2 -> hs_kept H m2 m3 -> hs_kept H m1 m3.
Proof. intros H m1 m2 m3 A12 A23 a Ha Hh. rewrite (A23 a Ha Hh). img_exact (A12 a Ha Hh). Qed.
Lemma hs_kept_refl : forall (H : word -> bool) (m : word -> option byte), hs_kept H m m.
Proof. intros H m a _ _. img_refl. Qed.
Lemma Z_to_bv64_of_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
intros a. img_apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by img_lia. img_refl.
Qed.
Lemma aview_mod {imgk : img} : forall H (m : word -> option byte) a, aview tfxsegs H m a = aview tfxsegs H m (a mod 2 ^ 64).
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv64_of_mod. img_refl. Qed.
Lemma apresent_mod : forall H (m : word -> option byte) a, apresent H m a = apresent H m (a mod 2 ^ 64).
Proof. intros H m a. unfold apresent. rewrite Z_to_bv64_of_mod. img_refl. Qed.
Lemma asan_consts : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ kHighShadowEnd = 0x10007fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
kHighMemEnd = 0x800000000000 /\ kLowMemEnd = 0x7fff8000.
Proof. split; [img_try (img_exact (proj1 alloc_ceiling_val)) | img_try (repeat split; img_refl)]. Qed.
Lemma aview_some_of_apresent {imgk : img} : forall H mem a, apresent H mem a -> aview tfxsegs H mem a <> None.
Proof.
intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma aregs_preserved_of_st_ok {imgk : img} : forall H E ss ms regs0 extra,
st_ok tfxsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 extra HS HA Hcs. img_exact (regs_preserved_of_st_ok tfxsegs E ss (restrict H ms) regs0 extra HS HA Hcs).
Qed.
Lemma aregs_preserved_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.
Lemma aview_eq_of {imgk : img} : forall H (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfxsegs H m' a = aview tfxsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte. rewrite E. img_refl. Qed.
Lemma find_segment_none {imgk : img} : forall a, ~ in_img tfxsegs a -> find_segment tfxsegs a 1 = None.
Proof.
intros a Hn. unfold in_img in Hn. generalize dependent Hn. generalize tfxsegs as sgs. intros sgs Hn.
induction sgs as [|sg rest IH]; [img_refl|]. cbn.
destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
- exfalso. img_apply Hn. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
exists sg. split; [img_try (left; img_refl) | img_lia].
- img_apply IH. intros (sg' & Hin & Hr). img_apply Hn. exists sg'. split; [img_try (right; img_exact Hin) | img_try (img_exact Hr)].
Qed.
Lemma seg_rom_none {imgk : img} : forall a, 0 <= a < 2 ^ 64 -> ~ in_img tfxsegs a -> seg_rom tfxsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha Hn. unfold seg_rom, memory_read. cbn [Z.of_N].
rewrite unsigned_lit_small by img_lia. rewrite (find_segment_none a Hn). img_refl.
Qed.
Lemma mbyte_of_aview {imgk : img} : forall H H' (m m' : word -> option byte) a,
aview tfxsegs H' m' a = aview tfxsegs H m a -> mbyte tfxsegs (mrestrict H' m') a = mbyte tfxsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfxsegs (mrestrict H' m') a) as [b'|], (mbyte tfxsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|img_refl].
injection E as E. f_equal. img_apply bv_eq. img_exact E.
Qed.
Lemma val_mem_kept {imgk : img} : forall H H' (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview tfxsegs H' m' (a + k) = aview tfxsegs H m (a + k)) ->
val_mem tfxsegs (mrestrict H m) a n v -> val_mem tfxsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview H H' m m' (a + Z.of_nat k)); [img_try (apply Hv, Hkn)|]. img_apply Hk. img_lia.
Qed.
Lemma apresent_writable {imgk : img} : forall H (m : word -> option byte) a, apresent H m a -> writable_at tfxsegs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma shadow_addr_bounds : forall x, 0 <= x < kHighMemEnd -> kLowMemEnd <= shadow_addr x < kHighShadowEnd.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. img_lia. Qed.
End f.
