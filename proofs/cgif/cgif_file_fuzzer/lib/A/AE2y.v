(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE08 YE21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition SB : Z := 0x7fff8000.
Lemma SB_eq : SB = SHADOW_OFF. Proof. reflexivity. Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma icpt_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_icpt FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_icpt tbl_icpt_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition ro_chunk (base : Z) (c : Z * N * Z) : YP09.chunk := YP09.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YP09.region :=
YP09.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition const_chk (ly : alayout) (a : Z) (n : N) (v : Z) : bool :=
match cell_lookup (Tfib_const ly) (ANum a) with
| Some (ACell (ANum a') w' (AV (ANum v'))) => (a' =? a) && Nat.eqb w' (N.to_nat n) && (v' =? v)
| _ => false
end.
Lemma const_chk_sound : forall ly a n v, const_chk ly a n v = true ->
cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) (N.to_nat n) (AV (ANum v))).
Proof.
intros ly a n v H. unfold const_chk in H.
destruct (cell_lookup (Tfib_const ly) (ANum a)) as [[e w av]|]; [|discriminate].
destruct e; try discriminate. destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. apply Z.eqb_eq in H3. subst. reflexivity.
Qed.
Definition rodata_chk (ly : alayout) (l : list (Z * Z * list (Z * N * Z))) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
forallb (fun c => const_chk ly (fst (fst r) + fst (fst c)) (snd (fst c)) (snd c)
&& (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r)) l.
Definition icpt_rodata : list (Z * Z * list (Z * N * Z)) :=
[ (0x9eb00, 8, [(0, 8%N, 0xa6cd9)]);
(0xa6cd8, 2, [(0, 1%N, 1); (1, 1%N, 1)]);
(0x9df90, 40, [(0, 8%N, 0xa37f8); (8, 8%N, 0xa5ff8); (16, 8%N, 0xa6ce8); (24, 8%N, 0xa6cf0); (32, 8%N, 0xa6ce0)]);
(0xa5ff8, 8, [(0, 8%N, 0x7fff8000)]);
(0xa6ce0, 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
(0x9fe20, 16, [(0, 8%N, 0x97294); (8, 8%N, 0x97698)]);
(0xa3840, 8, [(0, 8%N, 0x1000100000000)]) ].
Lemma icpt_rodata_chk : forall ly, rodata_chk ly icpt_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Section p.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Lemma rodata_ok : forall l ly S (H : word -> bool) mem E,
rodata_chk ly l = true ->
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region l).
Proof.
intros l ly S H mem E Hc HM. unfold rodata_chk in Hc.
rewrite forallb_forall in Hc. apply Forall_map. apply Forall_forall. intros [[base sz] cs] Hin.
specialize (Hc _ Hin). cbn [fst snd] in Hc. apply andb_prop in Hc as [Hc Hcs]. apply andb_prop in Hc as [H0 Hhi].
apply Z.leb_le in H0. apply Z.leb_le in Hhi.
unfold ro_region, region_ok. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
rewrite forallb_forall in Hcs. apply Forall_map. apply Forall_forall. intros [[off n] v] Hc'.
specialize (Hcs _ Hc'). cbn [fst snd] in Hcs.
apply andb_prop in Hcs as [Hcs H4]. apply andb_prop in Hcs as [Hcs H3]. apply andb_prop in Hcs as [H1 H2].
apply Z.leb_le in H2. apply Z.ltb_lt in H3. apply Z.leb_le in H4.
unfold ro_chunk. cbn [fst snd].
eapply (chunk_ok_val tfibsegs E _ 0 (base + off) n (SLit v) v); [reflexivity | lia | lia |].
rewrite Z.add_0_l. exact (tfib_const_lookup B TB ly S H mem (base + off) (N.to_nat n) v HM (const_chk_sound _ _ _ _ H1)).
Qed.
Lemma icpt_rodata_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfibsegs H mem) -> Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region icpt_rodata).
Proof. intros ly S H mem E HM. exact (rodata_ok icpt_rodata ly S H mem E (icpt_rodata_chk ly) HM). Qed.
End p.
Lemma ra_granule_zero : forall (rd : Z -> option Z) d n g,
range_addressable rd SHADOW_OFF d n -> d <= 8 * g + 7 < d + n -> 0 <= d -> rd (SB + g) = Some 0.
Proof.
intros rd d n g Hra Hg Hd. destruct (Hra (8 * g + 7) ltac:(lia)) as (s & Hs & Hok).
unfold shadow_of_addr in Hs. replace ((8 * g + 7) / 8) with g in Hs by (apply (Z.div_unique_pos _ 8 g 7); lia).
rewrite SB_eq. destruct Hok as [-> | [Hlt Hs8]]; [exact Hs|].
exfalso. replace ((8 * g + 7) mod 8) with 7 in Hlt by (apply (Z.mod_unique_pos _ 8 g 7); lia). lia.
Qed.
Lemma ra_last : forall (rd : Z -> option Z) d n,
range_addressable rd SHADOW_OFF d n -> 0 < n ->
exists b1, rd (SB + (d + n - 1) / 8) = Some b1 /\ saddr_ok (d + n - 1) b1.
Proof.
intros rd d n Hra Hn. destruct (Hra (d + n - 1) ltac:(lia)) as (s & Hs & Hok). exists s. rewrite SB_eq. exact (conj Hs Hok).
Qed.
Lemma aview_byte_ex : forall H mem a v,
aview tfibsegs H mem a = Some v -> exists b : byte, mbyte tfibsegs (mrestrict H mem) a = Some b /\ v = bv_unsigned b /\ 0 <= v < 256.
Proof.
intros H mem a v Hv. unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hv. injection Hv as <-. exists b. split; [reflexivity|]. split; [reflexivity|].
pose proof (bv_unsigned_in_range 8 b). unfold bv_modulus in H0. cbn in H0. lia.
Qed.
Lemma val_mem_of_rdword : forall H mem a v,
rdword (aview tfibsegs H mem) a = Some v -> val_mem tfibsegs (mrestrict H mem) a 8 v.
Proof.
intros H mem a v Hw. unfold rdword in Hw.
destruct (aview tfibsegs H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview tfibsegs H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview tfibsegs H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview tfibsegs H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview tfibsegs H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview tfibsegs H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview tfibsegs H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview tfibsegs H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection Hw as <-.
apply aview_byte_ex in E0 as (c0 & M0 & -> & R0). apply aview_byte_ex in E1 as (c1 & M1 & -> & R1).
apply aview_byte_ex in E2 as (c2 & M2 & -> & R2). apply aview_byte_ex in E3 as (c3 & M3 & -> & R3).
apply aview_byte_ex in E4 as (c4 & M4 & -> & R4). apply aview_byte_ex in E5 as (c5 & M5 & -> & R5).
apply aview_byte_ex in E6 as (c6 & M6 & -> & R6). apply aview_byte_ex in E7 as (c7 & M7 & -> & R7).
rewrite ?Z.add_0_r in M0.
set (v := bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))).
assert (Hv : 0 <= v < 2 ^ 64) by (subst v; lia).
assert (BY : forall (k : nat) (c : byte) (lo : Z) (hi : Z),
v = lo + 2 ^ (8 * Z.of_nat k) * (bv_unsigned c + 256 * hi) -> 0 <= lo < 2 ^ (8 * Z.of_nat k) -> 0 <= hi ->
Z_to_bv 8 (YO0f.le_byte v 8 k) = c).
{ intros k c lo hi Hdec Hlo Hhi. unfold YO0f.le_byte. rewrite (Z.mod_small v) by (cbn; lia).
rewrite Z.shiftr_div_pow2 by lia.
pose proof (bv_unsigned_in_range 8 c) as Hc. unfold bv_modulus in Hc. cbn [Z.of_N] in Hc. change (2 ^ 8) with 256 in Hc.
replace (v / 2 ^ (8 * Z.of_nat k)) with (bv_unsigned c + 256 * hi).
2:{ apply Z.div_unique with (r := lo); [left; lia | lia]. }
replace ((bv_unsigned c + 256 * hi) mod 256) with (bv_unsigned c).
2:{ apply Z.mod_unique with (q := hi); [left; lia | lia]. }
apply Z_to_bv_bv_unsigned. }
intros k Hk.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia];
[ change (a + Z.of_nat 0) with (a + 0); rewrite Z.add_0_r
| change (Z.of_nat 1) with 1 | change (Z.of_nat 2) with 2 | change (Z.of_nat 3) with 3 | change (Z.of_nat 4) with 4
| change (Z.of_nat 5) with 5 | change (Z.of_nat 6) with 6 | change (Z.of_nat 7) with 7 ].
- rewrite M0. f_equal. symmetry. apply (BY 0%nat c0 0 (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))))); cbn; subst v; lia.
- rewrite M1. f_equal. symmetry. apply (BY 1%nat c1 (bv_unsigned c0) (bv_unsigned c2 + 256 * (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))))); cbn; subst v; lia.
- rewrite M2. f_equal. symmetry. apply (BY 2%nat c2 (bv_unsigned c0 + 256 * bv_unsigned c1) (bv_unsigned c3 +
256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))))); cbn; subst v; lia.
- rewrite M3. f_equal. symmetry. apply (BY 3%nat c3 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * bv_unsigned c2))
(bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7)))); cbn; subst v; lia.
- rewrite M4. f_equal. symmetry. apply (BY 4%nat c4 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * bv_unsigned c3)))
(bv_unsigned c5 + 256 * (bv_unsigned c6 + 256 * bv_unsigned c7))); cbn; subst v; lia.
- rewrite M5. f_equal. symmetry. apply (BY 5%nat c5 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * bv_unsigned c4))))
(bv_unsigned c6 + 256 * bv_unsigned c7)); cbn; subst v; lia.
- rewrite M6. f_equal. symmetry. apply (BY 6%nat c6 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * bv_unsigned c5)))))
(bv_unsigned c7)); cbn; subst v; lia.
- rewrite M7. f_equal. symmetry. apply (BY 7%nat c7 (bv_unsigned c0 + 256 * (bv_unsigned c1 + 256 * (bv_unsigned c2 + 256 * (bv_unsigned c3 + 256 * (bv_unsigned c4 + 256 * (bv_unsigned c5 + 256 * bv_unsigned c6))))))
0); cbn; subst v; lia.
Qed.
Lemma icpt_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_icpt (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof AF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_icpt_ok _ _ Hlk) as Hfetch.
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
Definition MZ_PC : Z := 0x63e98.
Definition MZ_CLOB : list (bv 5) := [10%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv].
Definition ss_after_mz (ss : sstate) (rs : smem) (k : nat) (pc : Z) : sstate :=
let s1 := ss_after_stretch ss rs k MZ_CLOB pc in
mkSS (ss_pc s1) (sr_set (ss_regs s1) 10 (SLit 1)) (ss_mem s1) (ss_resv s1) (ss_facts s1).
Lemma mz_entry_eq : tfib_mem_is_zero_entry = Z_to_bv 64 MZ_PC.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma aview0_rdn1 : forall (H : word -> bool) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> aview tfibsegs H m a = Some 0 -> rdn tfibsegs (mrestrict H m) (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 0].
Proof.
intros H m a Ha Hv. apply (proj2 (rdn_mbytes tfibsegs _ 1 a [Z_to_bv 8 0])). split; [reflexivity|].
intros i Hi. replace i with 0%nat by lia. rewrite Z.add_0_r. cbn [nth_error].
rewrite (AF0x.aview_byte H m a 0 Hv). reflexivity.
Qed.
Lemma icpt_memisz : forall (W : world tfibsegs) E ss ms md (k : nat) (rs : smem) (beg N spv ra : Z),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = MZ_PC ->
ss_atoms_lt k ss = true -> regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true -> submem rs (ss_mem ss) ->
sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 beg -> sv_denot E (sr_get (ss_regs ss) 11) = Z_to_bv 64 N ->
sv_denot E (sr_get (ss_regs ss) 2) = Z_to_bv 64 spv -> sv_denot E (sr_get (ss_regs ss) 1) = Z_to_bv 64 ra ->
0 <= N <= 2 ^ 40 -> 0 <= beg -> beg + N + 8 <= 2 ^ 64 -> TFIB_IMG_END + 8 <= spv < 2 ^ 64 -> 0 <= ra < 2 ^ 64 -> ret_ok (Z_to_bv 64 ra) ->
(beg + N <= spv - 8 \/ spv <= beg) ->
(forall x, spv - 8 <= x < spv -> writable_at tfibsegs (mrestrict (w_H W) (ms_mem ms)) x) ->
(forall a, beg <= a < beg + N -> aview tfibsegs (w_H W) (ms_mem ms) a = Some 0) ->
Forall (fun r => 0 <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= spv - 8 \/ spv <= base_val E (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) rs ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 mat2, c' = mkCfg ms2 (with_vm_backing (m_vm_lazy md) mat2 md) /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) MZ_CLOB)) (ss_after_mz ss rs k ra) (restrict (w_H W) ms2) /\
(forall x : word, ~ (spv - 8 <= bv_unsigned x < spv) -> ms_mem ms2 x = ms_mem ms x) /\
(forall x : word, spv - 8 <= bv_unsigned x < spv -> ms_mem ms2 x <> None)).
Proof.
intros W E ss ms md k rs beg N spv ra HS Hrv Hpc Hat Hwf Hnc Hma Hsub R10 R11 R2 R1 HN Hbeg Hnw Hsp Hra Hret Hdisj Hslot Hz Hoff.
pose proof AF0x.Hwx_tfa as Hwx. unfold TFIB_IMG_END in Hsp.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
assert (G10 : getr (ms_regs ms) 10 = Z_to_bv 64 beg) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 10 HS); exact R10).
assert (G11 : getr (ms_regs ms) 11 = Z_to_bv 64 N) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 11 HS); exact R11).
assert (G2 : getr (ms_regs ms) 2 = Z_to_bv 64 spv) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 2 HS); exact R2).
assert (G1 : getr (ms_regs ms) 1 = Z_to_bv 64 ra) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms 1 HS); exact R1).
set (m0 := mrestrict (w_H W) (ms_mem ms)).
assert (Hstk : store_ok tfibsegs m0 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 spv) - 8)) 8 = true).
{ rewrite unsigned_lit_small by lia. apply (store_ok_of_all tfibsegs 8 m0 (Z_to_bv 64 (spv - 8)));
[rewrite unsigned_lit_small by lia; cbn [Z.of_nat Pos.to_nat]; lia | ].
intros x Hx. rewrite unsigned_lit_small in Hx by lia. unfold writable_at in Hslot.
specialize (Hslot (bv_unsigned x) ltac:(cbn [Z.of_nat Pos.to_nat Pos.iter_op Nat.add] in Hx; lia)).
rewrite Z_to_bv_bv_unsigned in Hslot. exact Hslot. }
destruct (tfib_mem_is_zero m0 (Z_to_bv 64 beg) (Z_to_bv 64 spv) N (seg_rom tfibsegs) (ms_regs ms) (Z_to_bv 64 ra)
HN ltac:(rewrite unsigned_lit_small by lia; lia) ltac:(rewrite unsigned_lit_small by lia; lia) Hstk
ltac:(rewrite !unsigned_lit_small by lia; lia)
ltac:(intros a Ha; rewrite unsigned_lit_small in Ha by lia; rewrite <- (Z_to_bv_bv_unsigned 64 a);
apply aview0_rdn1; [pose proof (u64_range a); lia | apply Hz; lia])
Hret G1 G2 G10 G11) as (regs' & Hms & Hagree & Ha0 & Hsp' & Hra').
rewrite mz_entry_eq in Hms. unfold MZ_PC in Hms.
set (m1 := wbytes m0 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 spv) - 8)) (word_to_le_bytes 8 (Z_to_bv 64 ra))) in Hms.
assert (M1out : forall x : word, ~ (spv - 8 <= bv_unsigned x < spv) -> m1 x = m0 x).
{ intros x Hx. subst m1. rewrite unsigned_lit_small by lia.
assert (L8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 ra))) = 8) by (rewrite length_N_to_le_bytes; reflexivity).
destruct (Z_lt_le_dec (bv_unsigned x) (spv - 8)) as [L|L].
- apply wbytes_below; rewrite ?L8, unsigned_lit_small by lia; lia.
- apply wbytes_above. rewrite ?L8, unsigned_lit_small by lia. lia. }
all: idtac.
pose proof (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 rs ra MZ_CLOB HS Hrv Hat Hwf Hnc Hma Hsub
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2.
rewrite Hshape in HS2. rewrite restrict_mkst_fx in HS2. cbn [ms_regs ms_mem mkst] in HS2.
specialize (HS2 ltac:(intros r Hr; apply Hagree; exact (reg_in_false r MZ_CLOB Hr))).
assert (KEPT : Forall (region_kept tfibsegs E m0 m1) rs).
{ apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) Hoff r Hr) as (O1 & O2 & O3 & O4 & O5).
apply (region_kept_outside tfibsegs E m0 m1 r (spv - 8) 8).
- intros x Hx. apply M1out. lia.
- subst m1. apply wbytes_grows.
- exact O1. - lia. - exact O2. - exact O4. - exact O5. }
specialize (HS2 KEPT).
rewrite Hshape. eapply (SRr_msteps_st tfibsegs Hwx W (havoc E k (map (getr regs') MZ_CLOB)) (ss_after_mz ss rs k ra) _ _ md).
- rewrite restrict_mkst_fx. exact Hms.
- unfold ss_after_mz. cbv zeta.
apply (st_ok_pin_reg _ (ss_after_stretch ss rs k MZ_CLOB ra) _ 10 (SLit 1)); [exact HS2 | intros H'; discriminate H' |].
cbn [sv_denot ms_regs mkst]. rewrite Ha0. reflexivity.
- intros ms' mat' HS' Hvis Hhid Hregs. apply SRr_ret. split; [reflexivity|]. exists ms', mat'. split; [reflexivity|].
rewrite Hregs. split; [exact HS'|]. split.
+ intros x Hx. destruct (w_H W x) eqn:Hh.
* rewrite (Hhid x Hh). reflexivity.
* rewrite (Hvis x Hh). cbn [ms_mem mkst]. rewrite (M1out x Hx). subst m0. unfold mrestrict. rewrite Hh. reflexivity.
+ intros x Hx. pose proof (Hslot (bv_unsigned x) Hx) as Wx. unfold writable_at, wview in Wx. rewrite Z_to_bv_bv_unsigned in Wx.
destruct (w_H W x) eqn:Hh.
* exfalso. apply Wx. subst m0. unfold mrestrict. rewrite Hh.
rewrite (tfib_find_segment_none_high (bv_unsigned x)) by (unfold TFIB_IMG_END in *; lia). reflexivity.
* rewrite (Hvis x Hh). cbn [ms_mem mkst]. subst m1 m0.
destruct (mrestrict (w_H W) (ms_mem ms) x) as [b|] eqn:Eb.
2:{ exfalso. apply Wx. rewrite (tfib_find_segment_none_high (bv_unsigned x)) by (unfold TFIB_IMG_END in *; lia). reflexivity. }
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
intros E t c. induction t as [|t IH]; [reflexivity|]. cbn [orz]. rewrite U_SAlu, IH, U_SLit. cbn [zalu_raw].
change (zcanon 0) with 0. rewrite Z.lor_0_l. apply zcanon_small. pose proof (U_range E c). unfold M64 in *. lia.
Qed.
Lemma U_dn1 : forall E pa pn d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 < n -> d + n <= 2 ^ 63 ->
U E (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) = d + n - 1.
Proof.
intros E pa pn d n Ha Hn Hd Hn0 Hdn.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E pn n Hn) by lia. rewrite U_SOff, Ha, unsigned_lit_small by lia.
unfold zcanon, M64. destruct (Z.eq_dec d 0) as [->|Hne].
- change ((0 + -1) mod 2 ^ 64) with (2 ^ 64 - 1). replace (2 ^ 64 - 1 + n) with ((n - 1) + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
- rewrite (Z.mod_small (d + -1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma qc_core_zero : forall E pa pn pb d n b1,
ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> ew E pb = Z_to_bv 64 b1 ->
0 <= d -> 0 < n -> d + n <= 2 ^ 63 -> 0 <= b1 < 256 -> saddr_ok (d + n - 1) b1 ->
U E (qc_core pa pn pb) = 0.
Proof.
intros E pa pn pb d n b1 Ha Hn Hb Hd Hn0 Hdn Hb1 Hok. unfold qc_core.
assert (Ub : U E (SOff pb 0) = b1) by (apply (U_atom E pb b1 Hb); lia).
pose proof (U_dn1 E pa pn d n Ha Hn Hd Hn0 Hdn) as Us.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Ub. change (zcanon 0) with 0.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Us, U_SLit, U_SLit, Ub.
change (zcanon 7) with 7. change (zcanon 1) with 1.
rewrite (zcanon_small (Z.land (d + n - 1) 7)) by (pose proof (Z_land_upper (d + n - 1) 7 ltac:(lia)); lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)) as Hm.
rewrite !swrap64_id by (unfold half64; lia).
destruct Hok as [-> | [Hlt _]].
- cbn. reflexivity.
- replace (0 <? b1) with true by (symmetry; apply Z.ltb_lt; lia).
replace ((d + n - 1) mod 8 <? b1) with true by (symmetry; apply Z.ltb_lt; lia). cbn. reflexivity.
Qed.
Lemma qc_flag_zero : forall E t pa pn pb d n b1,
ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> ew E pb = Z_to_bv 64 b1 ->
0 <= d -> 0 < n -> d + n <= 2 ^ 63 -> 0 <= b1 < 256 -> saddr_ok (d + n - 1) b1 ->
branch_taken BC_EQ (sv_denot E (qc_flag t pa pn pb)) (sv_denot E (SLit 0)) = true.
Proof.
intros. rewrite branch_eq_U, U_SLit. unfold qc_flag. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_orz.
rewrite (qc_core_zero E pa pn pb d n b1) by assumption. cbn. reflexivity.
Qed.
Lemma rp_b1_zero : forall E pb, ew E pb = Z_to_bv 64 0 ->
branch_taken BC_EQ (sv_denot E (SOff pb 0)) (sv_denot E (SLit 0)) = true.
Proof. intros E pb Hb. rewrite branch_eq_U, U_SLit, (U_atom E pb 0 Hb) by lia. reflexivity. Qed.
Lemma rp_b1_nonzero : forall E pb b1, ew E pb = Z_to_bv 64 b1 -> 0 < b1 < 256 ->
branch_taken BC_EQ (sv_denot E (SOff pb 0)) (sv_denot E (SLit 0)) = false.
Proof. intros E pb b1 Hb Hr. rewrite branch_eq_U, U_SLit, (U_atom E pb b1 Hb) by lia. change (zcanon 0) with 0. apply (proj2 (Z.eqb_neq b1 0)). lia. Qed.
Lemma rp_blt_last : forall E pa pn pb d n b1,
ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> ew E pb = Z_to_bv 64 b1 ->
0 <= d -> 0 < n -> d + n <= 2 ^ 63 -> (d + n - 1) mod 8 < b1 < 8 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) (SLit 7))) (sv_denot E (SOff pb 0)) = true.
Proof.
intros E pa pn pb d n b1 Ha Hn Hb Hd Hn0 Hdn Hlt.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned. fold (U E (SOff pb 0)).
fold (U E (SAlu ALU_AND (SAlu ALU_ADD (SOff pa (-1)) (SOff pn 0)) (SLit 7))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_dn1 E pa pn d n Ha Hn Hd Hn0 Hdn), U_SLit, (U_atom E pb b1 Hb) by lia.
change (zcanon 7) with 7.
rewrite (zcanon_small (Z.land (d + n - 1) 7)) by (pose proof (Z_land_upper (d + n - 1) 7 ltac:(lia)); lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)) as Hm.
rewrite !swrap64_id by (unfold half64; lia). apply Z.ltb_lt. lia.
Qed.
Lemma aview_vis_byte : forall (H : word -> bool) (m : word -> option byte) a,
aview tfibsegs H m a <> None -> exists v, aview tfibsegs H m a = Some v /\ 0 <= v < 256.
Proof.
intros H m a Hv. unfold aview in *. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|]; [|exfalso; apply Hv; reflexivity].
exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma hull_rdword : forall (H : word -> bool) (m : word -> option byte) x n h,
shadow_hull_vis (aview tfibsegs H m) x n ->
shadow_addr x / 8 * 8 <= h -> h + 8 <= shadow_addr (x + n - 1) / 8 * 8 + 8 ->
exists q, rdword (aview tfibsegs H m) h = Some q /\ 0 <= q < 2 ^ 64.
Proof.
intros H m x n h Hh Hlo Hhi.
assert (B : forall k, 0 <= k < 8 -> exists v, aview tfibsegs H m (h + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. apply aview_vis_byte. apply Hh. lia. }
destruct (B 0 ltac:(lia)) as (v0 & E0 & R0). destruct (B 1 ltac:(lia)) as (v1 & E1 & R1).
destruct (B 2 ltac:(lia)) as (v2 & E2 & R2). destruct (B 3 ltac:(lia)) as (v3 & E3 & R3).
destruct (B 4 ltac:(lia)) as (v4 & E4 & R4). destruct (B 5 ltac:(lia)) as (v5 & E5 & R5).
destruct (B 6 ltac:(lia)) as (v6 & E6 & R6). destruct (B 7 ltac:(lia)) as (v7 & E7 & R7).
rewrite Z.add_0_r in E0. unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. split; [reflexivity|]. lia.
Qed.
Lemma wbytes_inside : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned a)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn [length] in Hx; lia|].
cbn [length] in Hnw, Hx. cbn [wbytes].
destruct rest as [|b' rest'].
{ cbn [wbytes length] in *. assert (Heq : bv_unsigned x = bv_unsigned a) by lia.
rewrite Heq, Z.sub_diag. replace x with a by (apply bv_eq; lia). rewrite bv_eqb_refl. reflexivity. }
cbn [length] in Hnw, Hx.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- rewrite (wbytes_below (b' :: rest') _ (a + 1) x); [| cbn [length]; rewrite Hu1; lia | rewrite Hu1; lia].
rewrite Heq, Z.sub_diag. replace x with a by (apply bv_eq; lia). rewrite bv_eqb_refl. reflexivity.
- rewrite (IH _ (a + 1)%bv x) by (cbn [length]; rewrite Hu1; lia). rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Lemma lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|]. apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). apply zcanon_small. lia.
Qed.
Lemma U_and_m8 : forall E v, U E (SAlu ALU_AND v (SLit (-8))) = U E v - U E v mod 8.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. pose proof (U_range E v) as Hr. unfold M64 in Hr.
replace (zcanon (-8)) with (Z.land (Z.ones 64) (- 2 ^ 3)) by (vm_compute; reflexivity).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite (Z.mod_small (U E v)) by lia. rewrite land_neg_pow2 by lia.
change (2 ^ 3) with 8. apply zcanon_small. pose proof (Z.mod_pos_bound (U E v) 8 ltac:(lia)). lia.
Qed.
Lemma U_add2 : forall E pa pn d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 <= n -> d + n < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0)) = d + n.
Proof.
intros E pa pn d n Ha Hn Hd Hn0 Hdn. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E pa d Ha), (U_atom E pn n Hn) by lia. apply zcanon_small. lia.
Qed.
Lemma br_ovf_false : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 0)) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn. rewrite branch_ltu_U, U_not, (U_atom E pa d Hd), (U_atom E pn n Hn) by lia.
apply Z.ltb_ge. lia.
Qed.
Lemma br_cls_small : forall E n, ew E 12 = Z_to_bv 64 n -> 1 <= n <= 64 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff 12 (-65))) = false.
Proof.
intros E n Hn Rn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
unfold zcanon, M64. change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65).
replace ((n + -65) mod 2 ^ 64) with (n - 65 + 2 ^ 64).
2:{ replace (n + -65) with ((n - 65 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
cbn [negb]. replace (2 ^ 64 - 65 <? n - 65 + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma br_cls_zero : forall E, ew E 12 = Z_to_bv 64 0 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff 12 (-65))) = true.
Proof.
intros E Hn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
unfold zcanon, M64. change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65). change ((0 + -65) mod 2 ^ 64) with (2 ^ 64 - 65).
rewrite Z.ltb_irrefl. reflexivity.
Qed.
Lemma br_n_zero : forall E, ew E 12 = Z_to_bv 64 0 ->
branch_taken BC_NE (sv_denot E (SOff 12 0)) (sv_denot E (SLit 0)) = false.
Proof. intros E Hn. rewrite branch_ne_U, U_SLit, (U_atom E 12 0 Hn) by lia. reflexivity. Qed.
Lemma U_hull_addr : forall E (pg : nat) g0 c, ew E pg = Z_to_bv 64 g0 -> 0 <= g0 -> 0 <= c -> g0 + c + 8 < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff pg c) (SLit (-8))) = Z_to_bv 64 ((g0 + c) / 8 * 8).
Proof.
intros E pg g0 c Hg Hg0 Hc Hhi.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal. change (bv_unsigned (sv_denot E ?v)) with (U E v).
rewrite U_and_m8, (U_atom_off E pg g0 c Hg) by lia.
pose proof (Z.div_mod (g0 + c) 8 ltac:(lia)). lia.
Qed.
Lemma lor_lt_pow2 : forall a b n, 0 < n -> 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lor a b < 2 ^ n.
Proof.
intros a b n Hn Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor a b) 0) as [E|E]; [rewrite E; lia|].
apply Z.log2_lt_pow2. { pose proof (Z.lor_nonneg a b). lia. }
rewrite Z.log2_lor by lia.
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [->|]; [rewrite Z.log2_nonpos; lia|]. apply Z.log2_lt_pow2; lia.
- destruct (Z.eq_dec b 0) as [->|]; [rewrite Z.log2_nonpos; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma br_hull : forall E (p1 p2 : nat) q1 q2, ew E p1 = Z_to_bv 64 q1 -> ew E p2 = Z_to_bv 64 q2 -> 0 <= q1 < 2 ^ 64 -> 0 <= q2 < 2 ^ 64 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SOff p2 0) (SOff p1 0))) (sv_denot E (SLit 0)) = negb (Z.lor q2 q1 =? 0).
Proof.
intros E p1 p2 q1 q2 H1 H2 R1 R2. rewrite branch_ne_U, U_SLit, U_SAlu. cbn [zalu_raw].
rewrite (U_atom E p1 q1 H1), (U_atom E p2 q2 H2) by lia. change (zcanon 0) with 0.
rewrite zcanon_small; [reflexivity|]. apply lor_lt_pow2; lia.
Qed.
Lemma br_end_low : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 <= n -> d + n <= 2147450879 ->
branch_taken BC_GEU (sv_denot E (SLit 2147450879)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = true.
Proof.
intros E pa pn d n Hd Hn Rd Rn Hdn. rewrite branch_geu_U, U_SLit, (U_add2 E pa pn d n Hd Hn) by lia.
change (zcanon 2147450879) with 2147450879. cbn [negb]. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma br_end_high : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 <= n -> d + n <= 2 ^ 47 - 1 ->
branch_taken BC_LTU (sv_denot E (SLit 140737488355327)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn Hdn. rewrite branch_ltu_U, U_SLit, (U_add2 E pa pn d n Hd Hn) by lia.
change (zcanon 140737488355327) with (2 ^ 47 - 1). apply Z.ltb_ge. lia.
Qed.
Lemma br_beg_lt_end : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n -> 0 <= d -> 0 < n -> d + n < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pa 0)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn Hdn. rewrite branch_geu_U, (U_atom E pa d Hd), (U_add2 E pa pn d n Hd Hn) by lia.
cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma br_sbeg_lt_send : forall E (pu pe : nat) gu ge, ew E pu = Z_to_bv 64 gu -> ew E pe = Z_to_bv 64 ge -> 0 <= gu < ge -> ge + SB < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pu SB)) (sv_denot E (SOff pe SB)) = false.
Proof.
intros E pu pe gu ge Hu He R1 R2. unfold SB in *. rewrite branch_geu_U, (U_atom_off E pu gu 2147450880 Hu), (U_atom_off E pe ge 2147450880 He) by lia.
cbn [negb]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma val_mem1_of_aview : forall (H : word -> bool) (m : word -> option byte) a v,
aview tfibsegs H m a = Some v -> val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
destruct (aview_vis_byte H m a ltac:(rewrite Hv; discriminate)) as (v' & Hv' & Hr). rewrite Hv in Hv'. injection Hv' as <-.
rewrite (AF0x.aview_byte H m a v Hv). f_equal. apply bv_eq.
rewrite (le_byte_small v 1 0) by (cbn; lia). cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r. reflexivity.
Qed.
Lemma U_mz_len : forall E (pu pe : nat) gu ge, ew E pu = Z_to_bv 64 gu -> ew E pe = Z_to_bv 64 ge -> 0 <= gu <= ge -> ge < 2 ^ 62 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff pu 0) (SLit (-1))) (SOff pe 0)) = Z_to_bv 64 (ge - gu).
Proof.
intros E pu pe gu ge Hu He Hle Hhi.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E _)). f_equal. change (bv_unsigned (sv_denot E ?v)) with (U E v).
rewrite (U_zev E) by reflexivity. cbn [zev svpure].
unfold rho_of. rewrite Hu, He, !unsigned_lit_small by lia. rewrite !Z.add_0_r.
cbn [zmd_raw zalu_raw]. unfold zcanon, M64.
rewrite (Z.mod_small gu), (Z.mod_small ge) by lia. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (gu * (2 ^ 64 - 1)) with ((- gu) + gu * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_l. replace (- gu + ge) with (ge - gu) by lia. apply Z.mod_small. lia.
Qed.
Lemma ret_ok_lit : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. apply ret_ok_even. rewrite unsigned_lit_small by lia. exact He. Qed.
Lemma U_srl3 : forall E v, U E (SAlu ALU_SRL v (SLit 3)) = U E v / 8.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. pose proof (U_range E v). unfold M64 in *.
apply zcanon_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma icpt_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_icpt FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_icpt tbl_icpt_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma rdn_of_vis : forall (m : word -> option byte) a (n : nat),
0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
(forall i, 0 <= i < Z.of_nat n -> mbyte tfibsegs m (a + i) <> None) ->
exists bs, rdn tfibsegs m (Z_to_bv 64 a) n = Some bs /\ length bs = n /\
forall i, (i < n)%nat -> mbyte tfibsegs m (a + Z.of_nat i) = Some (nth i bs 0%bv).
Proof.
intros m a n Ha Hn Hv.
set (bs := map (fun i => match mbyte tfibsegs m (a + Z.of_nat i) with Some b => b | None => 0%bv end) (seq 0 n)).
assert (L : length bs = n) by (subst bs; rewrite length_map, length_seq; reflexivity).
assert (B : forall i, (i < n)%nat -> mbyte tfibsegs m (a + Z.of_nat i) = Some (nth i bs 0%bv)).
{ intros i Hi. subst bs.
assert (NE : nth_error (map (fun i0 : nat => match mbyte tfibsegs m (a + Z.of_nat i0) with Some b => b | None => 0%bv end) (seq 0 n)) i
= Some (match mbyte tfibsegs m (a + Z.of_nat i) with Some b => b | None => 0%bv end)).
{ rewrite nth_error_map, nth_error_seq. replace (i <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity. }
rewrite (nth_error_nth _ _ _ NE).
destruct (mbyte tfibsegs m (a + Z.of_nat i)) as [b|] eqn:Eb; [reflexivity|]. exfalso. exact (Hv (Z.of_nat i) ltac:(lia) Eb). }
exists bs. split; [|split; [exact L | exact B]].
apply (proj2 (rdn_mbytes tfibsegs m n a bs)). split; [exact L|]. intros i Hi. rewrite (B i Hi). symmetry. apply nth_error_nth'. lia.
Qed.
Lemma writable_at_same : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> writable_at tfibsegs m a -> writable_at tfibsegs m' a.
Proof. intros m m' a He Hw. unfold writable_at, wview in *. rewrite He. exact Hw. Qed.
Lemma hidden_not_writable : forall (W : world tfibsegs) (m : word -> option byte) a,
0 <= a < 2 ^ 64 -> w_H W (Z_to_bv 64 a) = true -> ~ writable_at tfibsegs (mrestrict (w_H W) m) a.
Proof.
intros W m a Ha Hh Hw. unfold writable_at, wview, mrestrict in Hw. rewrite Hh in Hw.
pose proof (w_Hoff W (Z_to_bv 64 a) Hh) as Hoff. rewrite Hoff in Hw. apply Hw. reflexivity.
Qed.
Definition Env (regs : bvmap 5 word) (extra : list Z) : env := Ereg regs (map (Z_to_bv 64) extra).
Lemma Env_reg : forall regs extra i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew (Env regs extra) i = getr regs r.
Proof. intros regs extra i r Hi. unfold Env. apply ew_Ereg_nat. exact Hi. Qed.
Lemma Env_x : forall regs extra j z, nth_error extra j = Some z -> ew (Env regs extra) (32 + j) = Z_to_bv 64 z.
Proof.
intros regs extra j z Hj. unfold Env. rewrite (ew_Ereg_extra regs _ j).
revert extra Hj. induction j as [|j IH]; intros [|e l] Hj; cbn in Hj |- *; try discriminate.
- injection Hj as ->. reflexivity.
- apply IH. exact Hj.
Qed.
Definition DROPC (ss : sstate) : sstate := set_facts ss (mkFacts (f_atoms (ss_facts ss)) [] (f_alias (ss_facts ss))).
Lemma st_ok_dropc : forall E ss ms, st_ok tfibsegs E ss ms -> st_ok tfibsegs E (DROPC ss) ms.
Proof.
intros E ss ms HS. unfold DROPC. apply st_ok_set_facts; [exact HS|].
destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & (HA & HC & HL)). split; [exact HA|]. split; [| exact HL]. cbn. exact I.
Qed.
Lemma br_eq_atoms : forall E (pa pb : nat) a b, ew E pa = Z_to_bv 64 a -> ew E pb = Z_to_bv 64 b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SOff pa 0)) (sv_denot E (SOff pb 0)) = (a =? b).
Proof. intros E pa pb a b Ha Hb Ra Rb. rewrite branch_eq_U, (U_atom E pa a Ha), (U_atom E pb b Hb) by lia. reflexivity. Qed.
Lemma br_geu_atom_add2 : forall E (pb pa pn : nat) b a n, ew E pb = Z_to_bv 64 b -> ew E pa = Z_to_bv 64 a -> ew E pn = Z_to_bv 64 n ->
0 <= b < 2 ^ 64 -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pb 0)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = negb (b <? a + n).
Proof. intros. rewrite branch_geu_U, (U_atom E pb b), (U_add2 E pa pn a n) by (try assumption; lia). reflexivity. Qed.
Lemma br_ltu_atom_add2 : forall E (pb pa pn : nat) b a n, ew E pb = Z_to_bv 64 b -> ew E pa = Z_to_bv 64 a -> ew E pn = Z_to_bv 64 n ->
0 <= b < 2 ^ 64 -> 0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot E (SOff pb 0)) (sv_denot E (SAlu ALU_ADD (SOff pa 0) (SOff pn 0))) = (b <? a + n).
Proof. intros. rewrite branch_ltu_U, (U_atom E pb b), (U_add2 E pa pn a n) by (try assumption; lia). reflexivity. Qed.
Definition hs_kept (H : word -> bool) (mem mem' : word -> option byte) : Prop :=
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Lemma in_band_rw_u64 : forall a, in_band_rw a -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia. Qed.
Lemma hs_kept_win : forall (H : word -> bool) (m0 mem mem' : word -> option byte) (lo hi plo phi : Z),
(forall z : word, ~ (lo <= bv_unsigned z < hi) -> mem' z = mem z) ->
(forall a, plo <= a < phi -> apresent H m0 a) -> plo <= lo -> hi <= phi ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros H m0 mem mem' lo hi plo phi MEQ PRES Hlo Hhi a Ha Hh. pose proof (in_band_rw_u64 a Ha) as Hr.
destruct (Z_lt_le_dec a lo) as [L1|L1]; [rewrite MEQ; [reflexivity | rewrite unsigned_lit_small by lia; lia]|].
destruct (Z_lt_le_dec a hi) as [L2|L2]; [| rewrite MEQ; [reflexivity | rewrite unsigned_lit_small by lia; lia]].
exfalso. destruct (PRES a ltac:(lia)) as [Hf _]. rewrite Hf in Hh. discriminate.
Qed.
Lemma hs_kept_eq : forall (H : word -> bool) (mem mem' : word -> option byte),
(forall z : word, mem' z = mem z) ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof. intros H mem mem' MEQ a _ _. apply MEQ. Qed.
Lemma hs_kept_unrestrict : forall (H : word -> bool) (m mr : word -> option byte),
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> munrestrict H m mr (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof. intros H m mr a _ Hh. unfold munrestrict. rewrite Hh. reflexivity. Qed.
Lemma hs_kept_trans : forall (H : word -> bool) (m1 m2 m3 : word -> option byte),
hs_kept H m1 m2 -> hs_kept H m2 m3 -> hs_kept H m1 m3.
Proof. intros H m1 m2 m3 A12 A23 a Ha Hh. rewrite (A23 a Ha Hh). exact (A12 a Ha Hh). Qed.
Lemma hs_kept_refl : forall (H : word -> bool) (m : word -> option byte), hs_kept H m m.
Proof. intros H m a _ _. reflexivity. Qed.
Lemma Z_to_bv64_of_mod : forall a, Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof.
intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma aview_mod : forall H (m : word -> option byte) a, aview tfibsegs H m a = aview tfibsegs H m (a mod 2 ^ 64).
Proof. intros H m a. unfold aview, mbyte. rewrite Z_to_bv64_of_mod. reflexivity. Qed.
Lemma apresent_mod : forall H (m : word -> option byte) a, apresent H m a = apresent H m (a mod 2 ^ 64).
Proof. intros H m a. unfold apresent. rewrite Z_to_bv64_of_mod. reflexivity. Qed.
Lemma asan_consts : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ kHighShadowEnd = 0x10007fff8000 /\ kHighMemBeg = 0x10007fff8000 /\
kHighMemEnd = 0x800000000000 /\ kLowMemEnd = 0x7fff8000.
Proof. split; [exact (proj1 alloc_ceiling_val) | repeat split; reflexivity]. Qed.
Lemma aview_some_of_apresent : forall H mem a, apresent H mem a -> aview tfibsegs H mem a <> None.
Proof.
intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.
Lemma aregs_preserved_of_st_ok : forall H E ss ms regs0 extra,
st_ok tfibsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED = true ->
aregs_preserved regs0 (ms_regs ms).
Proof.
intros H E ss ms regs0 extra HS HA Hcs. exact (regs_preserved_of_st_ok tfibsegs E ss (restrict H ms) regs0 extra HS HA Hcs).
Qed.
Lemma aregs_preserved_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.
Lemma aview_eq_of : forall H (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros H m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.
Lemma find_segment_none : forall a, ~ in_img tfibsegs a -> find_segment tfibsegs a 1 = None.
Proof.
intros a Hn. unfold in_img in Hn. generalize dependent Hn. generalize tfibsegs as sgs. intros sgs Hn.
induction sgs as [|sg rest IH]; [reflexivity|]. cbn.
destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + 1) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:E.
- exfalso. apply Hn. apply Bool.andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
exists sg. split; [left; reflexivity | lia].
- apply IH. intros (sg' & Hin & Hr). apply Hn. exists sg'. split; [right; exact Hin | exact Hr].
Qed.
Lemma seg_rom_none : forall a, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> seg_rom tfibsegs (Z_to_bv 64 a) = None.
Proof.
intros a Ha Hn. unfold seg_rom, memory_read. cbn [Z.of_N].
rewrite unsigned_lit_small by lia. rewrite (find_segment_none a Hn). reflexivity.
Qed.
Lemma mbyte_of_aview : forall H H' (m m' : word -> option byte) a,
aview tfibsegs H' m' a = aview tfibsegs H m a -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview tfibsegs H' m' (a + k) = aview tfibsegs H m (a + k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv k Hkn. rewrite (mbyte_of_aview H H' m m' (a + Z.of_nat k)); [apply Hv, Hkn|]. apply Hk. lia.
Qed.
Lemma apresent_writable : forall H (m : word -> option byte) a, apresent H m a -> writable_at tfibsegs (mrestrict H m) a.
Proof.
intros H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma shadow_addr_bounds : forall x, 0 <= x < kHighMemEnd -> kLowMemEnd <= shadow_addr x < kHighShadowEnd.
Proof. intros x Hx. unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd, kHighMemEnd in *. lia. Qed.
End f.
