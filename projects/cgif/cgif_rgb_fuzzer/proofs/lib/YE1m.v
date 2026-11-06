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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YE1p YE09 YE1s YE1r YE1w YE08 YF8r YE04 YE0v YE1q.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Notation tbl2 := tbl_x213 (only parsing).
Notation tbl2_ok := tbl_x213_ok (only parsing).
Definition x2_rodata {imgk : img} : list (Z * Z * list (Z * N * Z)) :=
[ ((0x103a8 + D_20), 8, [(0, 8%N, 0xafffff00000fffff)]);
((0xa2140 + D_10f0), 72, [(0, 8%N, (0x139c60 + D_10c0)); (8, 8%N, (0xa4038 + D_10f0)); (16, 8%N, (0x13bce8 + D_10c0)); (24, 8%N, (0xa79b8 + D_10c0)); (32, 8%N, (0xaa1b8 + D_10c0));
(40, 8%N, (0xaaea8 + D_10c0)); (48, 8%N, (0xaaeb0 + D_10c0)); (56, 8%N, (0xaaea0 + D_10c0)); (64, 8%N, (0xa4000 + D_10f0))]);
((0xa2e00 + D_10f0), 16, [(0, 8%N, (0xa6a50 + D_10f0)); (8, 8%N, (0xa6ad0 + D_10f0))]);
((0xa4000 + D_10f0), 8, [(0, 8%N, (0x9b894 + D_10ec))]);
((0xa6a50 + D_10f0), 128, [(0, 8%N, 0x20ec0); (8, 8%N, 0x3); (16, 8%N, 0x20);   (32, 8%N, 0x20ee0);
(40, 8%N, 0); (48, 8%N, 0); (56, 8%N, 0xffffffffffffffff);
(64, 8%N, 0x20f00); (72, 8%N, 0x2); (80, 8%N, 0x20);   (96, 8%N, 0x20f20);
(104, 8%N, 0); (112, 8%N, 0); (120, 8%N, 0xffffffffffffffff)]);
((0xa79d0 + D_10c0), 8, [(0, 8%N, 0x101010000000001)]);
((0xa7a00 + D_10c0), 8, [(0, 8%N, 0x1000100000000)]);
((0xa9a1c + D_10c0), 1, [(0, 1%N, 1)]);
((0xaa1b8 + D_10c0), 8, [(0, 8%N, 0x7fff8000)]);
((0xaae98 + D_10c0), 1, [(0, 1%N, 1)]);
((0xaaea0 + D_10c0), 24, [(0, 8%N, 0x7fffffffffff); (8, 8%N, 0); (16, 8%N, 0)]);
((0x139c60 + D_10c0), 8, [(0, 8%N, 0x1000)]);
((0x13bd60 + D_10c0), 8, [(0, 8%N, 0xffffffffffffffff)]) ].
Definition ro_chunk (base : Z) (c : Z * N * Z) : YQ0b.chunk := YQ0b.mkChunk (base + fst (fst c)) (CVal (snd (fst c)) (SLit (snd c))).
Definition ro_region (r : Z * Z * list (Z * N * Z)) : YQ0b.region :=
YQ0b.mkRegion None (fst (fst r)) (fst (fst r) + snd (fst r)) (fst (fst r)) (fst (fst r)) (map (ro_chunk (fst (fst r))) (snd r)).
Definition X2_STK : Z := 272.
Definition x2_shw {imgk : img} : list (Z * Z) := [(0x7fffc1d8, 4); (0x7fffc1e0, 4); ((0x8000cd4a + D_21e), 16)].
Definition shw_region (w : Z * Z) : YQ0b.region :=
YQ0b.mkRegion None (fst w) (fst w + snd w) (fst w) (fst w + snd w) [].
Definition x2_regions {imgk : img} : smem :=
YQ0b.mkRegion (Some 2%nat) (- X2_STK) 0 (- X2_STK) 0 []
:: cellr (0xa6b00 + D_10c0) 8 (SLit 1) true
:: cellr (0xa7a70 + D_10c0) 8 (SLit 0) true
:: map shw_region x2_shw ++ map ro_region x2_rodata.
Definition ss_x2 {imgk : img} : sstate := mkSS X2_PC sr_atoms x2_regions None (mkFacts [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4)] [] []).
Definition x2_st {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (sym_runN tfxsegs tbl2 FUEL ss_x2)))).
Lemma x2_run {imgk : img} : sym_runN tfxsegs tbl2 FUEL ss_x2 = (x2_st, RS_stopped (SR_jalr (SOff 1 0))).
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma x2_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) ->
sym_runN tfxsegs tbl2 FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl2 tbl2_ok YF8r.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|].
split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
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
Definition rodata_chk {imgk : img} (ly : alayout) : bool :=
forallb (fun r => (0 <=? fst (fst r)) && (fst (fst r) + snd (fst r) <=? 2 ^ 47) &&
forallb (fun c => const_chk ly (fst (fst r) + fst (fst c)) (snd (fst c)) (snd c)
&& (0 <=? snd c) && (snd c <? 2 ^ (8 * Z.of_N (snd (fst c)))) && (Z.of_N (snd (fst c)) <=? 8)) (snd r))
x2_rodata.
Lemma rodata_chk_true {imgk : img} : forall ly, rodata_chk ly = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Fixpoint zrange (lo : Z) (n : nat) : list Z := match n with O => [] | S k => lo :: zrange (lo + 1) k end.
Lemma In_zrange : forall n lo a, lo <= a < lo + Z.of_nat n -> In a (zrange lo n).
Proof.
induction n as [|n IH]; intros lo a Ha; [img_lia|]. cbn [zrange].
destruct (Z.eq_dec a lo) as [->|Hne]; [img_try (left; img_refl) | img_try (right)]. img_apply IH. img_lia.
Qed.
Definition x2_shbytes {imgk : img} : list Z := flat_map (fun w => zrange (fst w) (Z.to_nat (snd w))) x2_shw.
Definition shbyte_chk {imgk : img} (ly : alayout) : bool :=
forallb (fun a => match cell_lookup (Tfx_const ly) (ANum a) with
| Some (ACell (ANum a') 1%nat (AV (ANum v))) => (a' =? a) && (0 <=? v) && (v <? 256)
| _ => false end) x2_shbytes.
Lemma shbyte_chk_true {imgk : img} : forall ly, shbyte_chk ly = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Section S. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Hypothesis MU0 : forall ly, cell_lookup (Tfx_const ly) (ANum (0xa7a70 + D_10c0)) = Some (ACell (ANum (0xa7a70 + D_10c0)) 8 (AV (ANum 0))).
Lemma rodata_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfxsegs H mem) -> Forall (region_ok tfxsegs E (mrestrict H mem)) (map ro_region x2_rodata).
Proof.
intros ly S H mem E HM. pose proof (rodata_chk_true ly) as Hc. unfold rodata_chk in Hc.
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
Lemma shbytes_present : forall ly S (H : word -> bool) mem a,
ARm B ly S (aview tfxsegs H mem) -> In a x2_shbytes -> exists b, mbyte tfxsegs (mrestrict H mem) a = Some b.
Proof.
intros ly S H mem a HM Hin. pose proof (shbyte_chk_true ly) as Hc. unfold shbyte_chk in Hc.
rewrite forallb_forall in Hc. specialize (Hc a Hin). cbn beta in Hc.
destruct (cell_lookup (Tfx_const ly) (ANum a)) as [[e w av]|] eqn:HL; [|img_try (discriminate)].
destruct e; try discriminate. destruct w as [|[|w]]; try discriminate.
destruct av as [e'| ]; try discriminate. destruct e'; try discriminate.
apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hc _]. apply Z.eqb_eq in Hc. (subst; cbv beta).
pose proof (tfx_const_lookup B TB ly S H mem a 1 _ HM HL) as Hv.
specialize (Hv 0%nat ltac:(img_lia)). rewrite Z.add_0_r in Hv. eexists. img_exact Hv.
Qed.
Lemma shw_ok : forall ly S (H : word -> bool) mem E,
ARm B ly S (aview tfxsegs H mem) -> Forall (region_ok tfxsegs E (mrestrict H mem)) (map shw_region x2_shw).
Proof.
intros ly S H mem E HM. img_apply Forall_map. img_apply Forall_forall. intros [lo n] Hin.
assert (Hr : (lo = 0x7fffc1d8 /\ n = 4) \/ (lo = 0x7fffc1e0 /\ n = 4) \/ (lo = (0x8000cd4a + D_21e) /\ n = 16)).
{ cbn in Hin. destruct Hin as [Hq|[Hq|[Hq|[]]]]; injection Hq as <- <-; tauto. }
unfold shw_region, region_ok. cbn [fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [|img_try (constructor)]. intros o Ho. rewrite Z.add_0_l.
destruct (shbytes_present ly S H mem o HM) as [b Hb].
{ unfold x2_shbytes, x2_shw. cbn [flat_map fst snd Z.to_nat Pos.to_nat Pos.iter_op Nat.add].
rewrite !in_app_iff. destruct Hr as [[-> ->]|[[-> ->]|[-> ->]]];
[img_try (left) | img_try (right; left) | img_try (right; right; left)]; img_apply In_zrange; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; img_lia. }
img_apply (mbyte_high_writable _ o b); [img_try (unfold TFX_IMG_END; img_lia) | img_try (img_exact Hb)].
Qed.
Lemma zi8_14ea00 : wseg_ok tfxsegs (Z_to_bv 64 (0xa6b00 + D_10c0)) (Z.to_nat 8) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma zi8_14f970 : wseg_ok tfxsegs (Z_to_bv 64 (0xa7a70 + D_10c0)) (Z.to_nat 8) = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma x2_windows : forall E a, in_wrange E (ss_mem ss_x2) a ->
(bv_unsigned (ew E 2) - X2_STK <= a < bv_unsigned (ew E 2)) \/ XW2 a.
Proof.
intros E a Hin. destruct (in_wrange_windows E _ a Hin) as (b & lo & hi & Ht & Hr).
cbn in Ht. unfold XW2. unfold X2_STK in *.
repeat (destruct Ht as [Hq|Ht]; [img_try (injection Hq as <- <- <-; cbn [base_val] in Hr; img_lia)|]). destruct Ht.
Qed.
Theorem x2_realizes : xret_realizes_noar tfxsegs B X2_PC XW2 XTRUE.
Proof.
intros ly S W regs mem md HPRE _. pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HES : ESTACK = 4096) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (proj1 HAR) as HM.
unfold cfg_at. img_change (w64 X2_PC) with (Z_to_bv 64 X2_PC).
set (sp0 := spZ regs) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by img_lia.
set (E := Ereg regs (@nil word)).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (img_try ((subst E; cbv beta); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); img_refl)).
assert (HS0 : st_ok tfxsegs E ss_x2 (restrict (w_H W) (mkst regs (Z_to_bv 64 X2_PC) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_x2. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs []) with E.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- unfold x2_regions. img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_app; split; [img_exact (shw_ok ly S _ mem E HM) | img_exact (rodata_ok ly S _ mem E HM)]]])].
+ img_apply (region_ok_stack tfxsegs E _ 2 sp0 (- X2_STK)); [img_try (img_exact E2) | img_try (unfold X2_STK; img_lia) | img_lia |].
intros a Ha. img_apply YE0v.apresent_writable. img_apply HpresE. unfold X2_STK in Ha. img_lia.
+ unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; img_apply (wseg_writable _ (0xa6b00 + D_10c0) 8); [img_exact zi8_14ea00 | img_lia | img_lia | img_lia | img_lia]) |].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ 1); [img_refl | img_try (img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_exact (tfx_const_lookup B TB ly S _ mem (0xa6b00 + D_10c0) 8 1 HM ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
+ unfold region_ok, cellr. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val Z.of_N].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; rewrite Z.add_0_l; img_apply (wseg_writable _ (0xa7a70 + D_10c0) 8); [img_exact zi8_14f970 | img_lia | img_lia | img_lia | img_lia]) |].
constructor; [|img_try (constructor)]. eapply (chunk_ok_val tfxsegs E _ 0 _ 8 _ 0); [img_refl | img_try (img_zside) | img_try (img_zside) |].
rewrite Z.add_0_l. img_exact (tfx_const_lookup B TB ly S _ mem (0xa7a70 + D_10c0) 8 0 HM (MU0 ly)).
- img_apply pairwise_disjoint_of_extents. unfold x2_regions, x2_shw, x2_rodata, cellr, shw_region, ro_region, extent_of_region.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite E2. unfold X2_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
img_change (2 ^ 4) with 16. repeat split; img_lia. }
eapply SRr_bind; [img_try (img_apply (x2_phase W E ss_x2 x2_st _ _ md HS0 x2_run))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1).
eapply (SRr_ret_at tfxsegs tbl2 tbl2_ok Hwx W E); [img_try (img_exact HS1) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (MEQ : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) -> ms_mem ms1 x = mem x).
{ intros x Hx. img_apply HF1. intros Hin. img_apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [img_try (left; img_exact Hw) | img_try (right; img_exact Hw)]. }
assert (MEQr : forall x : word, ~ ((sp0 - X2_STK <= bv_unsigned x < sp0) \/ XW2 (bv_unsigned x)) ->
mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
{ intros x Hx. img_apply HFr1. intros Hin. img_apply Hx. destruct (x2_windows E _ Hin) as [Hw|Hw]; rewrite ?E2 in Hw; [img_try (left; img_exact Hw) | img_try (right; img_exact Hw)]. }
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - X2_STK <= a < sp0) -> ~ XW2 a ->
aview tfxsegs (w_H W) (ms_mem ms1) a = aview tfxsegs (w_H W) mem a).
{ intros a Hr H1 H2. img_apply aview_eq_of. img_apply MEQr. rewrite unsigned_lit_small by img_lia. tauto. }
assert (PRS : forall a, sp0 - X2_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. unfold X2_STK in Ha. img_apply (apresent_of_writable (w_H W) (ms_mem ms1) a ltac:(img_lia) (high_not_img a ltac:(img_lia))).
destruct HS1 as (_ & _ & _ & _ & _ & _ & _ & (_ & Hrs & _) & _).
pose proof (Forall_inv Hrs) as Hr0. destruct Hr0 as (_ & _ & Hw & _).
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw. rewrite E2 in Hw. unfold X2_STK in Hw.
replace a with (sp0 + (a - sp0)) by img_lia. img_apply Hw. img_lia. }
rreg HS1 (1%bv : bv 5) Q1. replace (ew E 1) with (getr regs 1) in Q1 by (img_try (symmetry; img_exact (ew_Ereg_nat regs [] 1 1%bv eq_refl))).
replace (v_jalr (getr (ms_regs ms1) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra)).
split; [img_refl|]. exists (ms_regs ms1), (ms_mem ms1), (with_vm_backing (m_vm_lazy md) mat' md).
split; [img_refl|].
split; [|img_try (split; [|split])].
- img_exact (aregs_preserved_of_st_ok _ E _ _ regs [] HS1 ltac:(img_try (split; [img_try (intros i Hi; img_refl) | img_refl])) ltac:(img_try ((try img_inst; img_case; vm_compute); img_refl))).
- img_apply with_vm_backing_same.
- intros a Hr Hs Hx. img_apply AV; [img_try (img_exact Hr) | img_try (unfold X2_STK; unfold sp0 in *; img_lia) | img_try (img_exact Hx)].
- intros a Hr Hx Hp.
destruct (Z_lt_le_dec a (sp0 - X2_STK)) as [L1|L1]; [| img_try (destruct (Z_lt_le_dec a sp0) as [L2|L2]; [img_apply PRS; img_lia|])].
all: destruct Hp as [Hh [b Hb]]; split; [img_try (img_exact Hh)|]; exists b; rewrite MEQ; [img_try (img_exact Hb)|]; rewrite unsigned_lit_small by img_lia; intros [Hw|Hw]; [img_lia | img_try (img_exact (Hx Hw))].
Qed.
End S.
End d.
