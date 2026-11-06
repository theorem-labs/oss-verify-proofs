(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: IMAGE-B TWIN of lib/A/CfPoison.v. The two contracts of YGcfHp.v
   (apoison_realizes_cf, aunpoison_realizes_cf) at omx-clap-core/fuzz_preset's ASan+UBSan image B
   (fuzz_preset.asan-ubsan, the #102 pin: stripped d663f82d, twin c90d4fa54d43160b; PAU pau-preset-102),
   over the second allocator instance ARcf, from the symbolic runs of AU/CfPoisonRunB102.v. RE-PIN of
   lib/AU/CfPoisonB.v (old pin B); the twin of lib/A/CfPoison102.v; theorems renamed with suffix _B102. They are the image-B
   fields po_poison_cf / po_unpoison_cf and the named premise APOISON / AUNPOISON of the S1 program walks.
   This file is lib/A/CfPoison.v with the module map A<x> -> Y<x> (the internal file gen_fc_b.py), FCxA / CfImgA / CfPoisonRun ->
   AU/FCxA / AU/CfImgB / AU/CfPoisonRunB, CfImg_A -> CfImg_B, and the theorems renamed with a _B suffix;
   every proof line is the same. lib/A/CfPoison.v is a PORT of
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMpoisonW.v (origin/cold/port-fm-bcmp 9261fc100fcf): the
   same walk over cgif's AR with a list of user-poisoned ranges (ARU, A/FMupoison.v) instead of ARcf with the
   ghost set Hp. The donor's ARU_poison_step / ARU_unpoison_step are h-rw-man-5's ahead_poison_law /
   ahead_unpoison_law, already proved in Reusable/YGcfHp.v (ahead_poison_law_proof, ahead_unpoison_law_proof),
   so this file only has to produce their premises from the run. The `unpoison U mem` layer of the donor is
   gone: ARcf reads the memory directly.
   No image numeral is typed here: every address comes from AU/CfPoisonRunB102.v (generated from the ELF and
   checked by the build) or from AU/CfImgB.v. The head size is CfParams_preset's cf_head = 16
   (A/CfParamsPreset.v, shared by both images).
   The shadow byte after the head: both functions READ the shadow byte of the granule that follows the head,
   shadow_addr (p + cf_head) = shadow_addr p + 2, before they return (image B' 0x550bc `lb s1`, 0x55258 `lbu s4`), so
   the restricted machine must see it (a failed load is a MachineFault). head_end_ok below gives it from the block's
   shadow law when cf_head < req_size n, where the granule is still inside the block. YGcfHp's texts take
   `cf_head <= req_size n`, which also admits req_size n = cf_head - the harness's own(0) / fuzz_malloc (0) case, a
   16-byte block whose head is the whole block, where the granule lies after the block. That case is a Theorem Labs lane's
   proved lemma CfApiPreset.poison_next_vis_cf (A/CfApiPreset.v, Section PV: YGcfHp.poison_next_vis_cf_le16 at
   cf_head = 16, from ARcf's conjunct that class 1's whole shadow band is never hidden; generic in segs), cited at
   head_end_ok (:219) as CfApiPreset.poison_next_vis_cf tfibsegs B .. with tfibsegs of Reusable/YB1v.v; it is generic
   in the implicit image class ci (Section PV's Context, through ARcf), inferred there with rc. No stand-in.
   Where p is (head_zone) comes from the block law in every case.
   The memnorm keep (the texts' last conjunct since h-mani-a8's leaves2, s1b 459129c18903) is paid by the frame:
   memnorm_frame2 below, from the walk's raw-memory frame MEQ (the walk writes only the 64-byte frame below sp and
   the two head shadow bytes, both outside the image and below TASK_SIZE). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
(* Before AU's FCxA below: CfApiPreset loads lib/A/FCxA.v, and the later AU import keeps the short name FCxA on AU's. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfApiPreset.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YGcfHp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface FCifaceCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN32 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import FCxA CfImgB CfPoisonRunB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import CfParamsPreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma po_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_po FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_po tbl_po_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma st_ok_add_fact0 : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.
Ltac unf_le_byte := try unfold YG0f.le_byte; try unfold YO0f.le_byte.
Lemma val_mem1_of_aview : forall H mem a v, aview tfibsegs H mem a = Some v -> val_mem tfibsegs (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hv. destruct (YE2y.aview_byte_ex H mem a v Hv) as (b & Hb & -> & Hr). intros k Hk. replace k with 0%nat by lia.
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal. unf_le_byte.
change (8 * Z.of_nat 1%nat) with 8. change (8 * Z.of_nat 0%nat) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma aview_of_val_mem1 : forall H mem a v, val_mem tfibsegs (mrestrict H mem) a 1 v -> 0 <= v < 256 -> aview tfibsegs H mem a = Some v.
Proof.
intros H mem a v Hv Hr. unfold aview. pose proof (Hv 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. rewrite X.
cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unf_le_byte. change (8 * Z.of_nat 1%nat) with 8. change (8 * Z.of_nat 0%nat) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma XS_denot : forall E d hv, bv_unsigned (ew E 10) = hv -> 0 <= hv -> 0 <= d -> hv + d < 2 ^ 64 ->
sv_denot E (XS d) = Z_to_bv 64 (SHADOW_OFF + (hv + d) / 8).
Proof.
intros E d hv HE H0 Hd Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (XS d))). f_equal.
change (bv_unsigned (sv_denot E (XS d))) with (U E (XS d)). rewrite (U_zev E (XS d)) by (vm_compute; reflexivity).
unfold XS. cbn [zev zalu_raw]. unfold rho_of. rewrite HE. change (Z.land (zcanon 3) 63) with 3. change (zcanon 2147450880) with 2147450880.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (hv + d) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (hv + d) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (hv + d)) by lia. rewrite (zcanon_small ((hv + d) / 8)) by lia. unfold SHADOW_OFF. apply zcanon_small. lia.
Qed.
Lemma XS0_denot : forall E d hv, bv_unsigned (ew E 10) = hv -> 0 <= hv -> 0 <= d -> hv + d < 2 ^ 64 ->
sv_denot E (XS0 d) = Z_to_bv 64 (SHADOW_OFF + (hv + d) / 8).
Proof.
intros E d hv HE H0 Hd Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (XS0 d))). f_equal.
change (bv_unsigned (sv_denot E (XS0 d))) with (U E (XS0 d)). rewrite (U_zev E (XS0 d)) by (vm_compute; reflexivity).
unfold XS0, XS. cbn [zev zalu_raw]. unfold rho_of. rewrite HE. change (Z.land (zcanon 3) 63) with 3. change (zcanon 2147450880) with 2147450880.
change (zcanon 0) with 0. rewrite Z.add_0_r.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (hv + d) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (hv + d) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small (hv + d)) by lia. rewrite (zcanon_small ((hv + d) / 8)) by lia. unfold SHADOW_OFF.
rewrite (zcanon_small (2147450880 + (hv + d) / 8)) by lia. apply zcanon_small. lia.
Qed.
End d.
Lemma env_agree_Ereg_app' : forall regs l1 l2 k, (k <= 32 + length l1)%nat -> env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma vis_apresent' : forall H mem a v, TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H mem a = Some v -> apresent H mem a.
Proof. intros H mem a v Ha Hv. destruct (YE2y.aview_byte_ex H mem a v Hv) as (b & Hb & _). exact (YF0x.mbyte_high_apresent H mem a b Ha Hb). Qed.
Lemma winsA_cases : forall E rs a, windows rs = WinsA -> in_wrange E rs a -> bv_unsigned (ew E 2) - PO_WIN <= a < bv_unsigned (ew E 2).
Proof.
intros E rs a HW Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi' & Ht & Hw). rewrite HW in Ht. unfold WinsA in Ht.
repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; unfold PO_WIN; first [lia | exfalso; lia] |]). destruct Ht.
Qed.
Lemma wins_cases : forall E rs a, windows rs = Wins -> in_wrange E rs a ->
bv_unsigned (ew E 2) - PO_WIN <= a < bv_unsigned (ew E 2) \/ bv_unsigned (ew E 32) <= a < bv_unsigned (ew E 32) + 2.
Proof.
intros E rs a HW Hin. destruct (in_wrange_windows E rs a Hin) as (b & lo & hi' & Ht & Hw). rewrite HW in Ht. unfold Wins in Ht.
repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; unfold PO_WIN; first [left; lia | right; lia | exfalso; lia] |]). destruct Ht.
Qed.

(* The memnorm keep (YGcfHp's last conjunct, h-mani-a8's leaves2): memnorm (YAkMemnorm.v:41) is pointwise, so a memory
   that differs from a memnorm memory only on windows outside the image and below TASK_SIZE is memnorm. The walk writes
   only the 64-byte frame below sp and the two head shadow bytes. *)
Lemma win_dec : forall lo hi z : Z, {lo <= z < hi} + {~ (lo <= z < hi)}.
Proof.
intros lo hi z. destruct (Z_le_dec lo z) as [A1|A1]; destruct (Z_lt_dec z hi) as [B1|B1].
- left. split; assumption.
- right. intros [_ X]. contradiction.
- right. intros [X _]. contradiction.
- right. intros [X _]. contradiction.
Qed.
Lemma memnorm_frame2 : forall (segs : list Segment) (m m' : word -> option byte) (lo1 hi1 lo2 hi2 : Z),
YAkMemnorm.memnorm segs m ->
(forall x : word, ~ (lo1 <= bv_unsigned x < hi1) -> ~ (lo2 <= bv_unsigned x < hi2) -> m' x = m x) ->
hi1 <= TASK_SIZE -> hi2 <= TASK_SIZE ->
(forall x : word, lo1 <= bv_unsigned x < hi1 -> find_segment segs (bv_unsigned x) 1 = None) ->
(forall x : word, lo2 <= bv_unsigned x < hi2 -> find_segment segs (bv_unsigned x) 1 = None) ->
YAkMemnorm.memnorm segs m'.
Proof.
intros segs m m' lo1 hi1 lo2 hi2 (Hi & Ht) Hout H1 H2 S1 S2. split; intros x b E.
- destruct (win_dec lo1 hi1 (bv_unsigned x)) as [I1|N1]; [unfold YAkMemnorm.ro_addr; rewrite (S1 x I1); reflexivity|].
  destruct (win_dec lo2 hi2 (bv_unsigned x)) as [I2|N2]; [unfold YAkMemnorm.ro_addr; rewrite (S2 x I2); reflexivity|].
  rewrite (Hout x N1 N2) in E. exact (Hi x b E).
- destruct (win_dec lo1 hi1 (bv_unsigned x)) as [I1|N1]; [right; destruct I1 as [_ X]; eapply Z.lt_le_trans; [exact X | exact H1]|].
  destruct (win_dec lo2 hi2 (bv_unsigned x)) as [I2|N2]; [right; destruct I2 as [_ X]; eapply Z.lt_le_trans; [exact X | exact H2]|].
  rewrite (Hout x N1 N2) in E. exact (Ht x b E).
Qed.
Ltac uaddr := try unfold kLowShadowBeg in *; try unfold kLowShadowEnd in *; try unfold kHighShadowBeg in *;
try unfold kHighShadowEnd in *; try unfold kHighMemBeg in *; try unfold kHighMemEnd in *; try unfold SHADOW_OFF in *;
try unfold TFIB_IMG_END in *; try unfold ASAN_CEIL in *; try unfold alloc_ceiling in *; try unfold ESTACK in *; try unfold PO_WIN in *; try unfold TASK_SIZE in *.
Ltac alia := uaddr; repeat split; lia.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance CfImg_B.
Variable B : asyms.
Hypothesis LAWS : AR_laws_cf tfibsegs B.
Hypothesis TB : TfibSyms B.

Let HF : AR_head_frame_law_cf tfibsegs B := alc_head_frame _ _ LAWS.
Let FI : fs_iface tfibsegs B (ARcf tfibsegs B) := fs_iface_ARcf tfibsegs B LAWS.

(* The image cells the walk reads, as regions of the symbolic memory. *)
Lemma po_rodata_ok_cf : forall ly S Hp W mem md E, ARcf tfibsegs B ly S Hp W mem md ->
Forall (region_ok tfibsegs E (mrestrict (w_H W) mem)) (map ro_region po_rodata).
Proof.
intros ly S Hp W mem md E HAR.
exact (FCxA.rodata_ok_x B (ARcf tfibsegs B) FI TB po_rodata ly S Hp W mem md E (po_rodata_chk ly) HAR).
Qed.

(* Where p is: the zone the run's facts assume (AU/CfPoisonRunB.v hLO / hHI), from the block law alone. *)
Lemma head_zone : forall ly S Hp (W : world tfibsegs) mem md p n,
ARcf tfibsegs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> cf_head <= req_size n ->
exists hi : bool, hLO hi <= p <= hHI hi.
Proof.
intros ly S Hp W mem md p n HAR Hb Hn.
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n HAR Hb) as (P16 & P4096 & PC & PAPP & _).
assert (A16 : cf_head = 16) by reflexivity. rewrite A16 in Hn.
pose proof YE2y.asan_consts as (ACr & _ & HMB & HME & _).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
unfold in_app in PAPP. destruct PAPP as [_ [PA2 | (PA2 & PA3)]].
- exists false. unfold hLO, hHI. split; [exact P4096 | lia].
- exists true. unfold hLO, hHI, ASAN_CEIL in *. rewrite HME. lia.
Qed.

(* The shadow byte of the granule after the head: inside the block when cf_head < req_size n (the block's shadow
   law), CfApiPreset.poison_next_vis_cf at equality. *)
Lemma head_end_ok : forall ly S Hp (W : world tfibsegs) mem md p n,
ARcf tfibsegs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> cf_head <= req_size n ->
(exists hi : bool, hLO hi <= p <= hHI hi) /\ aview tfibsegs (w_H W) mem (shadow_addr (p + cf_head)) <> None.
Proof.
intros ly S Hp W mem md p n HAR Hb Hn.
split; [exact (head_zone ly S Hp W mem md p n HAR Hb Hn)|].
destruct (Z.eq_dec (req_size n) cf_head) as [Heq | Hne]; [exact (CfApiPreset.poison_next_vis_cf tfibsegs B ly S Hp W mem md p n HAR Hb Heq)|].
assert (Hlt : cf_head < req_size n) by lia.
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n HAR Hb) as (P16 & _).
assert (A16 : cf_head = 16) by reflexivity.
destruct (alc_shadow _ _ LAWS ly S Hp W mem md p n HAR Hb) as [BS _].
set (hd := hd_skip Hp p) in *.
assert (Hhd : hd = 0 \/ hd = cf_head) by (unfold hd, hd_skip; destruct (existsb (Z.eqb p) Hp); [right | left]; reflexivity).
destruct BS as (B8 & BL & BV).
rewrite A16 in Hhd, Hlt.
assert (IDX : 0 <= (16 - hd) / 8 < (req_size n - hd + 7) / 8).
{ destruct Hhd as [-> | ->].
  - change ((16 - 0) / 8) with 2. split; [lia|].
    assert (24 <= req_size n - 0 + 7) by lia. pose proof (Z.div_le_mono 24 (req_size n - 0 + 7) 8 ltac:(lia) ltac:(lia)). change (24 / 8) with 3 in *. lia.
  - change ((16 - 16) / 8) with 0. split; [lia|]. assert (8 <= req_size n - 16 + 7) by lia.
    pose proof (Z.div_le_mono 8 (req_size n - 16 + 7) 8 ltac:(lia) ltac:(lia)). change (8 / 8) with 1 in *. lia. }
rewrite <- A16 in IDX at 1.
pose proof (BV _ IDX) as BVv.
assert (ADDR : shadow_of_addr SHADOW_OFF (p + hd) + (cf_head - hd) / 8 = shadow_addr (p + cf_head)).
{ unfold shadow_of_addr, shadow_addr. apply Z.mod_divide in P16 as [k Hk]; [|lia]. rewrite A16.
  destruct Hhd as [-> | ->]; rewrite Hk.
  - change ((16 - 0) / 8) with 2. replace (k * 16 + 0) with (k * 2 * 8) by lia. replace (k * 16 + 16) with ((k * 2 + 2) * 8) by lia.
    rewrite !Z.div_mul by lia. lia.
  - change ((16 - 16) / 8) with 0. replace (k * 16 + 16) with ((k * 2 + 2) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
rewrite ADDR in BVv. rewrite BVv. discriminate.
Qed.

(* The two head granules read the same byte: 0 while p is not hidden, shUserPoison once it is. *)
Lemma head_bytes : forall ly S Hp (W : world tfibsegs) mem md p n,
ARcf tfibsegs B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> cf_head <= req_size n -> cf_head mod 8 = 0 ->
exists hv, 0 <= hv < 256 /\ forall j, 0 <= j < 2 -> aview tfibsegs (w_H W) mem (shadow_addr p + j) = Some hv.
Proof.
intros ly S Hp W mem md p n HAR Hb Hn A8.
assert (A16 : cf_head = 16) by reflexivity.
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n HAR Hb) as (P16 & _).
pose proof (p8_of_p16 p P16) as P8.
assert (SHJ : forall j, 0 <= j < 2 -> shadow_addr (p + 8 * j) = shadow_addr p + j).
{ intros j Hj. unfold shadow_addr. apply Z.mod_divide in P8 as [k Hk]; [|lia]. rewrite Hk.
  replace (k * 8 + 8 * j) with ((k + j) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
assert (G8J : forall j, (p + 8 * j) mod 8 = 0).
{ intros j. apply Z.mod_divide in P8 as [k Hk]; [|lia]. rewrite Hk. replace (k * 8 + 8 * j) with ((k + j) * 8) by lia. apply Z.mod_mul. lia. }
destruct (existsb (Z.eqb p) Hp) eqn:EX.
- (* p is already hidden: both bytes are shUserPoison *)
  assert (Hin : In p Hp).
  { apply existsb_exists in EX as (x & Hx & Ex). apply Z.eqb_eq in Ex. subst x. exact Hx. }
  exists shUserPoison. split; [unfold shUserPoison; lia|]. intros j Hj.
  pose proof (head_ashadow0 tfibsegs B LAWS HF ly S Hp W mem md p HAR Hin A8 (p + 8 * j) (G8J j) ltac:(rewrite A16 in *; lia)) as HA0.
  pose proof (amc_shadow _ _ _ _ _ (proj1 HAR) (p + 8 * j) 0 (G8J j) HA0) as SHv.
  replace (in_head Hp (p + 8 * j)) with true in SHv
    by (symmetry; apply in_head_spec; exists p; split; [exact Hin | rewrite A16 in *; lia]).
  rewrite (SHJ j Hj) in SHv. exact SHv.
- (* p is not hidden: the block's shadow law gives 0 *)
  assert (Hni : ~ In p Hp).
  { intros Hin. assert (EXt : existsb (Z.eqb p) Hp = true) by (apply existsb_exists; exists p; split; [exact Hin | apply Z.eqb_refl]).
    rewrite EXt in EX. discriminate. }
  exists 0. split; [lia|]. intros j Hj.
  destruct (alc_shadow _ _ LAWS ly S Hp W mem md p n HAR Hb) as [BS _].
  rewrite (hd_skip_notin Hp p Hni), Z.add_0_r, Z.sub_0_r in BS.
  destruct BS as (_ & _ & BV).
  assert (IDX : 0 <= j < (req_size n + 7) / 8).
  { split; [lia|]. assert (23 <= req_size n + 7) by (rewrite A16 in Hn; lia).
    pose proof (Z.div_le_mono 23 (req_size n + 7) 8 ltac:(lia) ltac:(lia)). change (23 / 8) with 2 in *. lia. }
  pose proof (BV _ IDX) as BVv.
  replace (j <? req_size n / 8) with true in BVv.
  2:{ symmetry. apply Z.ltb_lt. assert (16 <= req_size n) by (rewrite A16 in Hn; lia).
      pose proof (Z.div_le_mono 16 (req_size n) 8 ltac:(lia) ltac:(lia)). change (16 / 8) with 2 in *. lia. }
  unfold shadow_of_addr in BVv. change (SHADOW_OFF + p / 8) with (shadow_addr p) in BVv. exact BVv.
Qed.

Theorem preset_apoison_cf_B102 : @apoison_realizes_cf fx rc CfImg_B CfParams_preset tfibsegs B.
Proof.
unfold apoison_realizes_cf.
intros ly S Hp W regs mem md p n HPRE G10 G11 A8 Hb Hn.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof YF0x.Hwx_tfa as Hwx.
pose proof (proj1 HAR) as M.
pose proof (amc_layout _ _ _ _ _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (A16 : cf_head = 16) by reflexivity.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Lbeg Lhi Hslo Htop; unfold kHighMemBeg, kHighMemEnd in *; alia).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n HAR Hb) as (P16 & P4096 & PC & PAPP & _).
pose proof (p8_of_p16 p P16) as H8.
destruct (head_end_ok ly S Hp W mem md p n HAR Hb Hn) as [ZONE HV2n].
destruct (head_bytes ly S Hp W mem md p n HAR Hb Hn A8) as (HVv & HVr & HV0).
destruct ZONE as [hi HZ].
assert (Hh : 4096 <= p < 2 ^ 47) by (destruct hi; unfold hLO, hHI, kHighMemBeg, kHighMemEnd, kLowShadowBeg in HZ; alia).
set (SH := shadow_addr p).
assert (HSH : SH = SHADOW_OFF + p / 8) by reflexivity.
assert (SHr : shLO hi <= SH <= shHI hi).
{ rewrite HSH. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|alia]. rewrite Hq, Z.div_mul by alia.
  destruct hi; unfold shLO, shHI, hLO, hHI, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg, kHighMemEnd in *; alia. }
assert (SHb : kLowShadowBeg <= SH /\ SH + 3 <= kHighMemBeg)
  by (clear - SHr; destruct hi; unfold shLO, shHI, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg in *; alia).
destruct SHb as [SHb1 SHb2].
assert (SHnum : 2147446784 <= SH /\ SH + 3 <= 17594333495296) by (clear - SHb1 SHb2; unfold kLowShadowBeg, kHighMemBeg in *; alia).
destruct SHnum as [SHn1 SHn2].
assert (SH2 : shadow_addr (p + cf_head) = SH + 2).
{ rewrite HSH, A16. unfold shadow_addr. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|alia]. rewrite Hq.
  replace (q * 8 + 16) with ((q + 2) * 8) by alia. rewrite !Z.div_mul by alia. alia. }
rewrite SH2 in HV2n.
assert (HV2 : exists VB, aview tfibsegs H mem (SH + 2) = Some VB).
{ destruct (aview tfibsegs H mem (SH + 2)) as [v|] eqn:Ev; [exists v; reflexivity | exfalso; exact (HV2n Ev)]. }
destruct HV2 as [VB HVB].
pose proof (YE2y.aview_byte_ex H mem (SH + 2) VB HVB) as (bVB & _ & _ & HVBr).
(* ---- phase A: entry to the load of the head's shadow byte ---- *)
set (E0 := YE2y.Env regs []).
assert (E0reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (E02 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0reg 2%nat 2%bv eq_refl); reflexivity).
assert (E010 : bv_unsigned (ew E0 10) = p) by (rewrite (E0reg 10%nat 10%bv eq_refl), G10; unfold w64; apply unsigned_lit_small; alia).
assert (G11' : getr regs 11 = w64 16) by (rewrite G11, A16; reflexivity).
assert (HS0 : st_ok tfibsegs E0 (ssA PO_ENTRY hi) (restrict H (mkst regs (Z_to_bv 64 PO_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssA.
  apply (YF0x.st_ok_pin_reg E0 (ssA0 PO_ENTRY hi) _ 11%bv (SLit 16)); [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11'; reflexivity].
  unfold ssA0. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold memA. apply Forall_cons; [|exact (po_rodata_ok_cf ly S Hp W mem md E0 HAR)].
    unfold stkA, PO_WIN. apply (region_ok_stack tfibsegs E0 _ 2 sp0 (- 64)); [exact E02 | alia | alia |].
    intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply HpresE. alia.
  - apply pairwise_disjoint_of_extents. unfold memA, stkA, po_rodata, icpt_rodata, ro_region, extent_of_region, PO_WIN.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E02.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; alia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E02, E010.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try alia; first [exact Hal16 | exact H8 | idtac]. }
eapply SRr_bind; [apply (po_phase W E0 _ _ _ _ _ HS0 (pr_A hi))|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
change (st_ok tfibsegs E0 (peA hi) (restrict H msA)) in HSA.
assert (MEQA : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ms_mem msA z = mem z).
{ intros z Hz. apply HFA. intros Hin. pose proof (winsA_cases E0 _ _ (pA_win hi) Hin) as X. rewrite E02 in X. unfold PO_WIN in X. alia. }
clear HFA HFrA.
destruct (pA_facts hi) as (PA1 & PA2 & PA3 & PA4 & PA5 & PA6).
pose proof (st_ok_restrict_mkst tfibsegs H E0 _ _ HSA PA2) as HshA. rewrite PA1 in HshA.
assert (RDA : forall (r : bv 5) v, reg_is (peA hi) (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E0 (peA hi) msA r HSA). }
assert (G9A : getr (ms_regs msA) 9 = Z_to_bv 64 SH).
{ rewrite (RDA 9%bv _ PA4). rewrite (XS0_denot E0 0 p E010) by alia. rewrite Z.add_0_r. reflexivity. }
assert (G10A : getr (ms_regs msA) 10 = Z_to_bv 64 SH).
{ rewrite (RDA 10%bv _ PA5). rewrite (XS_denot E0 0 p E010) by alia. rewrite Z.add_0_r. reflexivity. }
(* ---- phase B: the three shadow bytes as a region at the new atoms ---- *)
set (EB := YE2y.Env regs [SH; VB; HVv]).
assert (AGR : env_agree 32 E0 EB) by (unfold E0, EB, YE2y.Env; cbn [map]; apply (env_agree_Ereg_app' regs [] [Z_to_bv 64 SH; Z_to_bv 64 VB; Z_to_bv 64 HVv] 32); cbn; alia).
assert (EBreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EB i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (EB2 : bv_unsigned (ew EB 2) = sp0) by (rewrite (EBreg 2%nat 2%bv eq_refl); reflexivity).
assert (EB10 : bv_unsigned (ew EB 10) = p) by (rewrite (EBreg 10%nat 10%bv eq_refl), G10; unfold w64; apply unsigned_lit_small; alia).
assert (UB32 : bv_unsigned (ew EB 32) = SH) by (pose proof (YE2y.Env_x regs [SH; VB; HVv] 0 SH eq_refl) as X; cbn [Nat.add] in X; change (YE2y.Env regs [SH; VB; HVv]) with EB in X; rewrite X; apply unsigned_lit_small; clear - SHb1 SHb2; alia).
assert (UB33 : bv_unsigned (ew EB 33) = VB) by (pose proof (YE2y.Env_x regs [SH; VB; HVv] 1 VB eq_refl) as X; cbn [Nat.add] in X; change (YE2y.Env regs [SH; VB; HVv]) with EB in X; rewrite X; apply unsigned_lit_small; alia).
assert (UB34 : bv_unsigned (ew EB 34) = HVv) by (pose proof (YE2y.Env_x regs [SH; VB; HVv] 2 HVv eq_refl) as X; cbn [Nat.add] in X; change (YE2y.Env regs [SH; VB; HVv]) with EB in X; rewrite X; apply unsigned_lit_small; alia).
assert (VM1 : forall a v, ~ (sp0 - 64 <= a < sp0) -> 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a = Some v ->
  val_mem tfibsegs (mrestrict H (ms_mem msA)) a 1 v).
{ intros a v Ha Hr Hv. apply (YF0x.val_mem_ext (mrestrict H mem)); [| apply val_mem1_of_aview; exact Hv].
  intros k Hk. replace k with 0%nat by alia. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite MEQA; [reflexivity|]. rewrite unsigned_lit_small by alia. alia. }
assert (SHnS : forall j, 0 <= j < 3 -> ~ (sp0 - 64 <= SH + j < sp0)) by (intros j Hj; clear - SHb1 SHb2 Hslo Lbeg Hj; alia).
assert (SHr64 : forall j, 0 <= j < 3 -> TFIB_IMG_END <= SH + j < 2 ^ 64) by (intros j Hj; clear - SHn1 SHn2 Hj; unfold TFIB_IMG_END in *; alia).
rewrite HshA in HSA. rewrite restrict_mkst_fx in HSA.
assert (HSB0 : st_ok tfibsegs EB (pB hi) (restrict H (mkst (ms_regs msA) (Z_to_bv 64 P_LDA) (ms_mem msA) (seg_rom tfibsegs)))).
{ rewrite <- (pB_eq hi). unfold ppB. rewrite PA1. rewrite restrict_mkst_fx.
  apply st_ok_add_fact0; [| reflexivity | unfold aHV; rewrite UB34; alia].
  apply st_ok_add_fact0; [| reflexivity | unfold aV; rewrite UB33; alia].
  apply st_ok_add_fact0; [| reflexivity | unfold aSH; rewrite UB32; exact SHr].
  apply (st_ok_set_regs_mem tfibsegs 32 E0 EB (peA hi) (ms_regs msA) (ms_regs msA) (Z_to_bv 64 P_LDA) P_LDA
    (mrestrict H (ms_mem msA)) (mrestrict H (ms_mem msA)) (memB (peA hi)) updB HSA AGR PA3).
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - unfold updB. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
    + rewrite G9A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
    + rewrite G10A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
  - pose proof (st_ok_agree tfibsegs 32 E0 EB (peA hi) _ HSA AGR PA3) as HSA'.
    pose proof (st_ok_mem_ok tfibsegs EB (peA hi) _ HSA') as (WFA & ROKA & PDA).
    split; [rewrite memB_eq; vm_compute; reflexivity|]. split.
    + unfold memB. rewrite PA6 in ROKA. apply Forall_cons; [exact (Forall_inv ROKA)|]. apply Forall_cons; [|exact (Forall_inv_tail ROKA)].
      unfold rSH, aSH, region_ok. cbv zeta. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UB32.
      refine (conj _ (conj _ (conj _ _))); [clear - SHn1 SHn2; alia | clear - SHn1 SHn2; alia | |].
      { intros o Ho. apply (YF0x.apresent_writable H); [apply SHr64; alia|].
        apply (YF0x.apresent_same H mem); [apply MEQA; rewrite unsigned_lit_small by (pose proof (SHr64 o ltac:(alia)); alia); apply SHnS; alia|].
        exact (vis_apresent' H mem (SH + o) HVv (SHr64 o ltac:(alia)) (HV0 o ltac:(alia))). }
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val tfibsegs EB _ SH 0 1%N (SOff aHV 0) HVv); [cbn [sv_denot]; unfold aHV; rewrite UB34, Z.add_0_r; reflexivity | cbn; alia | cbn; alia |].
        apply VM1; [apply SHnS; alia | pose proof (SHr64 0 ltac:(alia)); alia | exact (HV0 0 ltac:(alia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 1 1%N (SOff aHV 0) HVv); [cbn [sv_denot]; unfold aHV; rewrite UB34, Z.add_0_r; reflexivity | cbn; alia | cbn; alia |].
        apply VM1; [apply SHnS; alia | pose proof (SHr64 1 ltac:(alia)); alia | exact (HV0 1 ltac:(alia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 2 1%N (SOff aV 0) VB); [cbn [sv_denot]; unfold aV; rewrite UB33, Z.add_0_r; reflexivity | cbn; alia | cbn; alia |].
        apply VM1; [apply SHnS; alia | pose proof (SHr64 2 ltac:(alia)); alia | exact HVB].
    + apply pairwise_disjoint_of_extents. rewrite memB_eq. let l' := eval vm_compute in memBc in change memBc with l'.
      unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EB2, ?UB32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - SHb1 SHb2 Hsp Hslo Lbeg. unfold kLowShadowBeg, kHighMemBeg in *. repeat split; alia. }
rewrite HshA.
eapply SRr_bind; [apply (po_phase W EB (pB hi) _ _ _ _ HSB0 (pr_B hi))|].
cbv beta. intros Wb cb _ (-> & msB & matB & -> & HSB & HFB & HFrB). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (peB hi) (restrict H msB)) in HSB.
assert (MEQB : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msB z = ms_mem msA z).
{ intros z Hz1 Hz2. apply HFB. intros Hin. pose proof (wins_cases EB _ _ (pB_win hi) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. alia. }
clear HFB HFrB.
destruct (pB_facts hi) as (PB1 & PB2 & PB3 & PB4).
pose proof (st_ok_restrict_mkst tfibsegs H EB _ _ HSB PB2) as HshB. rewrite PB1 in HshB.
assert (RDB : forall (r : bv 5) v, reg_is (peB hi) (bv_unsigned r) v = true -> getr (ms_regs msB) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (peB hi) msB r HSB). }
assert (G18B : getr (ms_regs msB) 18 = Z_to_bv 64 (SH + 2)).
{ rewrite (RDB 18%bv _ PB4). rewrite (XS0_denot EB 16 p EB10) by alia. rewrite <- A16, <- SH2. reflexivity. }
rewrite HshB in HSB. rewrite restrict_mkst_fx in HSB.
assert (HSC0 : st_ok tfibsegs EB (pC hi) (restrict H (mkst (ms_regs msB) (Z_to_bv 64 P_LDB) (ms_mem msB) (seg_rom tfibsegs)))).
{ rewrite <- (pC_eq hi). unfold ppC. rewrite PB1. rewrite restrict_mkst_fx.
  apply (st_ok_set_regs_mem tfibsegs 35 EB EB (peB hi) (ms_regs msB) (ms_regs msB) (Z_to_bv 64 P_LDB) P_LDB
    (mrestrict H (ms_mem msB)) (mrestrict H (ms_mem msB)) (ss_mem (peB hi)) [((18%bv : bv 5), SOff aSH 2)] HSB).
  - split; [intros; reflexivity | reflexivity].
  - exact PB3.
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G18B. cbn [sv_denot]. unfold aSH. rewrite UB32. reflexivity.
  - exact (st_ok_mem_ok tfibsegs EB (peB hi) _ HSB). }
rewrite HshB.
eapply SRr_bind; [apply (po_phase W EB (pC hi) _ _ _ _ HSC0 (pr_C hi))|].
cbv beta. intros Wc cc _ (-> & msC & matC & -> & HSC & HFC & HFrC). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (peC hi) (restrict H msC)) in HSC.
assert (MEQC : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msC z = ms_mem msB z).
{ intros z Hz1 Hz2. apply HFC. intros Hin. pose proof (wins_cases EB _ _ (pC_win hi) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. alia. }
clear HFC HFrC.
(* ---- phase D: the end-granule test, both ways ---- *)
assert (HSD : exists tk, st_ok tfibsegs EB (pD hi tk) (restrict H msC)).
{ destruct (branch_taken BC_GE (sv_denot EB (SLit 0)) (sv_denot EB V1)) eqn:Hbr.
  - exists true. exact (st_ok_add_cond tfibsegs EB (peC hi) _ BC_GE (SLit 0) V1 HSC Hbr).
  - exists false. exact (st_ok_add_cond_neg tfibsegs EB (peC hi) _ BC_GE (SLit 0) V1 HSC Hbr). }
destruct HSD as [tk HSD].
eapply SRr_bind; [apply (po_phase W EB (pD hi tk) _ _ _ _ HSD (pr_D hi tk))|].
cbv beta. intros Wd cd _ (-> & msD & matD & -> & HSDf & HFD & HFrD). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (peD hi tk) (restrict H msD)) in HSDf.
assert (MEQD : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = ms_mem msC z).
{ intros z Hz1 Hz2. apply HFD. intros Hin. pose proof (wins_cases EB _ _ (pD_win hi tk) Hin) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. alia. }
clear HFD HFrD.
assert (MEQ : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = mem z).
{ intros z Hz1 Hz2. rewrite (MEQD z Hz1 Hz2), (MEQC z Hz1 Hz2), (MEQB z Hz1 Hz2). exact (MEQA z Hz1). }
clear MEQA MEQB MEQC MEQD.
destruct (pD_facts hi tk) as (PD1 & PD2 & NR0 & NR1).
pose proof (pD_resv hi tk) as RVD.
eapply (SRr_ret_at tfibsegs tbl_po tbl_po_ok Hwx W EB); [exact HSDf | exact RVD | rewrite PD1; exact po_ret_word |].
intros mat'. rewrite wvb_wvb.
assert (RDD : forall (r : bv 5) v, reg_is (peD hi tk) (bv_unsigned r) v = true -> getr (ms_regs msD) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (peD hi tk) msD r HSDf). }
assert (RKD : forall rz, In rz KEPT -> getr (ms_regs msD) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. unfold final_ok in PD2. apply andb_prop in PD2 as [_ FB]. rewrite forallb_forall in FB. specialize (FB rz Hrz). cbn beta in FB.
  assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; unfold KEPT in Hrz; cbn in Hrz; alia).
  assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
  rewrite (RDD (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB].
  cbn [sv_denot]. rewrite (EBreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; alia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RKD 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs msD) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs msD), (ms_mem msD), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs EB (peD hi tk) _ HSDf) as (_ & ROKD & _). change (ms_mem (restrict H msD)) with (mrestrict H (ms_mem msD)) in ROKD.
pose proof (proj1 (Forall_forall _ _) ROKD _ (nth_error_In _ _ NR1)) as OKSH.
destruct pSH_shape as (BSH & WSH1 & WSH2 & CSH0 & CSH1). destruct pSTK_shape as (BS0 & WS01 & WS02).
unfold region_ok in OKSH. rewrite BSH in OKSH. cbn [base_val] in OKSH. unfold aSH in OKSH. rewrite UB32 in OKSH.
destruct OKSH as (_ & _ & _ & CHSH).
assert (P0 : aview tfibsegs H (ms_mem msD) SH = Some shUserPoison).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 0 1%N (SLit 247) 247 (proj1 (Forall_forall _ _) CHSH _ CSH0) eq_refl ltac:(cbn; alia) ltac:(cbn; alia)) as VMx.
  rewrite Z.add_0_r in VMx. exact (aview_of_val_mem1 H (ms_mem msD) SH 247 VMx ltac:(alia)). }
assert (P1 : aview tfibsegs H (ms_mem msD) (SH + 1) = Some shUserPoison).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 1 1%N (SLit 247) 247 (proj1 (Forall_forall _ _) CHSH _ CSH1) eq_refl ltac:(cbn; alia) ltac:(cbn; alia)) as VMx.
  exact (aview_of_val_mem1 H (ms_mem msD) (SH + 1) 247 VMx ltac:(alia)). }
assert (PW : forall b, (sp0 - 64 <= b < sp0 \/ SH <= b < SH + 2) -> apresent H (ms_mem msD) b).
{ intros b [Hbw|Hbw].
  - apply (st_ok_window_apresent H EB (peD hi tk) msD 0 pSTK b HSDf NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EB2; unfold PO_WIN; alia | unfold TFIB_IMG_END; alia].
  - apply (st_ok_window_apresent H EB (peD hi tk) msD 1 pSH b HSDf NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite UB32; alia | pose proof (SHr64 0 ltac:(alia)); pose proof (SHr64 2 ltac:(alia)); alia]. }
assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> ~ (SH <= a < SH + 2) -> aview tfibsegs H (ms_mem msD) a = aview tfibsegs H mem a).
{ intros a Ha N1 N2. apply YF0x.aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (HB' : forall a, in_band_rw a -> H (w64 a) = true -> ms_mem msD (w64 a) = mem (w64 a)).
{ intros a Hbd Hh'. unfold w64 in *. assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hbd; alia).
  apply MEQ; rewrite unsigned_lit_small by exact Ha; intros Hin; [ pose proof (PW a (or_introl Hin)) as (Hx & _) | pose proof (PW a (or_intror Hin)) as (Hx & _) ]; rewrite Hx in Hh'; discriminate Hh'. }
assert (CF8 : cf_head / 8 = 2) by reflexivity.
assert (HARcf : ARcf tfibsegs B ly S (p :: Hp) W (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat' md)).
{ apply (ahead_poison_law_proof tfibsegs B LAWS HF ly S Hp W mem md p n (ms_mem msD) _ (sp0 - 64) sp0 HAR A8 Hb Hn ltac:(alia) ltac:(alia)).
  - intros a Ha N1 N2. apply FR; [exact Ha | exact N1 |]. rewrite CF8 in N2. exact N2.
  - intros a Ha. apply YE2y.aview_some_of_apresent. apply PW. left. exact Ha.
  - intros i Hi. rewrite CF8 in Hi. assert (Hi2 : i = 0 \/ i = 1) by alia. destruct Hi2 as [-> | ->]; [rewrite Z.add_0_r; exact P0 | exact P1].
  - apply MF. - apply MF. - apply MF. - exact HB'. }
split; [exact HARcf|].
split; [|split; [apply with_vm_backing_same|split]].
- intros r Hr. unfold acallee_saved in Hr. apply RKD. clear - Hr. unfold KEPT. cbn. alia.
- intros i Hi. rewrite CF8 in Hi. assert (Hi2 : i = 0 \/ i = 1) by alia. destruct Hi2 as [-> | ->]; [rewrite Z.add_0_r; exact P0 | exact P1].
- split; [|split].
  + intros a Ha N1 N2. apply FR; [exact Ha | alia |]. rewrite CF8 in N2. exact N2.
  + intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [L|L].
    * apply (YF0x.apresent_same H mem); [apply MEQ; rewrite unsigned_lit_small by alia; alia | apply HpresE; alia].
    * apply PW. left. alia.
  + (* the memnorm keep: the walk wrote only [sp0 - 64, sp0) and [SH, SH + 2) *)
    intros MN0. apply (memnorm_frame2 tfibsegs mem (ms_mem msD) (sp0 - 64) sp0 SH (SH + 2) MN0).
    * intros x N1 N2. exact (MEQ x N1 N2).
    * alia.
    * alia.
    * intros x Hx. apply YF0x.tfib_find_segment_none_high. alia.
    * intros x Hx. apply YF0x.tfib_find_segment_none_high. alia.
Qed.

Theorem preset_aunpoison_cf_B102 : @aunpoison_realizes_cf fx rc CfImg_B CfParams_preset tfibsegs B.
Proof.
unfold aunpoison_realizes_cf.
intros ly S Hp W regs mem md p n HPRE G10 G11 A8 Hin Hb Hn.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof YF0x.Hwx_tfa as Hwx.
pose proof (proj1 HAR) as M.
pose proof (amc_layout _ _ _ _ _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as CR.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (A16 : cf_head = 16) by reflexivity.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Lbeg Lhi Hslo Htop; unfold kHighMemBeg, kHighMemEnd in *; alia).
destruct (alc_blocks _ _ LAWS ly S Hp W mem md p n HAR Hb) as (P16 & P4096 & PC & PAPP & _).
pose proof (p8_of_p16 p P16) as H8.
destruct (head_end_ok ly S Hp W mem md p n HAR Hb Hn) as [ZONE HV2n].
destruct (head_bytes ly S Hp W mem md p n HAR Hb Hn A8) as (HVv & HVr & HV0).
destruct ZONE as [hi HZ].
assert (Hh : 4096 <= p < 2 ^ 47) by (destruct hi; unfold hLO, hHI, kHighMemBeg, kHighMemEnd, kLowShadowBeg in HZ; alia).
set (SH := shadow_addr p).
assert (HSH : SH = SHADOW_OFF + p / 8) by reflexivity.
assert (SHr : shLO hi <= SH <= shHI hi).
{ rewrite HSH. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|alia]. rewrite Hq, Z.div_mul by alia.
  destruct hi; unfold shLO, shHI, hLO, hHI, SHADOW_OFF, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg, kHighMemEnd in *; alia. }
assert (SHb : kLowShadowBeg <= SH /\ SH + 3 <= kHighMemBeg)
  by (clear - SHr; destruct hi; unfold shLO, shHI, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, kHighMemBeg in *; alia).
destruct SHb as [SHb1 SHb2].
assert (SHnum : 2147446784 <= SH /\ SH + 3 <= 17594333495296) by (clear - SHb1 SHb2; unfold kLowShadowBeg, kHighMemBeg in *; alia).
destruct SHnum as [SHn1 SHn2].
assert (SH2 : shadow_addr (p + cf_head) = SH + 2).
{ rewrite HSH, A16. unfold shadow_addr. pose proof H8 as H8'. apply Z.mod_divide in H8' as [q Hq]; [|alia]. rewrite Hq.
  replace (q * 8 + 16) with ((q + 2) * 8) by alia. rewrite !Z.div_mul by alia. alia. }
rewrite SH2 in HV2n.
assert (HV2 : exists VB, aview tfibsegs H mem (SH + 2) = Some VB).
{ destruct (aview tfibsegs H mem (SH + 2)) as [v|] eqn:Ev; [exists v; reflexivity | exfalso; exact (HV2n Ev)]. }
destruct HV2 as [VB HVB].
pose proof (YE2y.aview_byte_ex H mem (SH + 2) VB HVB) as (bVB & _ & _ & HVBr).
set (E0 := YE2y.Env regs []).
assert (E0reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (E02 : bv_unsigned (ew E0 2) = sp0) by (rewrite (E0reg 2%nat 2%bv eq_refl); reflexivity).
assert (E010 : bv_unsigned (ew E0 10) = p) by (rewrite (E0reg 10%nat 10%bv eq_refl), G10; unfold w64; apply unsigned_lit_small; alia).
assert (G11' : getr regs 11 = w64 16) by (rewrite G11, A16; reflexivity).
assert (HS0 : st_ok tfibsegs E0 (ssA UP_ENTRY hi) (restrict H (mkst regs (Z_to_bv 64 UP_ENTRY) mem (seg_rom tfibsegs)))).
{ unfold ssA.
  apply (YF0x.st_ok_pin_reg E0 (ssA0 UP_ENTRY hi) _ 11%bv (SLit 16)); [| intros X; discriminate X | rewrite restrict_mkst_fx; cbn [sv_denot ms_regs mkst]; rewrite G11'; reflexivity].
  unfold ssA0. rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold memA. apply Forall_cons; [|exact (po_rodata_ok_cf ly S Hp W mem md E0 HAR)].
    unfold stkA, PO_WIN. apply (region_ok_stack tfibsegs E0 _ 2 sp0 (- 64)); [exact E02 | alia | alia |].
    intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply HpresE. alia.
  - apply pairwise_disjoint_of_extents. unfold memA, stkA, po_rodata, icpt_rodata, ro_region, extent_of_region, PO_WIN.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E02.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; alia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E02, E010.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try alia; first [exact Hal16 | exact H8 | idtac]. }
eapply SRr_bind; [apply (po_phase W E0 _ _ _ _ _ HS0 (ur_A hi))|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
change (st_ok tfibsegs E0 (ueA hi) (restrict H msA)) in HSA.
assert (MEQA : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ms_mem msA z = mem z).
{ intros z Hz. apply HFA. intros Hinw. pose proof (winsA_cases E0 _ _ (uA_win hi) Hinw) as X. rewrite E02 in X. unfold PO_WIN in X. alia. }
clear HFA HFrA.
destruct (uA_facts hi) as (PA1 & PA2 & PA3 & PA4 & PA5 & PA6).
pose proof (st_ok_restrict_mkst tfibsegs H E0 _ _ HSA PA2) as HshA. rewrite PA1 in HshA.
assert (RDA : forall (r : bv 5) v, reg_is (ueA hi) (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E0 (ueA hi) msA r HSA). }
assert (G19A : getr (ms_regs msA) 19 = Z_to_bv 64 SH).
{ rewrite (RDA 19%bv _ PA4). rewrite (XS0_denot E0 0 p E010) by alia. rewrite Z.add_0_r. reflexivity. }
assert (G10A : getr (ms_regs msA) 10 = Z_to_bv 64 SH).
{ rewrite (RDA 10%bv _ PA5). rewrite (XS_denot E0 0 p E010) by alia. rewrite Z.add_0_r. reflexivity. }
set (EB := YE2y.Env regs [SH; VB; HVv]).
assert (AGR : env_agree 32 E0 EB) by (unfold E0, EB, YE2y.Env; cbn [map]; apply (env_agree_Ereg_app' regs [] [Z_to_bv 64 SH; Z_to_bv 64 VB; Z_to_bv 64 HVv] 32); cbn; alia).
assert (EBreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EB i = getr regs r) by (intros; apply YE2y.Env_reg; assumption).
assert (EB2 : bv_unsigned (ew EB 2) = sp0) by (rewrite (EBreg 2%nat 2%bv eq_refl); reflexivity).
assert (EB10 : bv_unsigned (ew EB 10) = p) by (rewrite (EBreg 10%nat 10%bv eq_refl), G10; unfold w64; apply unsigned_lit_small; alia).
assert (UB32 : bv_unsigned (ew EB 32) = SH) by (pose proof (YE2y.Env_x regs [SH; VB; HVv] 0 SH eq_refl) as X; cbn [Nat.add] in X; change (YE2y.Env regs [SH; VB; HVv]) with EB in X; rewrite X; apply unsigned_lit_small; clear - SHb1 SHb2; alia).
assert (UB33 : bv_unsigned (ew EB 33) = VB) by (pose proof (YE2y.Env_x regs [SH; VB; HVv] 1 VB eq_refl) as X; cbn [Nat.add] in X; change (YE2y.Env regs [SH; VB; HVv]) with EB in X; rewrite X; apply unsigned_lit_small; alia).
assert (UB34 : bv_unsigned (ew EB 34) = HVv) by (pose proof (YE2y.Env_x regs [SH; VB; HVv] 2 HVv eq_refl) as X; cbn [Nat.add] in X; change (YE2y.Env regs [SH; VB; HVv]) with EB in X; rewrite X; apply unsigned_lit_small; alia).
assert (VM1 : forall a v, ~ (sp0 - 64 <= a < sp0) -> 0 <= a < 2 ^ 64 -> aview tfibsegs H mem a = Some v ->
  val_mem tfibsegs (mrestrict H (ms_mem msA)) a 1 v).
{ intros a v Ha Hr Hv. apply (YF0x.val_mem_ext (mrestrict H mem)); [| apply val_mem1_of_aview; exact Hv].
  intros k Hk. replace k with 0%nat by alia. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite MEQA; [reflexivity|]. rewrite unsigned_lit_small by alia. alia. }
assert (SHnS : forall j, 0 <= j < 3 -> ~ (sp0 - 64 <= SH + j < sp0)) by (intros j Hj; clear - SHb1 SHb2 Hslo Lbeg Hj; alia).
assert (SHr64 : forall j, 0 <= j < 3 -> TFIB_IMG_END <= SH + j < 2 ^ 64) by (intros j Hj; clear - SHn1 SHn2 Hj; unfold TFIB_IMG_END in *; alia).
rewrite HshA in HSA. rewrite restrict_mkst_fx in HSA.
assert (HSB0 : st_ok tfibsegs EB (uB hi) (restrict H (mkst (ms_regs msA) (Z_to_bv 64 U_LDA) (ms_mem msA) (seg_rom tfibsegs)))).
{ rewrite <- (uB_eq hi). unfold upB. rewrite PA1. rewrite restrict_mkst_fx.
  apply st_ok_add_fact0; [| reflexivity | unfold aHV; rewrite UB34; alia].
  apply st_ok_add_fact0; [| reflexivity | unfold aV; rewrite UB33; alia].
  apply st_ok_add_fact0; [| reflexivity | unfold aSH; rewrite UB32; exact SHr].
  apply (st_ok_set_regs_mem tfibsegs 32 E0 EB (ueA hi) (ms_regs msA) (ms_regs msA) (Z_to_bv 64 U_LDA) U_LDA
    (mrestrict H (ms_mem msA)) (mrestrict H (ms_mem msA)) (memB (ueA hi)) updUB HSA AGR PA3).
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - unfold updUB. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
    + rewrite G19A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
    + rewrite G10A. cbn [sv_denot]. unfold aSH. rewrite UB32, Z.add_0_r. reflexivity.
  - pose proof (st_ok_agree tfibsegs 32 E0 EB (ueA hi) _ HSA AGR PA3) as HSA'.
    pose proof (st_ok_mem_ok tfibsegs EB (ueA hi) _ HSA') as (WFA & ROKA & PDA).
    split; [rewrite memUB_eq; vm_compute; reflexivity|]. split.
    + unfold memB. rewrite PA6 in ROKA. apply Forall_cons; [exact (Forall_inv ROKA)|]. apply Forall_cons; [|exact (Forall_inv_tail ROKA)].
      unfold rSH, aSH, region_ok. cbv zeta. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UB32.
      refine (conj _ (conj _ (conj _ _))); [clear - SHn1 SHn2; alia | clear - SHn1 SHn2; alia | |].
      { intros o Ho. apply (YF0x.apresent_writable H); [apply SHr64; alia|].
        apply (YF0x.apresent_same H mem); [apply MEQA; rewrite unsigned_lit_small by (pose proof (SHr64 o ltac:(alia)); alia); apply SHnS; alia|].
        exact (vis_apresent' H mem (SH + o) HVv (SHr64 o ltac:(alia)) (HV0 o ltac:(alia))). }
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val tfibsegs EB _ SH 0 1%N (SOff aHV 0) HVv); [cbn [sv_denot]; unfold aHV; rewrite UB34, Z.add_0_r; reflexivity | cbn; alia | cbn; alia |].
        apply VM1; [apply SHnS; alia | pose proof (SHr64 0 ltac:(alia)); alia | exact (HV0 0 ltac:(alia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 1 1%N (SOff aHV 0) HVv); [cbn [sv_denot]; unfold aHV; rewrite UB34, Z.add_0_r; reflexivity | cbn; alia | cbn; alia |].
        apply VM1; [apply SHnS; alia | pose proof (SHr64 1 ltac:(alia)); alia | exact (HV0 1 ltac:(alia))].
      * apply (chunk_ok_val tfibsegs EB _ SH 2 1%N (SOff aV 0) VB); [cbn [sv_denot]; unfold aV; rewrite UB33, Z.add_0_r; reflexivity | cbn; alia | cbn; alia |].
        apply VM1; [apply SHnS; alia | pose proof (SHr64 2 ltac:(alia)); alia | exact HVB].
    + apply pairwise_disjoint_of_extents. rewrite memUB_eq. let l' := eval vm_compute in memUBc in change memUBc with l'.
      unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EB2, ?UB32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      clear - SHb1 SHb2 Hsp Hslo Lbeg. unfold kLowShadowBeg, kHighMemBeg in *. repeat split; alia. }
rewrite HshA.
eapply SRr_bind; [apply (po_phase W EB (uB hi) _ _ _ _ HSB0 (ur_B hi))|].
cbv beta. intros Wb cb _ (-> & msB & matB & -> & HSB & HFB & HFrB). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (ueB hi) (restrict H msB)) in HSB.
assert (MEQB : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msB z = ms_mem msA z).
{ intros z Hz1 Hz2. apply HFB. intros Hinw. pose proof (wins_cases EB _ _ (uB_win hi) Hinw) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. alia. }
clear HFB HFrB.
destruct (uB_facts hi) as (PB1 & PB2 & PB3 & PB4).
pose proof (st_ok_restrict_mkst tfibsegs H EB _ _ HSB PB2) as HshB. rewrite PB1 in HshB.
assert (RDB : forall (r : bv 5) v, reg_is (ueB hi) (bv_unsigned r) v = true -> getr (ms_regs msB) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (ueB hi) msB r HSB). }
assert (G9B : getr (ms_regs msB) 9 = Z_to_bv 64 (SH + 2)).
{ rewrite (RDB 9%bv _ PB4). rewrite (XS0_denot EB 16 p EB10) by alia. rewrite <- A16, <- SH2. reflexivity. }
rewrite HshB in HSB. rewrite restrict_mkst_fx in HSB.
assert (HSC0 : st_ok tfibsegs EB (uC hi) (restrict H (mkst (ms_regs msB) (Z_to_bv 64 U_LDB) (ms_mem msB) (seg_rom tfibsegs)))).
{ rewrite <- (uC_eq hi). unfold upC. rewrite PB1. rewrite restrict_mkst_fx.
  apply (st_ok_set_regs_mem tfibsegs 35 EB EB (ueB hi) (ms_regs msB) (ms_regs msB) (Z_to_bv 64 U_LDB) U_LDB
    (mrestrict H (ms_mem msB)) (mrestrict H (ms_mem msB)) (ss_mem (ueB hi)) [((9%bv : bv 5), SOff aSH 2)] HSB).
  - split; [intros; reflexivity | reflexivity].
  - exact PB3.
  - vm_compute. reflexivity.
  - intros r Hr. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G9B. cbn [sv_denot]. unfold aSH. rewrite UB32. reflexivity.
  - exact (st_ok_mem_ok tfibsegs EB (ueB hi) _ HSB). }
rewrite HshB.
eapply SRr_bind; [apply (po_phase W EB (uC hi) _ _ _ _ HSC0 (ur_C hi))|].
cbv beta. intros Wc cc _ (-> & msD & matC & -> & HSDf & HFC & HFrC). rewrite ?wvb_wvb in *.
change (st_ok tfibsegs EB (ueC hi) (restrict H msD)) in HSDf.
assert (MEQC : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = ms_mem msB z).
{ intros z Hz1 Hz2. apply HFC. intros Hinw. pose proof (wins_cases EB _ _ (uC_win hi) Hinw) as X. rewrite EB2, UB32 in X. unfold PO_WIN in X. alia. }
clear HFC HFrC.
assert (MEQ : forall z : word, ~ (sp0 - 64 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 2) -> ms_mem msD z = mem z).
{ intros z Hz1 Hz2. rewrite (MEQC z Hz1 Hz2), (MEQB z Hz1 Hz2). exact (MEQA z Hz1). }
clear MEQA MEQB MEQC.
destruct (uC_facts hi) as (PD1 & PD2 & RVD & NR0 & NR1).
eapply (SRr_ret_at tfibsegs tbl_po tbl_po_ok Hwx W EB); [exact HSDf | exact RVD | rewrite PD1; exact up_ret_word |].
intros mat'. rewrite wvb_wvb.
assert (RDD : forall (r : bv 5) v, reg_is (ueC hi) (bv_unsigned r) v = true -> getr (ms_regs msD) r = sv_denot EB v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EB (ueC hi) msD r HSDf). }
assert (RKD : forall rz, In rz KEPT -> getr (ms_regs msD) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. unfold final_ok in PD2. apply andb_prop in PD2 as [_ FB]. rewrite forallb_forall in FB. specialize (FB rz Hrz). cbn beta in FB.
  assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; unfold KEPT in Hrz; cbn in Hrz; alia).
  assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
  rewrite (RDD (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB].
  cbn [sv_denot]. rewrite (EBreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; alia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RKD 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs msD) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs msD), (ms_mem msD), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs EB (ueC hi) _ HSDf) as (_ & ROKD & _). change (ms_mem (restrict H msD)) with (mrestrict H (ms_mem msD)) in ROKD.
pose proof (proj1 (Forall_forall _ _) ROKD _ (nth_error_In _ _ NR1)) as OKSH.
destruct uSH_shape as (BSH & WSH1 & WSH2 & CSH0 & CSH1). destruct uSTK_shape as (BS0 & WS01 & WS02).
unfold region_ok in OKSH. rewrite BSH in OKSH. cbn [base_val] in OKSH. unfold aSH in OKSH. rewrite UB32 in OKSH.
destruct OKSH as (_ & _ & _ & CHSH).
assert (P0 : aview tfibsegs H (ms_mem msD) SH = Some 0).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 0 1%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHSH _ CSH0) eq_refl ltac:(cbn; alia) ltac:(cbn; alia)) as VMx.
  rewrite Z.add_0_r in VMx. exact (aview_of_val_mem1 H (ms_mem msD) SH 0 VMx ltac:(alia)). }
assert (P1 : aview tfibsegs H (ms_mem msD) (SH + 1) = Some 0).
{ pose proof (val_of_chunk_ok tfibsegs EB _ SH 1 1%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHSH _ CSH1) eq_refl ltac:(cbn; alia) ltac:(cbn; alia)) as VMx.
  exact (aview_of_val_mem1 H (ms_mem msD) (SH + 1) 0 VMx ltac:(alia)). }
assert (PW : forall b, (sp0 - 64 <= b < sp0 \/ SH <= b < SH + 2) -> apresent H (ms_mem msD) b).
{ intros b [Hbw|Hbw].
  - apply (st_ok_window_apresent H EB (ueC hi) msD 0 uSTK b HSDf NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EB2; unfold PO_WIN; alia | unfold TFIB_IMG_END; alia].
  - apply (st_ok_window_apresent H EB (ueC hi) msD 1 uSH b HSDf NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite UB32; alia | pose proof (SHr64 0 ltac:(alia)); pose proof (SHr64 2 ltac:(alia)); alia]. }
assert (FR : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 64 <= a < sp0) -> ~ (SH <= a < SH + 2) -> aview tfibsegs H (ms_mem msD) a = aview tfibsegs H mem a).
{ intros a Ha N1 N2. apply YF0x.aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; assumption. }
assert (HB' : forall a, in_band_rw a -> H (w64 a) = true -> ms_mem msD (w64 a) = mem (w64 a)).
{ intros a Hbd Hh'. unfold w64 in *. assert (Ha : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hbd; alia).
  apply MEQ; rewrite unsigned_lit_small by exact Ha; intros Hinw; [ pose proof (PW a (or_introl Hinw)) as (Hx & _) | pose proof (PW a (or_intror Hinw)) as (Hx & _) ]; rewrite Hx in Hh'; discriminate Hh'. }
assert (CF8 : cf_head / 8 = 2) by reflexivity.
assert (HARcf : ARcf tfibsegs B ly S (remove Z.eq_dec p Hp) W (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat' md)).
{ apply (ahead_unpoison_law_proof tfibsegs B LAWS HF ly S Hp W mem md p (ms_mem msD) _ (sp0 - 64) sp0 HAR A8 Hin ltac:(alia) ltac:(alia)).
  - intros a Ha N1 N2. apply FR; [exact Ha | exact N1 |]. rewrite CF8 in N2. exact N2.
  - intros a Ha. apply YE2y.aview_some_of_apresent. apply PW. left. exact Ha.
  - intros i Hi. rewrite CF8 in Hi. assert (Hi2 : i = 0 \/ i = 1) by alia. destruct Hi2 as [-> | ->]; [rewrite Z.add_0_r; exact P0 | exact P1].
  - apply MF. - apply MF. - apply MF. - exact HB'. }
split; [exact HARcf|].
split; [|split; [apply with_vm_backing_same|split]].
- intros r Hr. unfold acallee_saved in Hr. apply RKD. clear - Hr. unfold KEPT. cbn. alia.
- intros i Hi. rewrite CF8 in Hi. assert (Hi2 : i = 0 \/ i = 1) by alia. destruct Hi2 as [-> | ->]; [rewrite Z.add_0_r; exact P0 | exact P1].
- split; [|split].
  + intros a Ha N1 N2. apply FR; [exact Ha | alia |]. rewrite CF8 in N2. exact N2.
  + intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 64)) as [L|L].
    * apply (YF0x.apresent_same H mem); [apply MEQ; rewrite unsigned_lit_small by alia; alia | apply HpresE; alia].
    * apply PW. left. alia.
  + (* the memnorm keep: the walk wrote only [sp0 - 64, sp0) and [SH, SH + 2) *)
    intros MN0. apply (memnorm_frame2 tfibsegs mem (ms_mem msD) (sp0 - 64) sp0 SH (SH + 2) MN0).
    * intros x N1 N2. exact (MEQ x N1 N2).
    * alia.
    * alia.
    * intros x Hx. apply YF0x.tfib_find_segment_none_high. alia.
    * intros x Hx. apply YF0x.tfib_find_segment_none_high. alia.
Qed.
End f.
