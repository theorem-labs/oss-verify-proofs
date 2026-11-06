(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdy YCfr YCe9 YCfx YChv YChx YChn YCf6 YCft YCey YCe4 YCi1 YCrr YCib YCrn YCrm YCrt YCru YCrb.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma rfb_val_mem_byte1 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> exists v, 0 <= v < 256 /\ val_mem trbsegs (mrestrict H m) a 1 v.
Proof.
intros H m a [Hh [b Hb]]. exists (bv_unsigned b). pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn [Z.of_N] in R. change (2 ^ 8) with 256 in R.
split; [lia|]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. unfold mbyte, mrestrict. rewrite Hh. cbn. rewrite Hb. f_equal.
unfold YP0g.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r. rewrite (Z.mod_small (bv_unsigned b) 256) by lia. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma rfb_val_mem_byte2 : forall (H : word -> bool) (m : word -> option byte) a,
apresent H m a -> apresent H m (a + 1) -> exists v, 0 <= v < 65536 /\ val_mem trbsegs (mrestrict H m) a 2 v.
Proof.
intros H m a Ha0 Ha1.
destruct (rfb_val_mem_byte1 H m a Ha0) as (v0 & R0 & V0). destruct (rfb_val_mem_byte1 H m (a + 1) Ha1) as (v1 & R1 & V1).
exists (v0 + 256 * v1). split; [lia|]. intros k Hk.
assert (L0 : YP0g.le_byte v0 1 0 = v0) by (unfold YP0g.le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.shiftr_0_r, !(Z.mod_small v0 256) by lia; reflexivity).
assert (L1 : YP0g.le_byte v1 1 0 = v1) by (unfold YP0g.le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite Z.shiftr_0_r, !(Z.mod_small v1 256) by lia; reflexivity).
assert (M0 : YP0g.le_byte (v0 + 256 * v1) 2 0 = v0).
{ unfold YP0g.le_byte. change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite Z.shiftr_0_r, (Z.mod_small _ 65536) by lia.
replace (256 * v1) with (v1 * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (M1 : YP0g.le_byte (v0 + 256 * v1) 2 1 = v1).
{ unfold YP0g.le_byte. change (8 * Z.of_nat 1) with 8. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite (Z.mod_small _ 65536) by lia.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. replace (v0 + 256 * v1) with (v1 * 256 + v0) by lia.
rewrite Z.div_add_l by lia. rewrite (Z.div_small v0 256) by lia. rewrite Z.add_0_r. apply Z.mod_small. lia. }
destruct k as [|[|k]]; [| |lia].
- specialize (V0 0%nat ltac:(lia)). cbn [Z.of_nat] in *. rewrite V0, L0, M0. reflexivity.
- specialize (V1 0%nat ltac:(lia)). change (Z.of_nat 1) with 1. cbn [Z.of_nat] in V1. rewrite Z.add_0_r in V1. rewrite V1, L1, M1. reflexivity.
Qed.
Lemma rf_obj_of_regionB : forall E (H : word -> bool) (m : word -> option byte) b cs lo hi wlo whi e0 e8 v0 v8,
region_ok trbsegs E (mrestrict H m) (YQ0b.mkRegion (Some 11%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 11) = b ->
In (YQ0b.mkChunk 0 (CVal 8 e0)) cs -> In (YQ0b.mkChunk 8 (CVal 4 e8)) cs ->
sv_denot E e0 = Z_to_bv 64 v0 -> 0 <= v0 < 2 ^ 64 -> sv_denot E e8 = Z_to_bv 64 v8 -> 0 <= v8 < 2 ^ 32 ->
(forall a, b + 12 <= a < b + 22 -> apresent H m a) ->
exists fattr fgen delay, obj_at trbsegs (mrestrict H m) b LAY_RgbFrameConfig [v0; v8; fattr; fgen; delay].
Proof.
intros E H m b cs lo hi wlo whi e0 e8 v0 v8 HR Hb I0 I8 D0 R0 D8 R8 HP.
pose proof (field_of_region E _ 11 b cs lo hi wlo whi 0 8%N e0 v0 HR Hb I0 D0 ltac:(exact R0) ltac:(cbn; lia)) as V0.
pose proof (field_of_region E _ 11 b cs lo hi wlo whi 8 4%N e8 v8 HR Hb I8 D8 ltac:(exact R8) ltac:(cbn; lia)) as V8.
assert (PM : forall a, b + 12 <= a < b + 22 -> exists bb, mbyte trbsegs (mrestrict H m) a = Some bb)
by (intros a Ha; destruct (HP a Ha) as [Hh [bb Hbb]]; exists bb; unfold mbyte, mrestrict; rewrite Hh, Hbb; reflexivity).
destruct (val_mem_of_present4 trbsegs (mrestrict H m) (b + 12) ltac:(intros i Hi; apply PM; clear - Hi; lia)) as (fattr & R3 & V3).
destruct (val_mem_of_present4 trbsegs (mrestrict H m) (b + 16) ltac:(intros i Hi; apply PM; clear - Hi; lia)) as (fgen & R4 & V4).
destruct (rfb_val_mem_byte2 H m (b + 20) (HP (b + 20) ltac:(clear; lia)) (HP (b + 20 + 1) ltac:(clear; lia))) as (delay & R5 & V5).
exists fattr, fgen, delay.
unfold LAY_RgbFrameConfig. cbn [obj_at]. unfold field_ok. cbn [fst snd]. change (N.to_nat 8) with 8%nat in *. change (N.to_nat 4) with 4%nat in *. change (N.to_nat 2) with 2%nat.
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). change (2 ^ (8 * Z.of_N 4)) with 4294967296. change (2 ^ (8 * Z.of_N 2)) with 65536. change (2 ^ 32) with 4294967296 in *.
rewrite ?Z.add_0_r in *.
repeat split; try assumption; try lia.
Qed.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Lemma rf_fsep_intro : forall ly3 S3 W3 m3 md3 lyc (Sc : astate) (Bb : list (Z * Z)) fpos,
AR trbsegs B ly3 S3 W3 m3 md3 -> frames S3 = (0, fpos) :: frames Sc ->
(forall c p, frame_addr ly3 c p = frame_addr lyc c p) ->
(forall b, In b Bb -> In b (ablocks B ly3 S3)) ->
(forall b m i, In (b, m) Bb -> 0 <= i < req_size m ->
~ (in_zr (b + i) (frame_rng lyc (0, fpos)) \/ in_zr (b + i) (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8))) /\
(forall c p a, In (c, p) (frames Sc) ->
(in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) ->
~ (in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8))).
Proof.
intros ly3 S3 W3 m3 md3 lyc Sc Bb fpos HAR Hfrs EFA HBb.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
assert (Hfin0 : In (0, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR Hfin0) as (HFal & HFapp & _).
destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ 0 fpos HAR Hfin0) as (HF4096 & HFceil & _).
rewrite !EFA in *. change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8.
set (F := frame_addr lyc 0 fpos) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HF8 : 8 * (F / 8) = F) by (pose proof (Z.div_mod F 8 ltac:(lia)) as Q; replace (F mod 8) with 0 in Q; [lia|]; symmetry; replace F with (32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia); replace (32 * (F / 32)) with ((4 * (F / 32)) * 8) by lia; apply Z_mod_mult).
pose proof (shadow_addr_bounds F ltac:(lia)) as SBF. pose proof (shadow_addr_bounds (F + 64) ltac:(lia)) as SBF2.
pose proof (shadow_range_end F 64 ltac:(lia)) as SEF. change (64 / 8) with 8 in SEF.
split.
- intros b m i Hb Hi.
pose proof (HBb _ Hb) as Hb3.
pose proof (sep_block_frame trbsegs B LAWS _ _ _ _ _ b m 0 fpos HAR Hb3 Hfin0) as D. unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA in D. fold F in D. change (fs_frame_bytes 0) with 64 in D.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hb3) as (_ & Hb4096 & Hbceil & [_ Hbapp] & _).
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 0) with 64. unfold kLowMemEnd, kHighShadowEnd in *.
intros [X | X]; lia.
- intros c p a Hcp Ha.
assert (Hcp3 : In (c, p) (frames S3)) by (rewrite Hfrs; right; exact Hcp).
destruct (in_split _ _ Hcp) as (l2 & l3 & El).
pose proof (sep_frames_pos trbsegs B LAWS _ _ _ _ _ (0, fpos) (c, p) [] l2 l3 HAR ltac:(rewrite Hfrs, El; reflexivity)) as D.
unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite !EFA in D. fold F in D. change (fs_frame_bytes 0) with 64 in D.
destruct (al_frames _ _ LAWS _ _ _ _ _ c p HAR Hcp3) as (HGal & HGapp & _).
destruct (frames_bounds trbsegs B LAWS _ _ _ _ _ c p HAR Hcp3) as (HG4096 & HGceil & _).
rewrite !EFA in *. set (G := frame_addr lyc c p) in *. pose proof (fs_frame_bytes_nonneg c) as HGB.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp.
assert (HG8 : 8 * (G / 8) = G) by (pose proof (Z.div_mod G 8 ltac:(lia)) as Q; replace (G mod 8) with 0 in Q; [lia|]; symmetry; replace G with (32 * (G / 32)) by (pose proof (Z.div_mod G 32 ltac:(lia)); lia); replace (32 * (G / 32)) with ((4 * (G / 32)) * 8) by lia; apply Z_mod_mult).
pose proof (shadow_addr_bounds G ltac:(lia)) as SBG. pose proof (shadow_addr_bounds (G + fs_frame_bytes c) ltac:(lia)) as SBG2.
pose proof (shadow_range_end G (fs_frame_bytes c) HGB) as SEG.
assert (HGs8 : 8 * (fs_frame_bytes c / 8) <= fs_frame_bytes c) by (apply Z.mul_div_le; lia).
unfold in_zr, frame_rng in *. cbn [fst snd] in *. fold F. fold G in Ha. change (fs_frame_bytes 0) with 64. unfold kLowMemEnd, kHighShadowEnd in *.
unfold shadow_addr in *.
assert (HSH : F + 64 <= G -> F / 8 + 8 <= G / 8) by (intros; lia).
assert (HSH2 : G + fs_frame_bytes c <= F -> G / 8 + fs_frame_bytes c / 8 <= F / 8) by (intros; lia).
intros [X | X]; destruct Ha as [Y | Y]; lia.
Qed.
Lemma rfc_kept_callF : forall W memc W1 mem1 W2 mem2 sp Bb lyc Sc lyc' Sc' st dst slo shi (Er : Z -> Prop),
rfc_kept W memc W1 mem1 sp Bb lyc Sc st dst ->
acall_kept trbsegs B lyc' Sc' W1 mem1 W2 mem2 slo shi Er ->
sp - TRRFC_STK <= slo -> shi <= sp ->
(forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc' Sc')) -> (forall b m i, In (b, m) Bb -> 0 <= i < req_size m -> ~ Er (b + i)) ->
(forall c p, In (c, p) (frames Sc) -> In (c, p) (frames Sc')) -> (forall c p, frame_addr lyc' c p = frame_addr lyc c p) ->
(forall c p a, In (c, p) (frames Sc) -> (in_zr a (frame_rng lyc (c, p)) \/ in_zr a (shadow_addr (frame_addr lyc c p), fs_frame_bytes c / 8)) -> ~ Er a) ->
rfc_kept W memc W2 mem2 sp Bb lyc Sc st dst.
Proof.
intros W memc W1 mem1 W2 mem2 sp Bb lyc Sc lyc' Sc' st dst slo shi Er (K1 & K2 & K3) (A1 & A2 & _ & A4 & _) Hslo Hshi HBb HnE Hfr EFA HnF.
split; [|split].
- intros a Ha N1 N2 N3. rewrite <- (K1 a Ha N1 N2 N3). apply A1; [exact Ha | lia].
- intros b m i Hb Hi. rewrite <- (K2 b m i Hb Hi). apply (A2 b m i (HBb b m Hb) Hi). exact (HnE b m i Hb Hi).
- intros c p a Hcp Ha N2 N3. rewrite <- (K3 c p a Hcp Ha N2 N3).
apply (A4 c p a); [apply Hfr; exact Hcp | unfold frame_rng; cbn [fst snd]; rewrite !EFA; exact Ha | apply (HnF c p a Hcp Ha)].
Qed.
Lemma RA_dst_kept : forall W memc W3 m3 sp Bb lyc Sc st dst cid pos,
rfc_kept W memc W3 m3 sp Bb lyc Sc st dst -> In (cid, pos) (frames Sc) -> 0 <= cid -> frame_addr lyc cid pos mod 8 = 0 ->
frame_addr lyc cid pos <= dst -> dst + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
in_app (frame_addr lyc cid pos) (fs_frame_bytes cid) -> frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling -> alloc_ceiling <= st ->
range_addressable (aview trbsegs (w_H W) memc) SHADOW_OFF dst 24 -> range_addressable (aview trbsegs (w_H W3) m3) SHADOW_OFF dst 24.
Proof.
intros W memc W3 m3 sp Bb lyc Sc st dst cid pos (_ & _ & K3) Hfin Hcid Hfal Hd1 Hd2 Happ Hceil Hst HRA.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). ceil.
eapply (RA_kept_frame _ _ (frame_addr lyc cid pos) cid dst 24); [|exact Hcid|exact Hfal|exact Hd1|exact Hd2|exact HRA].
intros a Ha. apply (K3 cid pos a Hfin (or_intror Ha)).
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (frame_shadow_low (frame_addr lyc cid pos) cid a ltac:(lia) Hceil Ha) as Hlow. unfold kHighShadowEnd in Hlow. pose proof (fs_frame_bytes_nonneg cid). lia.
- pose proof (frame_shadow_low (frame_addr lyc cid pos) cid a ltac:(unfold in_app in Happ; lia) Hceil Ha) as Hlow. unfold kHighShadowEnd in Hlow. lia.
Qed.
Lemma rf_chain_push : forall lyc ly3 (rd0 rd : reader) st fp v ra ch sp',
achain lyc rd0 (st + 24) v ch -> ly_top ly3 = ly_top lyc -> ly_top lyc <= 2 ^ 64 ->
(forall a, st + 24 <= a < 2 ^ 64 -> rd a = rd0 a) -> fp <= st ->
rdword rd (fp - 8) = Some ra -> rdword rd (fp - 16) = Some v -> 4096 <= ra ->
alloc_ceiling <= fp -> fp mod 8 = 0 -> fp < ly_top lyc - 16 -> sp' + 16 <= fp ->
achain ly3 rd sp' fp ((fp, ra, v) :: ch).
Proof.
intros lyc ly3 rd0 rd st fp v ra ch sp' HCH Etop Htop UP Hfp H8 H16 Hra Hceil Hal Hlt Hsp'.
apply (achain_ly_top lyc ly3 _ _ _ _ Etop).
pose proof (achain_kept lyc rd0 rd (st + 24) v ch (st + 24) HCH ltac:(lia) Htop UP) as HC1.
pose proof (achain_lower lyc rd (st + 24) fp v ch HC1 ltac:(lia)) as HC2.
exact (achain_push lyc rd rd fp v ra ch sp' HC2 Htop (fun a _ => eq_refl) H8 H16 Hra Hceil Hal Hlt Hsp').
Qed.
End f.
End d.
Ltac rfb_zs_lia F :=
cbn beta; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite <- ?SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64;
try (fold F); unfold SB in *; lia.
Ltac unrunB HFr Zs AG F UN :=
pose proof (kept_of_frame _ _ _ _ _ Zs HFr
ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
let Hi := fresh "Hi" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
intros b wlo whi a Hi Hr; vm_compute in Hi;
repeat (destruct Hi as [Hq | Hi]; [injection Hq as <- <- <-; cbn [base_val] in Hr; revert Hr; evalE AG; intros Hr; rfb_zs_lia F |]); destruct Hi)) as UN.
Ltac rfb_after_run AG HJn :=
lazymatch goal with
| HFr : frame_of _ _ (mrestrict (w_H ?W3) ?mold) (mrestrict (w_H ?W3) ?mnew) |- _ =>
lazymatch goal with
| HK : rfc_kept ?W ?memc W3 mold ?spz ?Bb ?lyc ?Sc ?st ?dst, HSP : rfc_sep ?spz _ _ _ ?st ?dst,
HB : forall b m i, In (b, m) ?Bb -> _ -> ~ _, HFf : forall c p a, In (c, p) (frames ?Sc) -> _ -> ~ _,
RAs : range_addressable (aview trbsegs (w_H W3) mold) SHADOW_OFF ?st 24,
RAd : range_addressable (aview trbsegs (w_H W3) mold) SHADOW_OFF ?dst 24,
Fv := frame_addr ?lyc 0 ?fpos |- _ =>
let UN := fresh "UN" in let K2 := fresh "HKEPT" in
unrunB HFr (fun a => spz - TRRFC_STK <= a < spz \/ dst <= a < dst + 24 \/ st + 16 <= a < st + 24 \/
(in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8))) AG Fv UN;
pose proof (rfc_kept_stepE _ _ _ _ _ _ _ _ _ _ _ _ (fun a => in_zr a (frame_rng lyc (0, fpos)) \/ in_zr a (shadow_addr (frame_addr lyc 0 fpos), fs_frame_bytes 0 / 8))
HK HSP UN ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact Ha) ltac:(lia)
ltac:(let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; revert Ha; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
change (fs_frame_bytes 0 / 8) with 8; change (fs_frame_bytes 0) with 64; fold Fv; unfold SB; lia)
HB HFf) as K2;
clear HK UN; rename K2 into HK;
rfb_RA HK HJn RAs RAd;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end
end end
with rfb_RA HK HJn RAs RAd :=
let L := rnLAWSrf in
lazymatch type of HK with rfc_kept ?W ?memc ?W3 ?mnew ?spz ?Bb ?lyc ?Sc ?st ?dst =>
lazymatch goal with
| Hfin : In (?cid, ?pos) (frames Sc), HARc : AR trbsegs _ lyc Sc W memc _, RAdst0 : range_addressable (aview trbsegs (w_H W) memc) SHADOW_OFF dst 24 |- _ =>
let RAd2 := fresh "HRAdst" in let RAs2 := fresh "HRAst" in let Q := fresh "Q" in let Elo := fresh "Elo" in let Ehi := fresh "Ehi" in
pose proof (RA_dst_kept _ _ _ _ _ _ _ _ _ _ cid pos HK Hfin ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
(proj1 (proj2 (al_frames _ _ L _ _ _ _ _ cid pos HARc Hfin))) ltac:(lia) ltac:(lia) RAdst0) as RAd2;
pose proof (proj1 (proj2 HJn)) as Q; destruct Q as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _);
lazymatch type of HJn with ajournal _ ?Bv _ _ _ _ _ _ _ _ _ ?lyn ?Sn _ _ ?mdn _ =>
assert (RAs2 : range_addressable (aview trbsegs (w_H W3) mnew) SHADOW_OFF st 24)
by (apply (RA_stack Bv L lyn Sn W3 mnew mdn st 24 (proj1 HJn)); [rewrite Elo; lia | rewrite Ehi; lia | assumption | reflexivity | clear; lia]) end;
clear Elo Ehi; try clear RAs; try clear RAd; rename RAs2 into RAs; rename RAd2 into RAd
end end.
Ltac rf_chunk_e cs od :=
lazymatch eval cbv in (find (fun c => Z.eqb (YQ0b.c_off c) od) cs) with
| Some (YQ0b.mkChunk _ (CVal _ ?e)) => e
end.
Ltac idx_of_baseLo rs n lo :=
lazymatch rs with
| YQ0b.mkRegion (Some n) lo _ _ _ _ :: _ => constr:(0%nat)
| _ :: ?tl => let i := idx_of_baseLo tl n lo in constr:(S i)
end.
Ltac rf_obj_atB HS B11 v0 tac0 v8 tac8 HP OBJ :=
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict ?Hx ?msX) =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseA rs 11%nat in
let r := eval vm_compute in (nth i rs got_region) in
let HRd := fresh "HRd" in
pose proof (st_ok_region_nth Ex ssx (restrict Hx msX) i r HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
lazymatch type of HRd with region_ok _ _ _ (YQ0b.mkRegion (Some 11%nat) ?lo ?hi ?wlo ?whi ?cs) =>
let e0 := rf_chunk_e cs 0 in let e8 := rf_chunk_e cs 8 in
pose proof (rf_obj_of_regionB Ex _ _ _ cs lo hi wlo whi e0 e8 v0 v8 HRd B11 ltac:(cbn; tauto) ltac:(cbn; tauto)
ltac:(tac0) ltac:(lia) ltac:(tac8) ltac:(lia) HP) as OBJ end;
clear HRd end.
Ltac rf_stream_words2 HS B10 E33 E34 Vp Vn :=
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseLo rs 10%nat 0 in let i := eval vm_compute in i in
lazymatch type of B10 with _ = ?st =>
lazymatch type of E33 with _ = Z_to_bv 64 ?pd => lazymatch type of E34 with _ = Z_to_bv 64 ?nbv =>
field_atD HS i 10%nat st B10 0 8%N (SOff 33 0) pd ltac:(rewrite sv_denot_SOff0; exact E33) Vp;
field_atD HS i 10%nat st B10 8 8%N (SOff 34 0) nbv ltac:(rewrite sv_denot_SOff0; exact E34) Vn end end end end.
Ltac rf_stream_cur HS B10 c Ec Vc :=
lazymatch type of HS with st_ok _ ?Ex ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseLo rs 10%nat 16 in let i := eval vm_compute in i in
lazymatch type of B10 with _ = ?st =>
lazymatch type of Ec with _ = Z_to_bv 64 ?cu =>
field_atD HS i 10%nat st B10 16 8%N (SOff c 0) cu ltac:(rewrite sv_denot_SOff0; exact Ec) Vc end end end.
Fixpoint rfb_drop_nth_f (rs : smem) (i : nat) : smem :=
match rs, i with
| [], _ => []
| _ :: t, O => t
| r :: t, S i' => r :: rfb_drop_nth_f t i'
end.
Ltac rfb_drop_nth HS i :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let rs' := eval vm_compute in (rfb_drop_nth_f rs i) in
let HS3 := fresh "HS3" in
pose proof (st_ok_submem trbsegs Ex ssx msx rs' HS ltac:(cbn [ss_mem]; rfj_submem_to) ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac rfb_drop_cur HS :=
lazymatch type of HS with st_ok _ _ ?ssx _ =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_baseLo rs 10%nat 16 in let i := eval vm_compute in i in
rfb_drop_nth HS i end.
Ltac rfb_add_atom HS n w En :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trbsegs n Ev ssv msv [w] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (En : ew (havoc Ev n [w]) n = w) by (exact (ew_havoc_new _ n [w] 0 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
Ltac rfb_old_atom Ec := rewrite sv_denot_SOff0, ew_havoc_old by (cbn; lia); symmetry; exact Ec.
Ltac rfb_epi_arrive HS curv imgv fmtv tcur timg tfmt E390 E391 E392 :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (st_ok_havoc_win trbsegs 390 Ev ssv msv [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv] HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (E390 : ew (havoc Ev 390 [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv]) 390 = Z_to_bv 64 curv) by (exact (ew_havoc_new _ 390 [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E391 : ew (havoc Ev 390 [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv]) 391 = Z_to_bv 64 imgv) by (exact (ew_havoc_new _ 390 [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E392 : ew (havoc Ev 390 [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv]) 392 = Z_to_bv 64 fmtv) by (exact (ew_havoc_new _ 390 [Z_to_bv 64 curv; Z_to_bv 64 imgv; Z_to_bv 64 fmtv] 2 (Z_to_bv 64 0) ltac:(cbn; lia))) end;
rechunk_off HS 10%nat 16 (SOff 390 0) ltac:(rewrite sv_denot_SOff0, E390; tcur);
rechunk_off HS 11%nat 0 (SOff 391 0) ltac:(rewrite sv_denot_SOff0, E391; timg);
rechunk_off HS 11%nat 8 (SOff 392 0) ltac:(rewrite sv_denot_SOff0, E392; tfmt).
