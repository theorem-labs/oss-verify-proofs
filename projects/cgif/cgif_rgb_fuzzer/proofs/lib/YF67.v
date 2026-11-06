(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0h YG10 YG0u YG0d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YE0v YF63.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF0k YF6d.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Definition R_HDR : YQ0b.region := YQ0b.mkRegion (Some 9%nat) (-16) (-8) 0 0
[YQ0b.mkChunk (-16) (CVal 1 (SLit 2)); YQ0b.mkChunk (-15) (CVal 1 (SOff 32 0)); YQ0b.mkChunk (-14) (CVal 2 (SLit 0)); YQ0b.mkChunk (-12) (CVal 4 (SOff 33 0))].
Definition F_C1 : facts := mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 0); (33%nat, mkAF 0 (2 ^ 32 - 1) 0)] [] [].
Definition SM1 {imgk : img} : sstate := mkSS (0x323bc + D_150) sr_atoms [R_HDR; flit8 (0xa2188 + D_10f0) (0xa3ff8 + D_10f0); flit8 (0xa3ff8 + D_10f0) (0x9b490 + D_10ec)] None F_C1.
Definition SM2 {imgk : img} : sstate := mkSS (0x32434 + D_150) sr_atoms [] None (mkFacts [] [] []).
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section C1. Context {imgk : img}.
Variable W : world tfxsegs.
Variable md : Model.
Let H := w_H W.
Definition c1_post (regs1 : bvmap 5 word) (mem1 : word -> option byte) (p q len : Z) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD mat,
c' = mkCfg (mkst regsD (w64 (0x3244c + D_150)) memD (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regsD 1 = w64 (0x32434 + D_150) /\ getr regsD 10 = getr regs1 18 /\ getr regsD 11 = getr regs1 9 /\ getr regsD 12 = w64 0 /\ getr regsD 13 = w64 0 /\
getr regsD 14 = getr regs1 8 /\ getr regsD 15 = w64 1 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv -> getr regsD r = getr regs1 r) /\
(forall x : word, ~ (q <= bv_unsigned x < q + len) -> memD x = mem1 x) /\
(forall i, 0 <= i < len -> aview tfxsegs H memD (q + i) = aview tfxsegs H mem1 (p + i)) /\
(forall a, apresent H mem1 a -> apresent H memD a).
Lemma c1_tail : forall (regs1 : bvmap 5 word) (mem1 : word -> option byte) (mat1 : list word) (p q len : Z),
getr regs1 10 = w64 q -> getr regs1 11 = w64 p -> getr regs1 12 = w64 len -> getr regs1 1 = w64 (0x32434 + D_150) ->
0 <= len < 2 ^ 32 -> 0 <= q -> q + len <= 2 ^ 63 -> 0 <= p -> p + len <= 2 ^ 63 -> (q + len <= p \/ p + len <= q) ->
(forall a, p <= a < p + len -> apresent H mem1 a) -> (forall a, q <= a < q + len -> apresent H mem1 a) ->
SRr tfxsegs W (mkCfg (mkst regs1 (w64 (0x9b490 + D_10ec)) mem1 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat1 md)) (c1_post regs1 mem1 p q len).
Proof.
intros regs1 mem1 mat1 p q len G10 G11 G12 G1 Hlen Hq0 Hq1 Hp0 Hp1 HDISJ HSRC HDST.
pose proof YF8r.Hwx_tfa as Hwx.
assert (DW : forall a, q <= a < q + len -> writable_at tfxsegs (mrestrict H mem1) a /\ H (Z_to_bv 64 a) = false).
{ intros a Ha. split; [img_try (img_exact (YE0v.apresent_writable H mem1 a (HDST a Ha))) | img_try (img_exact (proj1 (HDST a Ha)))]. }
destruct (rdn_of_vis (mrestrict H mem1) p (Z.to_nat len) ltac:(img_lia) ltac:(img_lia)) as (bs & RDN & LEN & BS).
{ intros i Hi. destruct (HSRC (p + i) ltac:(img_lia)) as [Hh [b Hb]]. unfold mbyte, mrestrict. fold H. rewrite Hh, Hb. discriminate. }
assert (SOK : store_ok tfxsegs (mrestrict H mem1) (w64 q) (length bs) = true).
{ rewrite LEN. img_apply store_ok_of_all; unfold w64; rewrite unsigned_lit_small by img_lia; [img_lia|].
intros z Hz. pose proof (proj1 (DW (bv_unsigned z) ltac:(img_lia))) as Wz. unfold writable_at in Wz. rewrite Z_to_bv_bv_unsigned in Wz. img_exact Wz. }
destruct (tfx_memcpy bs (w64 q) (w64 p) (w64 len) (mrestrict H mem1) (seg_rom tfxsegs) regs1 G10 G11 G12
ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)) ltac:(img_try (rewrite LEN; img_exact RDN)) SOK
ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia)) ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia))
ltac:(img_try (unfold w64; rewrite !unsigned_lit_small by img_lia; img_lia)))
as (regs2 & Hms & A10 & Hkeep).
rewrite G1 in Hms. replace (v_jalr (w64 (0x32434 + D_150)) 0) with (Z_to_bv 64 (0x32434 + D_150) : word) in Hms by (img_try (img_apply bv_eq; (img_case; vm_compute); img_refl)).
img_change (Z_to_bv 64 tfx_A_musl_memcpy) with (w64 (0x9b490 + D_10ec)) in Hms.
set (m1r := mrestrict H mem1) in *. set (m2r := wbytes m1r (w64 q) bs) in Hms.
set (mem2 := munrestrict H mem1 m2r).
assert (LENZ : Z.of_nat (length bs) = len) by img_lia.
assert (M2out : forall z : word, ~ (q <= bv_unsigned z < q + len) -> mem2 z = mem1 z).
{ intros z Hz. (subst mem2 m2r; cbv beta). unfold munrestrict. destruct (H z) eqn:Hh; [img_refl|].
assert (Ew : wbytes m1r (w64 q) bs z = m1r z).
{ destruct (Z_lt_le_dec (bv_unsigned z) q) as [L|L].
- img_apply wbytes_below; unfold w64; rewrite ?LENZ, unsigned_lit_small by img_lia; img_lia.
- img_apply wbytes_above. unfold w64. rewrite LENZ, unsigned_lit_small by img_lia. img_lia. }
rewrite Ew. (subst m1r; cbv beta). unfold mrestrict. rewrite Hh. img_refl. }
assert (M2in : forall i, 0 <= i < len -> mem2 (Z_to_bv 64 (q + i)) = Some (nth (Z.to_nat i) bs 0%bv)).
{ intros i Hi. (subst mem2; cbv beta). unfold munrestrict. rewrite (proj2 (DW (q + i) ltac:(img_lia))).
(subst m2r; cbv beta). rewrite (YE0v.wbytes_inside bs m1r (w64 q) (Z_to_bv 64 (q + i)));
unfold w64; rewrite ?LENZ, ?unsigned_lit_small by img_lia; [|img_lia|img_lia].
replace (Z.to_nat (q + i - q)) with (Z.to_nat i) by img_lia. img_apply nth_error_nth'. img_lia. }
eapply (SRr_msteps tfxsegs Hwx W); [img_try (rewrite restrict_mkst_fx; img_exact Hms)|].
intros model' Hsbm _. rewrite (same_but_materialized_wvb _ model' Hsbm). cbn [ms_mem mkst].
img_change (unrestrict (w_H W) mem1 (mkst regs2 (Z_to_bv 64 (0x32434 + D_150)) m2r (seg_rom tfxsegs))) with (mkst regs2 (Z_to_bv 64 (0x32434 + D_150)) mem2 (seg_rom tfxsegs)).
rewrite ?wvb_wvb.
assert (HS : st_ok tfxsegs (Ereg regs2 []) SM2 (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (0x32434 + D_150)) mem2 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold SM2. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_Ereg.
- img_refl.
- constructor.
- img_exact I.
- split; [img_try (img_exact I) | img_try (split; img_exact I)]. }
srr_run_to_sh tfxtbl_rrF_ok HS (0x3244c + D_150).
assert (MEQ : forall x, ms_mem ms x = mem2 x).
{ intros x. img_apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & _). destruct Hin. }
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) _ _ _ HS eq_refl) as Hsh; cbn [ss_pc] in Hsh.
img_apply SRr_ret. split; [img_refl|]. exists (ms_regs ms), (ms_mem ms), mat.
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew (Ereg regs2 []) i = getr regs2 rr) by (img_try (intros ii rr Hnth; img_exact (ew_Ereg_nat regs2 _ ii rr Hnth))).
assert (KEEP : forall r : bv 5, r <> 5%bv -> r <> 6%bv -> r <> 7%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> r <> 28%bv ->
getr regs2 r = getr regs1 r) by (img_try (intros r; img_apply Hkeep)).
split. { rewrite Hsh at 1. img_refl. }
rreg HS (1%bv : bv 5) Q1. rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11. rreg HS (12%bv : bv 5) Q12. rreg HS (13%bv : bv 5) Q13.
rreg HS (14%bv : bv 5) Q14. rreg HS (15%bv : bv 5) Q15.
split. { rewrite Q1, (Y 1%nat 1%bv eq_refl), KEEP by (img_try (intros X; discriminate X)). img_exact G1. }
split. { rewrite Q10, (Y 18%nat 18%bv eq_refl). img_apply KEEP; intros X; discriminate X. }
split. { rewrite Q11, (Y 9%nat 9%bv eq_refl). img_apply KEEP; intros X; discriminate X. }
split; [img_try (img_exact Q12)|]. split; [img_try (img_exact Q13)|].
split. { rewrite Q14, (Y 8%nat 8%bv eq_refl). img_apply KEEP; intros X; discriminate X. }
split; [img_try (img_exact Q15)|].
split.
{ intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ let R := fresh "R" in lazymatch goal with |- getr _ ?rr = _ => rreg HS (rr : bv 5) R; rewrite R; let k := img_ev (Z.to_nat (bv_unsigned rr)) in rewrite (Y k rr eq_refl); img_apply KEEP; intros X; discriminate X end |]).
destruct Hr. }
split. { intros x Hx. rewrite MEQ. img_exact (M2out x Hx). }
split.
{ intros i Hi. assert (AV3 : aview tfxsegs H (ms_mem ms) (q + i) = aview tfxsegs H mem2 (q + i)) by (img_try (img_apply aview_same; img_apply MEQ)). rewrite AV3.
unfold aview. replace (mbyte tfxsegs (mrestrict H mem2) (q + i)) with (Some (nth (Z.to_nat i) bs 0%bv)).
2:{ unfold mbyte, mrestrict. rewrite (proj2 (DW (q + i) ltac:(img_lia))), (M2in i Hi). img_refl. }
fold m1r. replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by img_lia. rewrite (BS (Z.to_nat i) ltac:(img_lia)). img_refl. }
intros a Hp. img_apply (apresent_same H mem2 (ms_mem ms) a (MEQ _)).
destruct Hp as [Hh [b Hb]]. split; [img_try (img_exact Hh)|].
set (x := Z_to_bv 64 a) in *. destruct (Z_lt_le_dec (bv_unsigned x) q) as [L|L]; [|img_try (destruct (Z_lt_le_dec (bv_unsigned x) (q + len)) as [L2|L2])].
- exists b. rewrite (M2out x ltac:(img_lia)). img_exact Hb.
- exists (nth (Z.to_nat (bv_unsigned x - q)) bs 0%bv). rewrite <- (M2in (bv_unsigned x - q) ltac:(img_lia)). f_equal.
replace (q + (bv_unsigned x - q)) with (bv_unsigned x) by img_lia. symmetry. img_apply Z_to_bv_bv_unsigned.
- exists b. rewrite (M2out x ltac:(img_lia)). img_exact Hb.
Qed.
Definition c1_postM (regsM : bvmap 5 word) (memM : word -> option byte) (p q len : Z) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regsD memD mat,
c' = mkCfg (mkst regsD (w64 (0x3244c + D_150)) memD (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regsD 1 = w64 (0x32434 + D_150) /\ getr regsD 10 = getr regsM 18 /\ getr regsD 11 = w64 p /\ getr regsD 12 = w64 0 /\ getr regsD 13 = w64 0 /\
getr regsD 14 = getr regsM 8 /\ getr regsD 15 = w64 1 /\ getr regsD 19 = w64 len /\ getr regsD 20 = w64 q /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv -> getr regsD r = getr regsM r) /\
(forall x : word, ~ (q <= bv_unsigned x < q + len) -> memD x = memM x) /\
(forall i, 0 <= i < len -> aview tfxsegs H memD (q + i) = aview tfxsegs H memM (p + i)) /\
(forall a, apresent H memM a -> apresent H memD a).
Lemma c1_conv : forall (regsM regs1 : bvmap 5 word) (memM mem1 : word -> option byte) (p q len : Z) W' c',
(forall x, mem1 x = memM x) ->
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv -> getr regs1 r = getr regsM r) ->
getr regs1 9 = w64 p -> getr regs1 19 = w64 len -> getr regs1 20 = w64 q ->
c1_post regs1 mem1 p q len W' c' -> c1_postM regsM memM p q len W' c'.
Proof.
intros regsM regs1 memM mem1 p q len W' c' HM HR H9 H19 H20 (-> & regsD & memD & mat & -> & D1 & D10 & D11 & D12 & D13 & D14 & D15 & DK & DM & DC & DP).
split; [img_refl|]. exists regsD, memD, mat. split; [img_refl|]. split; [img_try (img_exact D1)|].
split; [img_try (rewrite D10; img_apply HR; cbn [In]; tauto)|]. split; [img_try (rewrite D11; img_exact H9)|]. split; [img_try (img_exact D12)|]. split; [img_try (img_exact D13)|].
split; [img_try (rewrite D14; img_apply HR; cbn [In]; tauto)|]. split; [img_try (img_exact D15)|].
split; [img_try (rewrite (DK 19%bv ltac:(cbn [In]; tauto)); img_exact H19)|]. split; [img_try (rewrite (DK 20%bv ltac:(cbn [In]; tauto)); img_exact H20)|].
split. { intros r Hr. rewrite (DK r); [img_try (img_exact (HR r Hr))|]. cbn [In] in Hr |- *. tauto. }
split; [img_try (intros x Hx; rewrite (DM x Hx); img_apply HM)|].
split. { intros i Hi. rewrite (DC i Hi). img_apply aview_same. img_apply HM. }
intros a Ha. img_apply DP. img_apply (apresent_same H memM mem1 a (HM _)). img_exact Ha.
Qed.
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. img_apply bv_eq. rewrite Z_to_bv_unsigned. img_change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. img_change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. img_apply Z.mod_small. img_exact Hv.
Qed.
Lemma c1_copy : forall (regsM : bvmap 5 word) (memM : word -> option byte) (p q n nold hb1 : Z),
getr regsM 9 = w64 p -> getr regsM 10 = w64 q -> getr regsM 19 = w64 n ->
16 <= p -> (p <= TFX_IMG_LO \/ TFX_IMG_END + 16 <= p) -> 4096 <= q <= 2 ^ 47 -> 0 <= n < 2 ^ 32 -> 0 <= nold < 2 ^ 32 -> 0 <= hb1 < 256 ->
p + Z.min n nold <= 2 ^ 63 -> (q + Z.min n nold <= p \/ p + Z.min n nold <= q) ->
val_mem tfxsegs (mrestrict H memM) (p - 16) 1 2 -> val_mem tfxsegs (mrestrict H memM) (p - 15) 1 hb1 ->
val_mem tfxsegs (mrestrict H memM) (p - 14) 2 0 -> val_mem tfxsegs (mrestrict H memM) (p - 12) 4 nold ->
val_mem tfxsegs (mrestrict H memM) (0xa2188 + D_10f0) 8 (0xa3ff8 + D_10f0) -> val_mem tfxsegs (mrestrict H memM) (0xa3ff8 + D_10f0) 8 (0x9b490 + D_10ec) ->
(forall a, p <= a < p + Z.min n nold -> apresent H memM a) -> (forall a, q <= a < q + Z.min n nold -> apresent H memM a) ->
SRr tfxsegs W (mkCfg (mkst regsM (w64 (0x323bc + D_150)) memM (seg_rom tfxsegs)) md) (c1_postM regsM memM p q (Z.min n nold)).
Proof.
intros regsM memM p q n nold hb1 G9 G10 G19 Hp16 HPI Hq Hn Hnold Hhb Hpl HDISJ V0 V1 V2 V4 VC1 VC2 HSRC HDST.
pose proof YF8r.Hwx_tfa as Hwx.
set (E1 := Ereg regsM [w64 hb1; w64 nold]).
assert (E9 : bv_unsigned (ew E1 9) = p) by (img_try ((subst E1; cbv beta); rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl), G9; unfold w64; img_apply unsigned_lit_small; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)).
assert (HS : st_ok tfxsegs E1 SM1 (restrict (w_H W) (mkst regsM (w64 (0x323bc + D_150)) memM (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold SM1, w64. img_apply (entry_st_ok_full tfxsegs).
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]])].
+ unfold region_ok, R_HDR. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. fold E1. rewrite E9.
split; [img_lia|]. split; [img_try (unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)|]. split; [img_try (intros o Ho; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
* eapply (chunk_ok_val tfxsegs _ _ _ (-16) 1 (SLit 2) 2); [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (eapply val_mem_addr; [img_exact V0 | img_lia])].
* eapply (chunk_ok_val tfxsegs _ _ _ (-15) 1 (SOff 32%nat 0) hb1); [img_try (cbn [sv_denot]; (subst E1; cbv beta); rewrite (ew_Ereg_extra regsM _ 0); cbn [nth]; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia) | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (eapply val_mem_addr; [img_exact V1 | img_lia])].
* eapply (chunk_ok_val tfxsegs _ _ _ (-14) 2 (SLit 0) 0); [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (eapply val_mem_addr; [img_exact V2 | img_lia])].
* eapply (chunk_ok_val tfxsegs _ _ _ (-12) 4 (SOff 33%nat 0) nold); [img_try (cbn [sv_denot]; (subst E1; cbv beta); rewrite (ew_Ereg_extra regsM _ 1); cbn [nth]; unfold w64; rewrite Zbv_add_unsigned; f_equal; img_lia) | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (eapply val_mem_addr; [img_exact V4 | img_lia])].
+ unfold region_ok, flit8. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs _ _ _ (0xa2188 + D_10f0) 8 (SLit (0xa3ff8 + D_10f0)) (0xa3ff8 + D_10f0)); [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_exact VC1)].
+ unfold region_ok, flit8. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; img_lia)|]. img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
eapply (chunk_ok_val tfxsegs _ _ _ (0xa3ff8 + D_10f0) 8 (SLit (0x9b490 + D_10ec)) (0x9b490 + D_10ec)); [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (img_exact VC2)].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, R_HDR, flit8. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. fold E1. rewrite !E9.
unfold TFX_IMG_LO, TFX_IMG_END in *. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms F_C1 atoms_ok]. split; [|img_try (split; [|img_exact I])]; unfold afact_ok; cbn [af_lo af_hi af_al2]; (subst E1; cbv beta).
+ rewrite (ew_Ereg_nat regsM _ 10 10%bv eq_refl), G10. unfold w64. rewrite unsigned_lit_small by img_lia. split; [img_lia|]. split; [img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia].
+ rewrite (ew_Ereg_extra regsM _ 1). cbn [nth]. unfold w64. rewrite unsigned_lit_small by img_lia. split; [img_lia|]. split; [img_try (img_change (2 ^ 0) with 1; img_apply Z.mod_1_r) | img_lia]. }
change (w64 (0x323bc + D_150)) with (Z_to_bv 64 (0x323bc + D_150)) in HS |- *.
assert (NOWR : forall (ma mb : word -> option byte), frame_of E1 (ss_mem SM1) ma mb -> forall x, mb x = ma x).
{ intros ma mb HFx x. img_apply HFx. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg). vm_compute in Hin.
repeat (destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <-; cbn [fst snd] in Hrg; img_lia)|]). destruct Hin. }
srr_run_sh tfxtbl_rrF_ok HS.
pose proof (NOWR _ _ HF) as MEQ1. clear HF HFr.
assert (R19 : rho_of E1 19%nat = n) by (img_try (unfold rho_of; (subst E1; cbv beta); rewrite (ew_Ereg_nat regsM _ 19 19%bv eq_refl), G19; unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (R33 : rho_of E1 33%nat = nold) by (img_try (unfold rho_of; (subst E1; cbv beta); rewrite (ew_Ereg_extra regsM _ 1); cbn [nth]; unfold w64; img_apply unsigned_lit_small; img_lia)).
srr_branch_sh tfxtbl_rrF_ok HS.
-
assert (LT : n < nold).
{ rewrite branch_ltu_U in Hc. apply Z.ltb_lt in Hc. revert Hc. rewrite !U_zev by img_refl. cbn [zev zalu_raw]. rewrite R19, R33.
rewrite !Z.add_0_r. img_change (zcanon 0) with 0. img_change (Z.of_N 32) with 32. rewrite ?(zcanon_id nold) by (img_try (unfold M64; img_lia)). rewrite ?(Z.mod_small nold) by img_lia.
rewrite Z.lor_0_l. rewrite ?(zcanon_id nold), ?(zcanon_id n) by (img_try (unfold M64; img_lia)). img_lia. }
srr_run_to_sh tfxtbl_rrF_ok HS (0x9b490 + D_10ec).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ2 : forall x, ms_mem msA x = memM x) by (img_try (intros x; rewrite (NOWR _ _ HF x); img_apply MEQ1)). clear HF HFr.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) _ _ _ HS eq_refl) as Hsh; cbn [ss_pc] in Hsh. rewrite Hsh.
rewrite (Z.min_l n nold) in * by img_lia.
eapply SRr_mono.
{ img_apply (c1_tail (ms_regs msA) (ms_mem msA) _ p q n).
- rreg HS (10%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 10 10%bv eq_refl). img_exact G10.
- rreg HS (11%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl). img_exact G9.
- rreg HS (12%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 19 19%bv eq_refl). img_exact G19.
- rreg HS (1%bv : bv 5) R. img_exact R.
- img_lia. - img_lia. - img_lia. - img_lia. - img_lia. - img_exact HDISJ.
- intros a Ha. img_apply (apresent_same H memM (ms_mem msA) a (MEQ2 _)). img_exact (HSRC a Ha).
- intros a Ha. img_apply (apresent_same H memM (ms_mem msA) a (MEQ2 _)). img_exact (HDST a Ha). }
intros W' c' _ POST. img_apply (c1_conv regsM (ms_regs msA) memM (ms_mem msA) p q n W' c' MEQ2); [| | | | img_try (img_exact POST)].
+ intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ let R := fresh "R" in lazymatch goal with |- getr _ ?rr = _ => rreg HS (rr : bv 5) R; rewrite R; let k := img_ev (Z.to_nat (bv_unsigned rr)) in img_exact (ew_Ereg_nat regsM _ k rr eq_refl) end |]).
destruct Hr.
+ rreg HS (9%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl). img_exact G9.
+ rreg HS (19%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 19 19%bv eq_refl). img_exact G19.
+ rreg HS (20%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 10 10%bv eq_refl). img_exact G10.
-
assert (GE : nold <= n).
{ rewrite branch_ltu_U in Hc. apply Z.ltb_ge in Hc. revert Hc. rewrite !U_zev by img_refl. cbn [zev zalu_raw]. rewrite R19, R33.
rewrite !Z.add_0_r. img_change (zcanon 0) with 0. img_change (Z.of_N 32) with 32. rewrite ?(zcanon_id nold) by (img_try (unfold M64; img_lia)). rewrite ?(Z.mod_small nold) by img_lia.
rewrite Z.lor_0_l. rewrite ?(zcanon_id nold), ?(zcanon_id n) by (img_try (unfold M64; img_lia)). img_lia. }
srr_run_to_sh tfxtbl_rrF_ok HS (0x9b490 + D_10ec).
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msA end.
assert (MEQ2 : forall x, ms_mem msA x = memM x) by (img_try (intros x; rewrite (NOWR _ _ HF x); img_apply MEQ1)). clear HF HFr.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) _ _ _ HS eq_refl) as Hsh; cbn [ss_pc] in Hsh. rewrite Hsh.
rewrite (Z.min_r n nold) in * by img_lia.
assert (DN : forall t, svpure t = true -> zev (rho_of E1) t = nold -> sv_denot E1 t = w64 nold) by (img_try (intros t Ht Hz; img_apply denot_by_zev; [img_try (img_exact Ht) | img_lia | img_try (img_exact Hz)])).
assert (ZN : zev (rho_of E1) (SAlu ALU_OR (SLit 0) (SOff 33 0)) = nold).
{ cbn [zev zalu_raw]. rewrite R33, Z.add_0_r. img_change (zcanon 0) with 0. rewrite ?(zcanon_id nold) by (img_try (unfold M64; img_lia)). rewrite Z.lor_0_l. rewrite ?(zcanon_id nold) by (img_try (unfold M64; img_lia)). img_refl. }
eapply SRr_mono.
{ img_apply (c1_tail (ms_regs msA) (ms_mem msA) _ p q nold).
- rreg HS (10%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 10 10%bv eq_refl). img_exact G10.
- rreg HS (11%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl). img_exact G9.
- rewrite (st_ok_reg_denot (w_H W) E1 _ msA 12%bv HS). lazymatch goal with |- context [sr_get ?sr ?r] => let e := img_ev (sr_get sr r) in img_change (sr_get sr r) with e end.
img_apply DN; [img_refl|]. cbn [zev zalu_raw]. rewrite R33. img_change (zcanon 0) with 0. rewrite !Z.add_0_r.
rewrite ?(zcanon_id nold) by (img_try (unfold M64; img_lia)). rewrite Z.lor_0_l. rewrite !(zcanon_id nold) by (img_try (unfold M64; img_lia)). img_refl.
- rreg HS (1%bv : bv 5) R. img_exact R.
- img_lia. - img_lia. - img_lia. - img_lia. - img_lia. - img_exact HDISJ.
- intros a Ha. img_apply (apresent_same H memM (ms_mem msA) a (MEQ2 _)). img_exact (HSRC a Ha).
- intros a Ha. img_apply (apresent_same H memM (ms_mem msA) a (MEQ2 _)). img_exact (HDST a Ha). }
intros W' c' _ POST. img_apply (c1_conv regsM (ms_regs msA) memM (ms_mem msA) p q nold W' c' MEQ2); [| | | | img_try (img_exact POST)].
+ intros r Hr. cbn [In] in Hr.
repeat (destruct Hr as [<-|Hr]; [ let R := fresh "R" in lazymatch goal with |- getr _ ?rr = _ => rreg HS (rr : bv 5) R; rewrite R; let k := img_ev (Z.to_nat (bv_unsigned rr)) in img_exact (ew_Ereg_nat regsM _ k rr eq_refl) end |]).
destruct Hr.
+ rreg HS (9%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 9 9%bv eq_refl). img_exact G9.
+ rewrite (st_ok_reg_denot (w_H W) E1 _ msA 19%bv HS). lazymatch goal with |- context [sr_get ?sr ?r] => let e := img_ev (sr_get sr r) in img_change (sr_get sr r) with e end.
img_apply DN; [img_refl|]. cbn [zev zalu_raw]. rewrite R33. img_change (zcanon 0) with 0. rewrite !Z.add_0_r.
rewrite ?(zcanon_id nold) by (img_try (unfold M64; img_lia)). rewrite Z.lor_0_l. rewrite !(zcanon_id nold) by (img_try (unfold M64; img_lia)). img_refl.
+ rreg HS (20%bv : bv 5) R. rewrite R. (subst E1; cbv beta). rewrite (ew_Ereg_nat regsM _ 10 10%bv eq_refl). img_exact G10.
Qed.
End C1.
End c.
