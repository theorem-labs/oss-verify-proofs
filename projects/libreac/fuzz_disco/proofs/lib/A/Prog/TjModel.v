(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths, module names and numbers changed; 1071 of its 1108 lines of code are new or changed and 293 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow PaStep DiscoSyms DiscoList DiscoAddr DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import TjSpec TjBase DiscoRo TjCuts TjEntry TjLoopCuts TjSnSh.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnShared PfFacts SnprintfDef SnprintfDefR.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_json_text.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require tj_lemmas.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import SnprintfConsts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import AmemBlock8.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma tjm_sub : forall c l z, zcanon z = 2 ^ 64 - 1 -> 0 <= l <= c -> c < 2 ^ 63 -> zcanon (c + zcanon (l * zcanon z)) = c - l.
Proof.
intros c l z Hz Hl Hc. rewrite Hz. unfold zcanon, M64.
destruct (Z.eq_dec l 0) as [->|Hl0].
{ rewrite Z.mul_0_l, Zmod_0_l, Z.add_0_r, Z.sub_0_r. apply Z.mod_small. lia. }
replace (l * (2 ^ 64 - 1)) with ((2 ^ 64 - l) + (l - 1) * 2 ^ 64) by ring.
rewrite Z_mod_plus_full, (Z.mod_small (2 ^ 64 - l)) by lia.
replace (c + (2 ^ 64 - l)) with ((c - l) + 1 * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma tjm_dec : forall v, 0 <= v < 256 -> disco_json_text.dec v = pf_dec v.
Proof.
intros v Hv.
assert (A : forallb (fun k => if list_eq_dec Z.eq_dec (disco_json_text.dec (Z.of_nat k)) (pf_dec (Z.of_nat k)) then true else false)
(seq 0 256) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. specialize (A (Z.to_nat v) ltac:(apply in_seq; lia)).
rewrite Z2Nat.id in A by lia. destruct (list_eq_dec Z.eq_dec (disco_json_text.dec v) (pf_dec v)); [assumption | discriminate].
Qed.
Lemma tjm_tok : forall e tok x, model_of reac_disco_table_json_c.box_tok e = (tok, x) ->
(length tok <= 11)%nat /\ Forall (fun c => 0 < c < 256) tok.
Proof.
intros e tok x H. unfold model_of in H.
destruct (e_has_decl e =? 0).
{ injection H as <- _. split; [cbn; lia|]. repeat constructor; lia. }
destruct (reac_disco_table_json_c.box_tok (e_family e) (e_decl_in e) (e_decl_out e)) as [t|] eqn:Eb.
- injection H as <- _. unfold reac_disco_table_json_c.box_tok in Eb.
destruct (Z.eqb_spec (disco_box_name_model.bn_ret (e_family e) [] (e_decl_in e) (e_decl_out e)) 0) as [Hr|Hr]; [|discriminate].
injection Eb as <-.
destruct (tj_lemmas.tj_box_ok _ _ _ Hr) as (Ea & Eb & Ez).
destruct (disco_box_name_model.bn_c17 (e_family e) (e_decl_in e) (e_decl_out e) Ea Eb Ez) as (_ & _ & LTK & _ & CTK).
cbv zeta in LTK, CTK. split; [exact LTK | exact (tj_lemmas.tok_rng _ CTK)].
- injection H as <- _. split; [cbn; lia|]. repeat constructor; lia.
Qed.
Lemma tjm_ra_kept : forall (rd rd' : Z -> option Z) p n,
(forall x, p <= x < p + n -> rd' (SHADOW_OFF + x / 8) = rd (SHADOW_OFF + x / 8)) ->
range_addressable rd SHADOW_OFF p n -> range_addressable rd' SHADOW_OFF p n.
Proof.
intros rd rd' p n Hk H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. unfold shadow_of_addr in *.
rewrite (Hk x Hx). split; assumption.
Qed.
Lemma tjm_hull_kept : forall (rd rd' : Z -> option Z) x n,
(forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Hk H s Hs. rewrite (Hk s Hs). exact (H s Hs). Qed.
Ltac ro_base HS n :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs n in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 0) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 0 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity)) ltac:(intros o Ho; lia))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma tjm_mod8 : forall x i, x mod 8 = 0 -> (x + 48 * i + 15) mod 8 = 7.
Proof.
intros x i H.
assert (Hq : x + 48 * i + 15 = 8 * (x / 8 + 6 * i + 1) + 7) by (pose proof (Z.div_mod x 8 ltac:(lia)); lia).
rewrite Hq, Z.add_comm, Z.mul_comm, Z.mod_add by lia. reflexivity.
Qed.
Lemma tjm_bltz : forall E a b v, U E a = v -> 0 <= v < 2 ^ 63 -> U E b = 0 ->
branch_taken BC_LT (sv_denot E a) (sv_denot E b) = false.
Proof.
intros E a b v Ha Hv Hb. cbn [branch_taken]. rewrite bv_lts_signed.
unfold U in Ha, Hb.
rewrite (signed_of_small (sv_denot E a)) by (rewrite Ha; unfold half64; lia).
rewrite (signed_of_small (sv_denot E b)) by (rewrite Hb; unfold half64; lia).
rewrite Ha, Hb. apply Z.ltb_ge. lia.
Qed.
Lemma tjm_u1_rng : forall T k, 0 <= disco_table_c.u_at T k 1 < 256.
Proof.
intros T k. unfold disco_table_c.u_at.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 1)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 1)) as H1.
assert (Hl : (length (disco_table_c.sub T k 1) <= 1)%nat) by (unfold disco_table_c.sub; rewrite length_firstn; lia).
remember (length (disco_table_c.sub T k 1)) as n eqn:En.
destruct n as [|[|n]]; [cbn in H1; lia | cbn in H1; lia | lia].
Qed.
Ltac rw516 HS E516 Hp Fv :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let rs := eval vm_compute in (ss_mem ssx) in
let i := idx_of_base rs 516%nat in let i := eval vm_compute in i in
let r := eval vm_compute in (nth i rs got_regionP) in
let HS3 := fresh "HS3" in
pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r 0 256) HS ltac:(vm_compute; reflexivity) eq_refl ltac:(vm_compute; reflexivity)
(region_ok_rewindow _ Ex _ r 0 256 (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia;
rewrite E516, unsigned_lit_small by lia;
let o := fresh "o" in let Ho := fresh "Ho" in
intros o Ho; apply (apresent_writable _); apply (proj1 (Hp (Fv + o) ltac:(lia)))))) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Ltac notw AG :=
let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
intros (rg & Hin & Hrg);
lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
destruct Hin.
Ltac fa2 tac := apply Forall_cons; [tac | apply Forall_cons; [tac | apply Forall_nil]].
Ltac tjm_kept AG Hfr Hpres2 :=
eapply region_kept_aview; [evalE AG | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply Hfr; lia | exact Hpres2].
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
Context {RO : ro_below_ofl (@pa_segs _ disco_listing PI) (@pa_relro_lo _ disco_listing PI) (@pa_relro_hi _ disco_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Variables SNPC GC GV IMGLO IMGHI : Z.
Variable CR : list (Z * Z).
Hypothesis HSNPC : pa_sigma DS___interceptor_trampoline_snprintf = SNPC.
Hypothesis ASNP : forall fq : YK11.FPState,
SnprintfDefR.asnprintf_realizesR (fx := fq) SEGS B pa_relro_lo pa_relro_hi GC GV IMGLO IMGHI disco_fmt_lo disco_fmt_hi CR SNPC.
Hypothesis tj_snp_consts : forall (W : world SEGS) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> consts_view SEGS W mem CR.
Hypothesis tj_snp_cr : Forall (fun r => IMG_LO <= fst r /\ 0 <= snd r /\ fst r + snd r <= IMG_TOP) CR.
Hypothesis tj_snp_canary : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
exists cval, rdword (aview SEGS (w_H W) mem) GC = Some GV /\ rdword (aview SEGS (w_H W) mem) GV = Some cval.
Hypothesis tj_snp_gcgv : IMG_LO <= GC /\ GC + 8 <= IMG_TOP /\ IMG_LO <= GV /\ GV + 8 <= IMG_TOP.
Hypothesis tj_snp_img : IMG_LO <= IMGLO /\ IMGHI <= IMG_TOP.
Hypothesis DRO : disco_ro_unowned B.
Hypothesis GM : globs_marked SEGS B disco_globs.
Hypothesis HV : img_shadow_vis SEGS B.
Hypothesis TJS : tj_strs.
Variables STK EV EVB : Z.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Hypothesis HSTK : TJ_FRAME + SNPRINTF_STK <= STK.
Hypothesis HEVB : 0 <= EVB.
Hypothesis HEV : 8 * EVB <= EV.
Lemma tjm_fmt : forall ly S (W : world SEGS) mem md k s rs,
AR SEGS B ly S W mem md -> arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
tj_ro_at k s -> Forall (zdisjoint (VAL (A_OBJ k), Z.of_nat (length s) + 1)) rs ->
fmt_at (aview SEGS (w_H W) mem) rs (VAL (A_OBJ k)) s.
Proof.
intros ly S W mem md k s rs HAR HROD (Hg & Hro & Hlo & Hhi & Hc & Hb) Hrs.
destruct (ro_read_ok_glob SEGS B disco_globs ly S W mem md (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k)) (Z.of_nat (length s) + 1)
GM Hg HV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra Hhull].
unfold IMG_LO, IMG_TOP in Hlo, Hhi.
unfold fmt_at. split; [lia|]. split.
- intros i Hi. rewrite (ro_bytes SEGS pa_relro_lo pa_relro_hi B _ (VAL (A_OBJ k)) (Z.of_nat (length s) + 1) (VAL (A_OBJ k) + i) HROD
(Hro (VAL (A_OBJ k) + i) ltac:(lia))
(disco_ro_unowned_at B _ _ DRO ltac:(unfold disco_ro_ranges; apply in_or_app; left; exact Hg)) ltac:(lia)).
pose proof (Hb (Z.to_nat i) ltac:(rewrite length_app; cbn [length]; lia)) as Hq.
rewrite Z2Nat.id in Hq by lia. exact Hq.
- split; [exact Hrs|]. split; [unfold amem_range, kLowMemEnd; left; lia|]. split; assumption.
Qed.
Lemma tjm_P34_unk : forall e, model_of reac_disco_table_json_c.box_tok e = (s_unknown, s_0x0) ->
P3 reac_disco_table_json_c.box_tok e = tj_f_model_unk /\ P4 reac_disco_table_json_c.box_tok e = tj_f_width_0.
Proof. intros e H. unfold P3, P4. rewrite H. split; reflexivity. Qed.
Lemma tjm_garr8_app : forall H H' (m m' : word -> option byte) p (acc T : list Z),
garr8 SEGS (mrestrict H m) p (acc ++ [0]) ->
(forall a, p <= a < p + Z.of_nat (length acc) -> aview SEGS H' m' a = aview SEGS H m a) ->
(forall i, 0 <= i < Z.of_nat (length T) -> aview SEGS H' m' (p + Z.of_nat (length acc) + i) = Some (nth (Z.to_nat i) T 0)) ->
aview SEGS H' m' (p + Z.of_nat (length acc) + Z.of_nat (length T)) = Some 0 ->
garr8 SEGS (mrestrict H' m') p (acc ++ T ++ [0]).
Proof.
intros H H' m m' p acc T HG HK HT H0 j Hj.
rewrite !length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length acc)) as [Hja|Hja].
- rewrite app_nth1 by exact Hja. destruct (HG j ltac:(rewrite length_app; cbn [length]; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by exact Hja.
split; [|exact Hr]. apply (val_mem_aview_kept_x SEGS H H' m m' (p + Z.of_nat j) 1 _); [|exact Hv].
intros x Hx. apply HK. lia.
- rewrite app_nth2 by exact Hja.
destruct (Nat.lt_ge_cases (j - length acc) (length T)) as [HjT|HjT].
+ rewrite app_nth1 by exact HjT.
pose proof (HT (Z.of_nat (j - length acc)) ltac:(lia)) as Hb. rewrite Nat2Z.id in Hb.
replace (p + Z.of_nat (length acc) + Z.of_nat (j - length acc)) with (p + Z.of_nat j) in Hb by lia.
exact (val_mem1_of_aview SEGS H' m' (p + Z.of_nat j) _ Hb).
+ rewrite app_nth2 by exact HjT. replace (j - length acc - length T)%nat with 0%nat by lia. cbn [nth].
replace (p + Z.of_nat j) with (p + Z.of_nat (length acc) + Z.of_nat (length T)) by lia.
exact (val_mem1_of_aview SEGS H' m' _ _ H0).
Qed.
Lemma tjm_garr8_u1 : forall (m : word -> option byte) (a k : Z) (T : list byte),
garr8 SEGS m a (map bv_unsigned T) -> 0 <= k -> k + 1 <= Z.of_nat (length T) ->
val_mem SEGS m (a + k) 1 (disco_table_c.u_at T k 1).
Proof.
intros m a k T HG Hk HkT j Hj.
assert (Hlt : (Z.to_nat k + j < length (map bv_unsigned T))%nat) by (rewrite length_map; lia).
pose proof (garr8_mbyte SEGS m a _ (Z.to_nat k + j) HG Hlt) as Hb.
replace (a + Z.of_nat (Z.to_nat k + j)) with (a + k + Z.of_nat j) in Hb by lia.
rewrite Hb. f_equal.
assert (Hnth : nth_error (disco_table_c.sub T k 1) j = Some (nth (Z.to_nat k + j) T (Z_to_bv 8 0))).
{ unfold disco_table_c.sub. rewrite nth_error_firstn. destruct (Nat.ltb_spec j 1); [|lia].
rewrite nth_error_skipn. apply nth_error_nth'. lia. }
pose proof (YA0j.nth_error_le_byte _ _ _ Hnth) as Hv.
rewrite (nth_indep (map bv_unsigned T) 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
rewrite map_nth. rewrite Hv. unfold disco_table_c.u_at, YO0f.le_byte.
pose proof (bytes_le_to_Z_nonneg (disco_table_c.sub T k 1)) as H0.
pose proof (bytes_le_to_Z_bound (disco_table_c.sub T k 1)) as H1.
assert (Hlen : length (disco_table_c.sub T k 1) = 1%nat) by (unfold disco_table_c.sub; rewrite length_firstn, length_skipn; lia).
rewrite Hlen in H1. assert (Hj0 : j = 0%nat) by lia. subst j.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256 in H1 |- *.
rewrite Z.shiftr_0_r. f_equal. rewrite Z.pow_0_r, Z.div_1_r. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Theorem pb_tj_seg_unk : tj_seg_unk B STK EV EVB IMG.
Proof.
unfold tj_seg_unk, tj_fromU, tj_from0.
intros i FX FT cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0 tj_F tj_FL]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
unfold INV_tjU, tj_lbody, tj_wrote in HINV. cbn [c_cap c_T c_now c_buf c_t c_ly c_S] in HINV.
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & E740 & E741) & HMOD & acc & E813 & Hacc & Htxt & Hgarr).
assert (HTX : reac_disco_table_json_c.tj_text T now = acc ++ tj_f_model_unk ++ tj_f_width_0 ++ tj_after4 (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i).
{ rewrite Htxt. unfold tj_after2. destruct (tjm_P34_unk _ HMOD) as [-> ->]. reflexivity. }
pose proof Hok as (HT1 & _). unfold disco_table_c.tbl_T1 in HT1.
assert (HkEV : k <= EV) by (pose proof (Z.mul_le_mono_nonneg_l (i + 1) 8 EVB HEVB ltac:(lia)); lia).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
paj_run_shc RUNP RUNC HS HJ. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (proj1 HJ) as HARq.
assert (Hinq : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact (proj1 (Hbuf Hcap3))]).
pose proof (proj2 (Hbuf Hcap3)) as Hcq.
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARq Hinq) as (_ & Hq4096 & Hqceil & Hqapp & _).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HARq Hinq) as Hqimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARq Hinq Hfin) as Hqsep.
rewrite EFA0 in Hqsep. fold F in Hqsep. change (fs_frame_bytes 2) with 256 in Hqsep. unfold zdisjoint in Hqsep. cbn [fst snd] in Hqsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hqapp. unfold off_img, IMG_LO, IMG_TOP in Hqimg.
eapply aview_kept_out; [exact HFr | lia | notw AG]. }
clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARc Hinb) as (Hb16 & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HARc Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARc Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
set (L := Z.of_nat (length acc)) in *.
pose proof (img_env_atomP E 288 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E288.
pose proof (img_env_atomP E 289 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E289.
pose proof TJS as (_ & _ & _ & _ & _ & _ & Hmu & Hw0 & _).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof Hmu as (_ & _ & Hmulo & Hmuhi & _). unfold IMG_LO, IMG_TOP in Hmulo, Hmuhi. change (A_OBJ 47) with 288%nat in Hmulo, Hmuhi.
cbn [length tj_f_model_unk Z.of_nat] in Hmulo, Hmuhi.
unfold w64 in E813.
rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 12 buf E12), (U_atom E 813 L E813) by lia; apply zcanon_id; unfold M64; lia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom E 13 cap E13), (U_atom E 813 L E813) by lia; rewrite U_SLit; apply tjm_sub; [reflexivity | lia | lia]) Ra1.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL (A_OBJ 47)) tj_f_model_unk (map PLit tj_f_model_unk) [] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [] tj_f_model_unk cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24392)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp, E3. exact Hgp. }
{ rewrite Qtp, E4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E288. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ apply (tjm_fmt _ _ _ _ _ 47 _ _ HARc HRODc Hmu). unfold snp_out. change (A_OBJ 47) with 288%nat. cbn [length tj_f_model_unk Z.of_nat]. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact (tj_ro_fmt_rng 47 tj_f_model_unk Hmu ltac:(cbn; lia)). }
{ unfold tj_f_model_unk; discriminate. }
{ vm_compute. reflexivity. }
{ cbv [tj_f_model_unk map]. repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros ii Hii; cbn in Hii; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact I. }
{ exact I. }
{ vm_compute. reflexivity. }
{ lia. }
{ cbn. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1a Hf2a HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia. rewrite HSNP in Hfr.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tjm_kept AG Hfr Hpres2).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx') B LAWS). pose (RUNTO := paj_run_to (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
assert (LMU : Z.of_nat (length tj_f_model_unk) = 18) by reflexivity.
assert (LW0 : Z.of_nat (length tj_f_width_0) = 14) by reflexivity.
rewrite LMU in Ha0', Hwr, Hnul, Hfr.
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 813 0) (SLit (-1)))) = cap - L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13v), (U_atom Ev 813 L E813) by lia; rewrite U_SLit; apply tjm_sub; [reflexivity | lia | lia]);
assert (U0 : U Ev (SOff 823 0) = 18) by (apply U_atom; [exact Qr0 | lia])
end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b) in Hc end.
rewrite U0, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha. eapply aview_kept_out; [exact HFr | lia | notw AG]. }
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1a Hf2a) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [exact HkEV|]. split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [intros _; reflexivity|]. split; [|intros _ _; reflexivity].
intros _ Hlt. exfalso. unfold tj_len in Hlt. rewrite HTX, !length_app, !Nat2Z.inj_add in Hlt. fold L in Hlt. lia.
+ cbn [c_fq]. exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
rename Hc into Hn1.
rewrite Z.min_l in Hwr, Hnul, Hfr by lia.
assert (G1 : garr8 SEGS (mrestrict (w_H W3) mem2) buf ((acc ++ tj_f_model_unk) ++ [0])).
{ rewrite <- app_assoc. apply (tjm_garr8_app (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc tj_f_model_unk Hgarr).
- intros a Ha. rewrite (Hfr a ltac:(lia) ltac:(lia) ltac:(lia)). apply HK1. lia.
- intros ii Hii. rewrite LMU in Hii. exact (Hwr ii ltac:(lia)).
- rewrite LMU. exact Hnul. }
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (HK2b : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) mem2 a).
{ intros a Ha. rewrite <- (HK2 a Ha). eapply aview_kept_out; [exact HFr | lia | notw AG]. }
clear HF HFr HG.
assert (G1b : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms1)) buf ((acc ++ tj_f_model_unk) ++ [0])).
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 (ms_mem ms1) buf); [|exact G1].
intros a Ha. rewrite !length_app in Ha. cbn [length] in Ha. apply HK2b. lia. }
pose proof (proj1 HJ2) as HARc2.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD) as HRODc2.
destruct (tj_snp_canary _ _ _ _ _ HARc2) as (cval2 & HG1b & HG2b).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E13w : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (E12w : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by lia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12) end.
rregU HS (10%bv : bv 5) (buf + L + 18) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite (U_atom E5 12 buf E12w), (U_atom E5 813 L E813), (U_atom E5 823 18 Qr0) by lia;
rewrite (zcanon_id (buf + L)) by (unfold M64; lia); apply zcanon_id; unfold M64; lia) Rb0.
rregU HS (11%bv : bv 5) (cap - L - 18) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom E5 13 cap E13w), (U_atom E5 813 L E813), (U_atom E5 823 18 Qr0) by lia;
rewrite !U_SLit; rewrite (tjm_sub cap L) by (first [reflexivity | lia]); apply tjm_sub; [reflexivity | lia | lia]) Rb1.
prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp2. prreg HS (4%bv : bv 5) Qtp2. prreg HS (1%bv : bv 5) Qra2. prreg HS (12%bv : bv 5) Qa22.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fx' GC GV IMGLO IMGHI CR SNPC (ASNP fx') W3 (ms_regs ms1) (ms_mem ms1) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L + 18) (cap - L - 18) (VAL (A_OBJ 48)) tj_f_width_0 (map PLit tj_f_width_0) [] (map (argZ (ms_regs ms1)) [3; 4; 5; 6; 7] ++ []) [] tj_f_width_0 cval2 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24428)) _ HJ2 HRODc2).
{ unfold spZ at 1. rewrite Qsp2, E60, unsigned_lit_small by lia. lia. }
{ rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16. reflexivity. }
{ lia. }
{ lia. }
{ rewrite Qgp2, (AG 3%nat) by lia. rewrite (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp2, (AG 4%nat) by lia. rewrite (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra2. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Rb0. }
{ exact Rb1. }
{ rewrite Qa22, E289. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc2). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1b. }
{ exact HG2b. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ pose proof Hw0 as (_ & _ & Hw0lo & Hw0hi & _). unfold IMG_LO, IMG_TOP in Hw0lo, Hw0hi. change (A_OBJ 48) with 289%nat in Hw0lo, Hw0hi.
cbn [length tj_f_width_0 Z.of_nat] in Hw0lo, Hw0hi.
apply (tjm_fmt _ _ _ _ _ 48 _ _ HARc2 HRODc2 Hw0). unfold snp_out. change (A_OBJ 48) with 289%nat. cbn [length tj_f_width_0 Z.of_nat]. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact (tj_ro_fmt_rng 48 tj_f_width_0 Hw0 ltac:(cbn; lia)). }
{ unfold tj_f_width_0; discriminate. }
{ vm_compute. reflexivity. }
{ cbv [tj_f_width_0 map]. repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros ii Hii; cbn in Hii; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact I. }
{ exact I. }
{ vm_compute. reflexivity. }
{ lia. }
{ cbn. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc2 | exact Hinb | lia | lia]. }
{ exact Hf2a. }
intros fx'' regs3 mem3 md3b Hf1b Hf2b HJ3 HP3 Hb0' Hwr2 Hnul2 Hfr2 Hpres4 Hsame2.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr2 by lia. rewrite HSNP in Hfr2. rewrite LW0 in Hb0', Hwr2, Hnul2, Hfr2.
reseat HS HJ3 HP3 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tjm_kept AG Hfr2 Hpres4).
apply (st_ok_pi_restrict_fx fx' fx'') in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx'') B LAWS). pose (RUNTO := paj_run_to (fx := fx'') B LAWS).
pose (BR := paj_branch (fx := fx'') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx'') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx'') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx'') B LAWS).
prreg HS (10%bv : bv 5) Qr1. cbn [ms_regs] in Qr1. rewrite Hb0' in Qr1. symmetry in Qr1. unfold w64 in Qr1.
lazymatch type of Qr1 with ew ?Ev ?n = _ =>
assert (E13x : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U1 : U Ev (SOff n 0) = 14) by (apply U_atom; [exact Qr1 | lia]);
assert (U5 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 813 0) (SLit (-1)))) (SMd M_MUL (SOff 823 0) (SLit (-1)))) = cap - L - 18)
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13x), (U_atom Ev 813 L E813), (U_atom Ev 823 18 Qr0) by lia;
rewrite !U_SLit; rewrite (tjm_sub cap L) by (first [reflexivity | lia]); apply tjm_sub; [reflexivity | lia | lia])
end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (denot_lit_U Ev a), (denot_lit_U Ev b) in Hc end.
rewrite U1, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ3. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a) by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
+ rewrite branch_geu_U, U1, U5 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
paj_run_to_shc RUNTOP HS HJ3 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx'' Ev k _ _ Wg msF mdF
(fun r Hr => eq_trans (Hf1b r Hr) (Hf1a r Hr)) Hf2b) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ3.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [exact HkEV|]. split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [intros _; reflexivity|]. split; [|intros _ _; reflexivity].
intros _ Hlt. exfalso. unfold tj_len in Hlt. rewrite HTX, !length_app, !Nat2Z.inj_add in Hlt. fold L in Hlt. lia.
* cbn [c_fq]. exact HS.
+ rewrite branch_geu_U, U1, U5 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
rewrite Z.min_l in Hwr2, Hnul2, Hfr2 by lia.
assert (G2 : garr8 SEGS (mrestrict (w_H W3) mem3) buf ((acc ++ tj_f_model_unk ++ tj_f_width_0) ++ [0])).
{ rewrite <- !app_assoc. rewrite (app_assoc acc). apply (tjm_garr8_app (w_H W3) (w_H W3) (ms_mem ms1) mem3 buf (acc ++ tj_f_model_unk) tj_f_width_0 G1b).
- intros a Ha. rewrite length_app, Nat2Z.inj_add, LMU in Ha. fold L in Ha. rewrite (Hfr2 a ltac:(lia) ltac:(lia) ltac:(lia)). reflexivity.
- intros ii Hii. rewrite LW0 in Hii. rewrite length_app, Nat2Z.inj_add, LMU. fold L. replace (buf + (L + 18) + ii) with (buf + L + 18 + ii) by lia. exact (Hwr2 ii ltac:(lia)).
- rewrite length_app, Nat2Z.inj_add, LMU, LW0. fold L. replace (buf + (L + 18) + 14) with (buf + L + 18 + 14) by lia. exact Hnul2. }
paj_run_to_shc RUNTOP HS HJ3 0x5fdc. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (G3 : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ tj_f_model_unk ++ tj_f_width_0) ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem3 m1 buf); [|exact G2];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha; rewrite !Nat2Z.inj_add, LMU, LW0 in Ha; fold L in Ha;
rewrite <- (HK3 a ltac:(lia)); eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
rregU HS (21%bv : bv 5) (L + 18) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 813 L E813), (U_atom _ 823 18 Qr0) by lia; apply zcanon_id; unfold M64; lia) R21.
rregU HS (10%bv : bv 5) 14 ltac:(exact U1) R10.
ra_join HS ss_tjT 950%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join HS ss_tjT 840%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 840%nat 4%nat R10 E844. ra_join_val HS 840%nat 12%nat R21 E852.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FT (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx'' Ev k _ _ Wg msF mdF
(fun r Hr => eq_trans (Hf1b r Hr) (Hf1a r Hr)) Hf2b) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite !ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [apply img_env_havoc_hi; [assumption | unfold A_LIM; lia] | unfold A_LIM; lia].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ3.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjT, tj_lbody, tj_wrote, tj_split. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [exact Hk0|]. split.
{ split; [exact Hperm|]. split; [exact (tj_keep_journal B LAWS STK EV IMG _ _ _ _ _ _ _ _ HBASE HJ3)|].
split; [exact Hcap3|]. split; [exact Hi|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E721|]. split; [exact E722|]. split; [exact E723|]. split; [exact E734|]. split; [exact E740|]. exact E741. }
exists (acc ++ tj_f_model_unk ++ tj_f_width_0). split.
{ exists (L + 18), 14. split; [exact E852|]. split; [exact E844|]. split; [lia|]. split; [lia|].
rewrite !length_app, !Nat2Z.inj_add, LMU, LW0. fold L. lia. }
split; [rewrite !length_app, !Nat2Z.inj_add, LMU, LW0; fold L; lia|].
split; [rewrite HTX, <- !app_assoc; reflexivity|].
rewrite <- !app_assoc in G3. rewrite <- !app_assoc. exact G3.
* cbn [c_fq]. exact HS.
Qed.
Theorem pb_tj_seg_tok : tj_seg_tok B STK EV EVB IMG.
Proof.
unfold tj_seg_tok, tj_fromK, tj_from0.
intros i FX FT cx E k ly3 S3 W3 ms3 md3 HBASE HEX HJ HFR HINV HS.
destruct cx as [fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0].
pose proof HBASE as HB0. pose proof HEX as HX0. unfold tj_baseX in HB0. unfold tj_EX, tj_F, tj_FL in HX0.
unfold INV_tjK, tj_lbody, tj_wrote, tj_F in HINV.
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0]
in HB0, HX0, HINV, HJ, HFR, HS.
pose proof HB0 as (HPRE & Hfrm0 & Hroom & HROD & HIM & H10 & H11 & H12 & H13 & Hnow & Hcap & Hobj & Harr & HlenT & Hok
& Hbuf & Hev & Hsp1b & HE0 & HE032 & HE02).
pose proof HX0 as (AG & E60 & E516 & E528 & E529 & HEI).
destruct HINV as (Hk0 & (Hperm & HKEEP & Hcap3 & Hi & E721 & E722 & E723 & E734 & E740 & E741) & E834 & E832
& (tok & HMOD & Htok & Htra & Hthv) & acc & E833 & Hacc & Htxt & Hgarr).
destruct (tjm_tok _ _ _ HMOD) as (Ltok & Ctok).
assert (HP3 : P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) =
[44; 34; 109; 111; 100; 101; 108; 34; 58; 34] ++ tok ++ [34]) by (unfold P3, key, qstr, k_model; rewrite HMOD; reflexivity).
assert (HTX : reac_disco_table_json_c.tj_text T now = acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)
++ P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)
++ tj_after4 (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i).
{ rewrite Htxt. unfold tj_after2. reflexivity. }
pose proof Hok as (HT1 & _). unfold disco_table_c.tbl_T1 in HT1.
assert (HkEV : k <= EV) by (pose proof (Z.mul_le_mono_nonneg_l (i + 1) 8 EVB HEVB ltac:(lia)); lia).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSNP : SNPRINTF_STK = 11776) by reflexivity.
assert (HSK : 11776 + 640 <= STK) by (unfold TJ_FRAME in HSTK; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
destruct (sp1_facts (spZ regs + -288) ltac:(clear - Hceil Hslo Hstk0 HSK C1; lia)
ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Hsp1b in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 304 <= sp1 <= spZ regs - 288) by (clear - Hsp1r; lia). clear Hsp1r.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & Hk3 & _ & _ & _ & _ & _ & Hpres3 & _ & _ & HQT3).
destruct (al_layout _ _ LAWS ly S W mem md ly3 HAR Hly3) as (Eab3 & EFA & Eown3).
assert (EFA0 : forall c p, frame_addr ly3 c p = frame_addr ly c p) by exact EFA.
set (F := frame_addr ly 2 fpos) in *. set (FLg := flag_addr ly 2 fpos) in *.
assert (Hfin : In (2, fpos) (frames S3)) by (rewrite HFR; left; reflexivity).
assert (HF3 : frame_addr ly3 2 fpos = F) by (rewrite EFA; reflexivity).
assert (E1 : ew E 1 = getr regs 1) by (rewrite (AG 1%nat ltac:(lia)); exact (HE0 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite (AG 2%nat ltac:(lia)); exact (HE0 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (AG 3%nat ltac:(lia)); exact (HE0 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (AG 4%nat ltac:(lia)); exact (HE0 4%nat 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite (AG 10%nat ltac:(lia)); rewrite (HE0 10%nat 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat ltac:(lia)); rewrite (HE0 12%nat 12%bv eq_refl); exact H12).
assert (E13 : ew E 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat ltac:(lia)); rewrite (HE0 13%nat 13%bv eq_refl); exact H13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite (AG 32%nat ltac:(lia)); exact HE032).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (AG 2%nat ltac:(lia)); exact HE02).
img_factsF E.
pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as Hob242. pose proof (pa_obj_img 0 ltac:(unfold disco_nobj; lia)) as Hob241.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as Hob307. pose proof (pa_obj_img 67 ltac:(unfold disco_nobj; lia)) as Hob308.
cbv [A_OBJ Nat.add] in Hob241, Hob242, Hob307, Hob308.
pose proof (palf_uar_img B TL) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
unfold IMG_LO, IMG_TOP in Hob241, Hob242, Hob307, Hob308, Huar.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HFal & [HFhi _] & HFpres & HFSpres).
rewrite EFA in HFal, HFhi, HFpres, HFSpres. fold F in HFal, HFhi, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos HAR3 Hfin) as (HF4096 & HFceil & HFhigh).
rewrite EFA in HF4096, HFceil, HFhigh. fold F in HF4096, HFceil, HFhigh.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR3 Hfin) as HFhigh_img. rewrite EFA in HFhigh_img. fold F in HFhigh_img.
change (fs_frame_bytes 2) with 256 in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
assert (Hsp16 : (sp1 - spZ regs) mod 16 = 0) by (rewrite <- Zminus_mod_idemp_l, Hsp1al16, <- Zminus_mod_idemp_r, Hal16; reflexivity).
clear Hsp1b Hsp1al Hsp1al16 Hal16 HFal. box Hsp16.
pose (RUNP := SRr_run_pi_AJ (fx := fq) B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fq) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fq) B LAWS).
ro_base HS 529%nat. ro_base HS 516%nat.
paj_run_shc RUNP RUNC HS HJ. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (HK1 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. pose proof (proj1 HJ) as HARq.
assert (Hinq : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact (proj1 (Hbuf Hcap3))]).
pose proof (proj2 (Hbuf Hcap3)) as Hcq.
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARq Hinq) as (_ & Hq4096 & Hqceil & Hqapp & _).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HARq Hinq) as Hqimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARq Hinq Hfin) as Hqsep.
rewrite EFA0 in Hqsep. fold F in Hqsep. change (fs_frame_bytes 2) with 256 in Hqsep. unfold zdisjoint in Hqsep. cbn [fst snd] in Hqsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hqapp. unfold off_img, IMG_LO, IMG_TOP in Hqimg.
eapply aview_kept_out; [exact HFr | lia | notw AG]. }
assert (Htok1 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (F + 96) (tok ++ [0])).
{ apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) (ms_mem ms3) (ms_mem ms) (F + 96)); [|exact Htok].
intros a Ha. rewrite length_app in Ha. cbn [length] in Ha. eapply aview_kept_out; [exact HFr | lia | notw AG]. }
assert (Htra1 : range_addressable (aview SEGS (w_H W3) (ms_mem ms)) SHADOW_OFF (F + 96) (Z.of_nat (length tok) + 1)).
{ apply (tjm_ra_kept (aview SEGS (w_H W3) (ms_mem ms3))); [|exact Htra].
intros x Hx. eapply aview_kept_out; [exact HFr | unfold SHADOW_OFF; lia | unfold SHADOW_OFF; notw AG]. }
assert (Hthv1 : shadow_hull_vis (aview SEGS (w_H W3) (ms_mem ms)) (F + 96) (Z.of_nat (length tok) + 1)).
{ apply (tjm_hull_kept (aview SEGS (w_H W3) (ms_mem ms3))); [|exact Hthv].
intros s Hs. unfold shadow_addr, SHADOW_OFF in Hs. eapply aview_kept_out; [exact HFr | lia | notw AG]. }
clear HF HFr HG.
pose proof (proj1 HJ) as HARc.
assert (Hinb0 : In (buf, Nb) (ablocks B ly S)) by exact (proj1 (Hbuf Hcap3)).
assert (Hcapb : cap <= req_size Nb) by exact (proj2 (Hbuf Hcap3)).
assert (Hinb : In (buf, Nb) (ablocks B ly3 S3)) by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinb0]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ buf Nb HARc Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & HNb).
pose proof (blk_off_imgP _ _ _ _ _ _ buf Nb HARc Hinb) as Hbimg.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ buf Nb 2 fpos HARc Hinb Hfin) as Hbsep.
rewrite EFA0 in Hbsep. fold F in Hbsep. change (fs_frame_bytes 2) with 256 in Hbsep. unfold zdisjoint in Hbsep. cbn [fst snd] in Hbsep.
unfold in_app, kLowShadowBeg, kHighMemBeg in Hbapp. unfold off_img, IMG_LO, IMG_TOP in Hbimg.
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARc Hfin) as (_ & _ & HFpc & _). rewrite HF3 in HFpc. change (fs_frame_bytes 2) with 256 in HFpc.
set (L := Z.of_nat (length acc)) in *.
pose proof (img_env_atomP E 290 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E290.
pose proof (img_env_atomP E 291 HEI ltac:(unfold A_TEXT, A_LIM; lia)) as E291.
pose proof TJS as (_ & _ & _ & _ & Hmd & Hwd & _).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD) as HRODc.
destruct (tj_snp_canary _ _ _ _ _ HARc) as (cval & HG1 & HG2).
pose proof tj_snp_gcgv as (Hgc1 & Hgc2 & Hgv1 & Hgv2). unfold IMG_LO, IMG_TOP in Hgc1, Hgc2, Hgv1, Hgv2.
pose proof Hmd as (_ & _ & Hmdlo & Hmdhi & _). unfold IMG_LO, IMG_TOP in Hmdlo, Hmdhi. change (A_OBJ 49) with 290%nat in Hmdlo, Hmdhi.
cbn [length tj_f_model Z.of_nat] in Hmdlo, Hmdhi.
unfold w64 in E833, E834, E832, E740.
assert (LP3 : Z.of_nat (length (P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i))) = 11 + Z.of_nat (length tok))
by (rewrite HP3, !length_app; cbn [length]; lia).
rregU HS (10%bv : bv 5) (buf + L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom E 12 buf E12), (U_atom E 833 L E833) by lia; apply zcanon_id; unfold M64; lia) Ra0.
rregU HS (11%bv : bv 5) (cap - L) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom E 13 cap E13), (U_atom E 833 L E833) by lia; rewrite U_SLit; apply tjm_sub; [reflexivity | lia | lia]) Ra1.
rregU HS (13%bv : bv 5) (F + 96) ltac:(rewrite U_SOff, E516, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia) Ra3.
prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (1%bv : bv 5) Qra. prreg HS (12%bv : bv 5) Qa2.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fq GC GV IMGLO IMGHI CR SNPC (ASNP fq) W3 (ms_regs ms) (ms_mem ms) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L) (cap - L) (VAL (A_OBJ 49)) tj_f_model
[PLit 44; PLit 34; PLit 109; PLit 111; PLit 100; PLit 101; PLit 108; PLit 34; PLit 58; PLit 34; Ps; PLit 34]
[] (map (argZ (ms_regs ms)) [3; 4; 5; 6; 7] ++ []) [APtr tok]
(P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i))
cval (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24468)) _ HJ HRODc).
{ unfold spZ at 1. rewrite Qsp, E60, unsigned_lit_small by lia. lia. }
{ exact Hsp16. }
{ lia. }
{ lia. }
{ rewrite Qgp, E3. exact Hgp. }
{ rewrite Qtp, E4. exact Htp. }
{ exact Qra. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Ra0. }
{ exact Ra1. }
{ rewrite Qa2, E290. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1. }
{ exact HG2. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ apply (tjm_fmt _ _ _ _ _ 49 _ _ HARc HRODc Hmd). unfold snp_out. change (A_OBJ 49) with 290%nat. cbn [length tj_f_model Z.of_nat]. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact (tj_ro_fmt_rng 49 tj_f_model Hmd ltac:(cbn; lia)). }
{ unfold tj_f_model; discriminate. }
{ vm_compute. reflexivity. }
{ repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros ii Hii; cbn in Hii; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ cbn [pf_args_asan map app]. split; [|exact I].
assert (Ha3Z : argZ (ms_regs ms) 3 = F + 96) by (unfold argZ; replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Ra3; apply unsigned_lit_small; lia).
rewrite Ha3Z.
cbn [pf_arg_asan]. split; [exact Ctok|]. split; [lia|]. split; [lia|].
split.
{ intros ii Hii. pose proof (Htok1 (Z.to_nat ii) ltac:(rewrite length_app; cbn [length]; lia)) as (_ & Hrng).
pose proof (garr8_mbyte SEGS _ _ _ (Z.to_nat ii) Htok1 ltac:(rewrite length_app; cbn [length]; lia)) as Hmb.
rewrite Z2Nat.id in Hmb by lia. rewrite aview_mbyte, Hmb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hrng. }
split.
{ intros x Hx. unfold str_end in Hx. apply (aview_some_of_apresent SEGS). apply (proj1 (HFpc x ltac:(lia))). }
split.
{ unfold snp_out, str_end. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
split.
{ unfold amem_range, in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. pose proof (@ASAN_CEIL_range rc) as AC. unfold ASAN_CEIL in AC. lia. }
split; [exact Htra1 | exact Hthv1]. }
{ cbn [SnFF.pf_args_amem map app].
assert (Ha3Z : argZ (ms_regs ms) 3 = F + 96) by (unfold argZ; replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Ra3; apply unsigned_lit_small; lia).
rewrite Ha3Z. split; [exact (amem_range_sub_app F 256 (F + 96) (Z.of_nat (length tok) + 8) HFhigh HFceil ltac:(lia) ltac:(lia) ltac:(lia)) | exact I]. }
{ rewrite HP3. reflexivity. }
{ lia. }
{ rewrite LP3. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc | exact Hinb | lia | lia]. }
{ exact Hfrm0. }
intros fx' regs2 mem2 md2 Hf1a Hf2a HJ2 HP2 Ha0' Hwr Hnul Hfr Hpres2 Hsame.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr by lia. rewrite HSNP in Hfr. rewrite LP3 in Ha0', Hwr, Hnul, Hfr.
reseat HS HJ2 HP2 [0; 1; 2; 3; 4; 5; 6; 7]%nat AG ltac:(idtac; tjm_kept AG Hfr Hpres2).
apply (st_ok_pi_restrict_fx fq fx') in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx') B LAWS). pose (RUNTO := paj_run_to (fx := fx') B LAWS).
pose (BR := paj_branch (fx := fx') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx') B LAWS).
prreg HS (10%bv : bv 5) Qr0. cbn [ms_regs] in Qr0. rewrite Ha0' in Qr0. symmetry in Qr0. unfold w64 in Qr0.
lazymatch type of Qr0 with ew ?Ev ?n = _ =>
assert (E13v : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U4 : U Ev (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 833 0) (SLit (-1)))) = cap - L)
by (rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13v), (U_atom Ev 833 L E833) by lia; rewrite U_SLit; apply tjm_sub; [reflexivity | lia | lia]);
assert (U0 : U Ev (SOff n 0) = 11 + Z.of_nat (length tok)) by (apply U_atom; [exact Qr0 | lia])
end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (tjm_bltz Ev a b (11 + Z.of_nat (length tok)) U0 ltac:(lia) ltac:(rewrite U_SLit; reflexivity)) in Hc end. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK2 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a) by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
pose proof HJ2 as (HARx & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARx Hfin) as (_ & _ & HFpx & HFSx).
rewrite HF3 in HFpx, HFSx. change (fs_frame_bytes 2 / 8) with 32 in HFSx. change (fs_frame_bytes 2) with 256 in HFpx.
fs_rwF HS E529 HFSx. rw516 HS E516 HFpx F.
paj_run_to_shc RUNTOP HS HJ2 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx' Ev k _ _ Wg msF mdF Hf1a Hf2a) end end.
+ exact HBASE.
+ unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
+ cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ2.
+ cbn [c_S c_fpos]. exact HFR.
+ unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [exact HkEV|]. split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [intros _; reflexivity|]. split; [|intros _ _; reflexivity].
intros _ Hlt. exfalso. unfold tj_len in Hlt. rewrite HTX, !length_app, !Nat2Z.inj_add, LP3 in Hlt. fold L in Hlt. lia.
+ cbn [c_fq]. exact HS.
- rewrite branch_geu_U, U0, U4 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
rename Hc into Hn1.
rewrite Z.min_l in Hwr, Hnul, Hfr by lia.
assert (G1 : garr8 SEGS (mrestrict (w_H W3) mem2) buf ((acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)) ++ [0])).
{ rewrite <- app_assoc. apply (tjm_garr8_app (w_H W3) (w_H W3) (ms_mem ms3) mem2 buf acc _ Hgarr).
- intros a Ha. rewrite (Hfr a ltac:(lia) ltac:(lia) ltac:(lia)). apply HK1. lia.
- intros ii Hii. rewrite LP3 in Hii. exact (Hwr ii ltac:(lia)).
- rewrite LP3. exact Hnul. }
lazymatch type of HK2 with forall a, _ -> aview _ _ ?m1 a = _ =>
assert (G1b : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)) ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem2 m1 buf); [|exact G1];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha; apply HK2; rewrite !Nat2Z.inj_add, LP3 in Ha; fold L in Ha; lia) end.
pose proof (tj_keep_journal B LAWS STK EV IMG _ _ _ _ _ _ _ _ HBASE HJ2) as (_ & HarrK & HobjK).
cbn [c_fq c_ly c_S c_W c_regs c_mem c_md c_ch c_t c_now c_buf c_cap c_Nb c_T c_fpos c_sp1 c_E0] in HarrK, HobjK.
pose proof HobjK as ((cid & pos & Hin & Hcid & _ & Hflo & Hfhi) & Ht8 & HraK).
destruct (in_split _ _ Hin) as (l2 & l3 & Hl23).
pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (2, fpos) (cid, pos) [] l2 l3 HAR3 ltac:(rewrite HFR, Hl23; reflexivity)) as HsepT.
unfold frame_rng in HsepT. cbn [fst snd] in HsepT. rewrite !EFA0 in HsepT. fold F in HsepT. change (fs_frame_bytes 2) with 256 in HsepT.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (HT4096 & HTceil & HTapp).
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR Hin) as HTimg.
set (Ft := frame_addr ly cid pos) in *.
pose proof (proj1 (@ASAN_CEIL_range rc)) as ACR. unfold ASAN_CEIL in ACR.
assert (Hi8 : 0 <= i <= 7) by (clear - Hi HT1; lia).
destruct (HraK (t + 48 * i + 15) ltac:(clear - Hi8; lia)) as (s15 & Hs15 & Hok15).
assert (Hs0 : s15 = 0) by (destruct Hok15 as [-> | (Hm & Hm2)]; [reflexivity | exfalso; rewrite (tjm_mod8 t i Ht8) in Hm; clear - Hm Hm2; lia]).
subst s15.
assert (DTc : 4096 <= t /\ t + 400 <= alloc_ceiling) by (clear - HT4096 HTceil Hflo Hfhi; lia).
assert (DT : t + 400 <= 2147446784 \/ 17594333495296 <= t)
by (clear - HTapp Hflo Hfhi; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HTapp; lia).
assert (DTi : t + 400 <= 65536 \/ IMG_TOP <= t) by (clear - HTimg Hflo Hfhi; unfold off_img, IMG_LO in HTimg; lia).
assert (DFs : F + 256 <= t \/ t + 400 <= F) by (clear - HsepT Hflo Hfhi; unfold zdisjoint in HsepT; cbn [fst snd] in HsepT; lia).
assert (DF : F + 256 <= 2147446784 \/ 17594333495296 <= F) by (clear - HFhigh; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFhigh; lia).
unfold IMG_TOP in DTi.
set (din := disco_table_c.u_at T (48 * i + 13) 1) in *. set (dout := disco_table_c.u_at T (48 * i + 14) 1) in *.
pose proof (tjm_garr8_u1 _ _ (48 * i + 13) T HarrK ltac:(lia) ltac:(rewrite HlenT; cbn; lia)) as Vdin.
pose proof (tjm_garr8_u1 _ _ (48 * i + 14) T HarrK ltac:(lia) ltac:(rewrite HlenT; cbn; lia)) as Vdout.
pose proof (tjm_u1_rng T (48 * i + 13)) as Rdin. pose proof (tjm_u1_rng T (48 * i + 14)) as Rdout. fold din in Rdin. fold dout in Rdout.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 880 Ev ssv msv [Z_to_bv 64 din; Z_to_bv 64 dout] HS ltac:(vm_compute; reflexivity)) as HS3;
hei_pose Ev 880%nat [Z_to_bv 64 din; Z_to_bv 64 dout] end.
clear HS. rename HS3 into HS. rebaseE HS AG HEv.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E880 : ew Ev 880 = Z_to_bv 64 din) by (rewrite HEv; exact (ew_havoc_new _ 880 [Z_to_bv 64 din; Z_to_bv 64 dout] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E881 : ew Ev 881 = Z_to_bv 64 dout) by (rewrite HEv; exact (ew_havoc_new _ 880 [Z_to_bv 64 din; Z_to_bv 64 dout] 1 (Z_to_bv 64 0) ltac:(cbn; lia))) end.
clear HEv.
assert (Esh : SB + (t + 48 * i + 14) / 8 = SB + (t + 48 * i + 13) / 8) by (clear - Ht8; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_alias Ev _ _ (SOff 832 0) (SOff 834 0) HS
ltac:(rewrite !denot_lit_U, !U_SOff, E832, E834, Esh; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 834%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E834, unsigned_lit_small by (clear - DTc Hi8 ACR; unfold SB; lia); split; [clear - DTc Hi8 ACR; unfold SB; lia|]; split; [clear - DTc Hi8 ACR; unfold SB; lia|]; split; [intros o Ho; clear - Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (SB + (t + 48 * i + 13) / 8) 0 1 (SLit 0) 0); [reflexivity | clear; cbn; lia | clear; cbn; lia |];
rewrite Z.add_0_r; replace (SB + (t + 48 * i + 13) / 8) with (shadow_of_addr SHADOW_OFF (t + 48 * i + 15)) by (clear - Ht8; unfold shadow_of_addr, SHADOW_OFF, SB; lia);
exact (proj1 (val_mem1_of_aview SEGS _ _ _ _ Hs15)))
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E834; evalE AG; unfold SB in *; clear - DTc DF DFs Ht8 HFq Hi8 Hsp1 Hslo Hceil ACR HSK Hob241 Hob242 Hob307 Hob308 HF4096 HFceil; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 740%nat) 13 15 0 0 [YP09.mkChunk 13 (CVal 1 (SOff 880 0)); YP09.mkChunk 14 (CVal 1 (SOff 881 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite E740, unsigned_lit_small by (clear - DTc Hi8 ACR; lia); split; [clear - DTc Hi8 ACR; lia|]; split; [clear - DTc Hi8 ACR; lia|]; split; [intros o Ho; clear - Ho; lia|];
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
[ apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 13 1 (SOff 880 0) din); [cbn [sv_denot]; rewrite E880, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rdin; cbn; lia | clear; cbn; lia |];
replace (t + 48 * i + 13) with (t + (48 * i + 13)) by (clear; lia); exact Vdin
| apply (chunk_ok_val SEGS Ev _ (t + 48 * i) 14 1 (SOff 881 0) dout); [cbn [sv_denot]; rewrite E881, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Rdout; cbn; lia | clear; cbn; lia |];
replace (t + 48 * i + 14) with (t + (48 * i + 14)) by (clear; lia); exact Vdout ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E740, E834; evalE AG; unfold SB in *; clear - DT DTc DTi DFs Ht8 HFq HF8lo HF8hi Hi8 Hsp1 Hslo Hceil ACR HSK Hob241 Hob242 Hob307 Hob308 HF4096 HFceil; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ss HS.
paj_run_shc RUNP RUNC HS HJ2. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
assert (EDin : e_decl_in (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) = din) by reflexivity.
assert (EDout : e_decl_out (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) = dout) by reflexivity.
assert (HP4 : P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i) =
[44; 34; 119; 105; 100; 116; 104; 34; 58; 34] ++ disco_json_text.dec din ++ [120] ++ disco_json_text.dec dout ++ [34])
by (unfold P4, key, qstr, k_width; rewrite HMOD; cbn [snd]; rewrite EDin, EDout, <- !app_assoc; reflexivity).
pose proof (tj_lemmas.dec_len din) as Ldin. pose proof (tj_lemmas.dec_len dout) as Ldout.
set (r1 := 11 + Z.of_nat (length tok)) in *.
set (r2 := 12 + Z.of_nat (length (disco_json_text.dec din)) + Z.of_nat (length (disco_json_text.dec dout))).
assert (LP4 : Z.of_nat (length (P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i))) = r2)
by (rewrite HP4, !length_app; cbn [length]; unfold r2; lia).
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK3 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a) by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into msC end.
assert (G1c : garr8 SEGS (mrestrict (w_H W3) (ms_mem msC)) buf ((acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)) ++ [0])).
{ lazymatch type of G1b with garr8 _ (mrestrict _ ?mb) _ _ =>
apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mb (ms_mem msC) buf); [|exact G1b] end.
intros a Ha. rewrite !length_app in Ha. cbn [length] in Ha. apply HK3. rewrite !Nat2Z.inj_add, LP3 in Ha. fold L in Ha. lia. }
pose proof (proj1 HJ2) as HARc2.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 HROD) as HRODc2.
destruct (tj_snp_canary _ _ _ _ _ HARc2) as (cval2 & HG1b & HG2b).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (E13w : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (E12w : ew Ev 12 = Z_to_bv 64 buf) by (rewrite (AG 12%nat) by lia; rewrite (HE0 12%nat 12%bv eq_refl); exact H12) end.
rregU HS (10%bv : bv 5) (buf + L + r1) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 12 buf E12w), (U_atom _ 833 L E833), (U_atom _ 843 r1 Qr0) by lia;
rewrite (zcanon_id (buf + L)) by (unfold M64; lia); apply zcanon_id; unfold M64; lia) Rb0.
rregU HS (11%bv : bv 5) (cap - L - r1) ltac:(rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom _ 13 cap E13w), (U_atom _ 833 L E833), (U_atom _ 843 r1 Qr0) by lia;
rewrite !U_SLit; rewrite (tjm_sub cap L) by (first [reflexivity | lia]); apply tjm_sub; [reflexivity | lia | lia]) Rb1.
rregU HS (13%bv : bv 5) din ltac:(rewrite U_SExt; cbv beta iota; rewrite (U_atom _ 880 din E880) by lia; change (2 ^ Z.of_N 8) with 256; rewrite Z.mod_small by lia; apply zcanon_id; unfold M64; lia) Rb3.
rregU HS (14%bv : bv 5) dout ltac:(rewrite U_SExt; cbv beta iota; rewrite (U_atom _ 881 dout E881) by lia; change (2 ^ Z.of_N 8) with 256; rewrite Z.mod_small by lia; apply zcanon_id; unfold M64; lia) Rb4.
assert (Ha3Z : argZ (ms_regs msC) 3 = din) by (unfold argZ; replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Rb3; apply unsigned_lit_small; lia).
assert (Ha4Z : argZ (ms_regs msC) 4 = dout) by (unfold argZ; replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity); rewrite Rb4; apply unsigned_lit_small; lia).
prreg HS (2%bv : bv 5) Qsp2. prreg HS (3%bv : bv 5) Qgp2. prreg HS (4%bv : bv 5) Qtp2. prreg HS (1%bv : bv 5) Qra2. prreg HS (12%bv : bv 5) Qa22.
pmkst HS. rewrite HSNPC.
eapply (aj_sh_snprintf_at B LAWS pa_segs_low STK fx' GC GV IMGLO IMGHI CR SNPC (ASNP fx') W3 (ms_regs msC) (ms_mem msC) (spZ regs) (tj_fp buf cap) ly S W mem md [(2, fpos)] ly3 S3 _ k (buf + L + r1) (cap - L - r1) (VAL (A_OBJ 50)) tj_f_width
[PLit 44; PLit 34; PLit 119; PLit 105; PLit 100; PLit 116; PLit 104; PLit 34; PLit 58; PLit 34; Pd; PLit 120; Pd; PLit 34]
[] (map (argZ (ms_regs msC)) [3; 4; 5; 6; 7] ++ []) [AInt din; AInt dout]
(P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i))
cval2 (sp1 - spZ regs) (Z_to_bv 64 (BASE + 24532)) _ HJ2 HRODc2).
{ unfold spZ at 1. rewrite Qsp2, E60, unsigned_lit_small by lia. lia. }
{ exact Hsp16. }
{ lia. }
{ lia. }
{ rewrite Qgp2, (AG 3%nat) by lia. rewrite (HE0 3%nat 3%bv eq_refl). exact Hgp. }
{ rewrite Qtp2, (AG 4%nat) by lia. rewrite (HE0 4%nat 4%bv eq_refl). exact Htp. }
{ exact Qra2. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ exact Rb0. }
{ exact Rb1. }
{ rewrite Qa22, E291. reflexivity. }
{ exact (tj_snp_consts _ _ HRODc2). }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. lia. }
{ eapply Forall_impl; [|exact tj_snp_cr]. intros r Hr. cbv beta in *. unfold IMG_LO, IMG_TOP in Hr. unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact HG1b. }
{ exact HG2b. }
{ lia. }
{ lia. }
{ lia. }
{ lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ pose proof Hwd as (_ & _ & Hwdlo & Hwdhi & _). unfold IMG_LO, IMG_TOP in Hwdlo, Hwdhi. change (A_OBJ 50) with 291%nat in Hwdlo, Hwdhi.
cbn [length tj_f_width Z.of_nat] in Hwdlo, Hwdhi.
apply (tjm_fmt _ _ _ _ _ 50 _ _ HARc2 HRODc2 Hwd). unfold snp_out. change (A_OBJ 50) with 291%nat. cbn [length tj_f_width Z.of_nat]. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ exact (tj_ro_fmt_rng 50 tj_f_width Hwd ltac:(cbn; lia)). }
{ unfold tj_f_width; discriminate. }
{ vm_compute. reflexivity. }
{ repeat (apply Forall_cons; [exact I|]). apply Forall_nil. }
{ split; [reflexivity | intros ii Hii; cbn in Hii; lia]. }
{ cbn [length Z.of_nat]. lia. }
{ unfold snp_out. fa2 ltac:(unfold zdisjoint; cbn [fst snd]; lia). }
{ cbn [pf_args_asan map app]. split; [|split; [|exact I]].
+ cbn [pf_arg_asan]. rewrite Ha3Z. split; [lia | reflexivity].
+ cbn [pf_arg_asan]. rewrite Ha4Z. split; [lia | reflexivity]. }
{ exact I. }
{ rewrite HP4, (tjm_dec din Rdin), (tjm_dec dout Rdout). reflexivity. }
{ lia. }
{ rewrite LP4. unfold r2. lia. }
{ lia. }
{ lia. }
{ unfold snp_out. cbn [pairwise]. split; [apply Forall_cons; [unfold zdisjoint; cbn [fst snd]; lia | apply Forall_nil] | split; [apply Forall_nil | exact I]]. }
{ intros a Ha. split; [|lia]. right. left. split.
+ exists (buf, buf + cap). split; [unfold tj_fp; rewrite (proj2 (Z.ltb_ge cap 3) Hcap3); left; reflexivity | cbn [fst snd]; lia].
+ exists buf, Nb. split; [exact Hinb | lia]. }
{ apply (amem_range_of_block8 SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ apply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ apply (shadow_hull_vis_of_block SEGS B LAWS _ _ _ _ _ buf Nb _ _ HARc2 Hinb); lia. }
{ eapply tj_dest_off_globals; [exact (proj1 tj_snp_img) | exact (proj2 tj_snp_img) | exact HARc2 | exact Hinb | lia | lia]. }
{ exact Hf2a. }
intros fx'' regs3 mem3 md3b Hf1b Hf2b HJ3 HPr3 Hb0' Hwr2 Hnul2 Hfr2 Hpres4 Hsame2.
replace (spZ regs + (sp1 - spZ regs)) with sp1 in Hfr2 by lia. rewrite HSNP in Hfr2. rewrite LP4 in Hb0', Hwr2, Hnul2, Hfr2.
reseat HS HJ3 HPr3 [2; 3; 4; 5; 6; 7; 8; 9]%nat AG ltac:(idtac; tjm_kept AG Hfr2 Hpres4).
apply (st_ok_pi_restrict_fx fx' fx'') in HS.
clear RUN RUNTO BR RUNP RUNTOP RUNC.
pose (RUN := paj_run (fx := fx'') B LAWS). pose (RUNTO := paj_run_to (fx := fx'') B LAWS).
pose (BR := paj_branch (fx := fx'') (PI := PI)).
pose (RUNP := SRr_run_pi_AJ (fx := fx'') B LAWS). pose (RUNTOP := SRr_run_to_pi_AJ (fx := fx'') B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (fx := fx'') B LAWS).
prreg HS (10%bv : bv 5) Qr1. cbn [ms_regs] in Qr1. rewrite Hb0' in Qr1. symmetry in Qr1. unfold w64 in Qr1.
lazymatch type of Qr1 with ew ?Ev ?n = _ =>
assert (E13x : ew Ev 13 = Z_to_bv 64 cap) by (rewrite (AG 13%nat) by lia; rewrite (HE0 13%nat 13%bv eq_refl); exact H13);
assert (U1 : U Ev (SOff n 0) = r2) by (apply U_atom; [exact Qr1 | unfold r2; lia]);
assert (U5 : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 13 0) (SMd M_MUL (SOff 833 0) (SLit (-1)))) (SMd M_MUL (SOff 843 0) (SLit (-1)))) = cap - L - r1)
by (rewrite !U_SAlu; cbn [zalu_raw]; rewrite !U_SMd; cbn [zmd_raw]; rewrite (U_atom Ev 13 cap E13x), (U_atom Ev 833 L E833), (U_atom Ev 843 r1 Qr0) by lia;
rewrite !U_SLit; rewrite (tjm_sub cap L) by (first [reflexivity | lia]); apply tjm_sub; [reflexivity | lia | lia])
end.
psrr_branch_pi RUNP BR HS.
{ exfalso. lazymatch type of Hc with branch_taken _ (sv_denot ?Ev ?a) (sv_denot _ ?b) = _ =>
rewrite (tjm_bltz Ev a b r2 U1 ltac:(unfold r2; lia) ltac:(rewrite U_SLit; reflexivity)) in Hc end. discriminate Hc. }
clear Hc.
paj_run_shc RUNP RUNC HS HJ3. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (HK4 : forall a, buf <= a < buf + cap -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a) by (intros a Ha; eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
+ rewrite branch_geu_U, U1, U5 in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
pose proof HJ3 as (HARy & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARy Hfin) as (_ & _ & HFpy & HFSy).
rewrite HF3 in HFpy, HFSy. change (fs_frame_bytes 2 / 8) with 32 in HFSy. change (fs_frame_bytes 2) with 256 in HFpy.
fs_rwF HS E529 HFSy. rw516 HS E516 HFpy F.
paj_run_to_shc RUNTOP HS HJ3 0x621c. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
prreg HS (21%bv : bv 5) R21.
ra_join HS ss_tjX 640%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 20; 21; 23; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 640%nat 13%nat R21 E653.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FX (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx'' Ev k _ _ Wg msF mdF
(fun r Hr => eq_trans (Hf1b r Hr) (Hf1a r Hr)) Hf2b) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [assumption | unfold A_LIM; lia].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ3.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjX. cbn [c_ly c_S c_cap c_T c_now c_buf].
split; [exact HkEV|]. split; [exact Hperm|].
exists (-1). split; [rewrite E653; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity|].
split; [intros _; reflexivity|]. split; [|intros _ _; reflexivity].
intros _ Hlt. exfalso. unfold tj_len in Hlt. rewrite HTX, !length_app, !Nat2Z.inj_add, LP3, LP4 in Hlt. fold L in Hlt. lia.
* cbn [c_fq]. exact HS.
+ rewrite branch_geu_U, U1, U5 in Hc. apply negb_false_iff, Z.ltb_lt in Hc.
rewrite Z.min_l in Hwr2, Hnul2, Hfr2 by lia.
assert (G2 : garr8 SEGS (mrestrict (w_H W3) mem3) buf ((acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)
++ P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)) ++ [0])).
{ rewrite <- !app_assoc. rewrite (app_assoc acc). apply (tjm_garr8_app (w_H W3) (w_H W3) (ms_mem msC) mem3 buf _ _ G1c).
- intros a Ha. rewrite length_app, Nat2Z.inj_add, LP3 in Ha. fold L in Ha. rewrite (Hfr2 a ltac:(lia) ltac:(lia) ltac:(lia)). reflexivity.
- intros ii Hii. rewrite LP4 in Hii. rewrite length_app, Nat2Z.inj_add, LP3. fold L. replace (buf + (L + r1) + ii) with (buf + L + r1 + ii) by lia. exact (Hwr2 ii ltac:(lia)).
- rewrite length_app, Nat2Z.inj_add, LP3, LP4. fold L. replace (buf + (L + r1) + r2) with (buf + L + r1 + r2) by lia. exact Hnul2. }
paj_run_to_shc RUNTOP HS HJ3 0x5fdc. { awrFL_with ltac:(idtac; tj_hd AG HSK) AG fpos F EFA0. }
lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) =>
assert (G3 : garr8 SEGS (mrestrict (w_H W3) m1) buf ((acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)
++ P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)) ++ [0]))
by (apply (garr8_aview_kept SEGS (w_H W3) (w_H W3) mem3 m1 buf); [|exact G2];
intros a Ha; rewrite !length_app in Ha; cbn [length] in Ha; rewrite !Nat2Z.inj_add, LP3, LP4 in Ha; fold L in Ha;
rewrite <- (HK4 a ltac:(lia)); eapply aview_kept_out; [exact HFr | lia | notw AG]) end.
clear HF HFr HG.
pose proof HJ3 as (HARz & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 2 fpos HARz Hfin) as (_ & _ & HFpz & HFSz).
rewrite HF3 in HFpz, HFSz. change (fs_frame_bytes 2 / 8) with 32 in HFSz. change (fs_frame_bytes 2) with 256 in HFpz.
fs_rwF HS E529 HFSz. rw516 HS E516 HFpz F.
rregU HS (21%bv : bv 5) (L + r1) ltac:(rewrite U_SAlu; cbn [zalu_raw]; rewrite (U_atom _ 833 L E833), (U_atom _ 843 r1 Qr0) by lia; apply zcanon_id; unfold M64; lia) R21.
rregU HS (10%bv : bv 5) r2 ltac:(exact U1) R10.
ra_join HS ss_tjT 950%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join HS ss_tjT 840%nat ([1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 24; 26; 27; 28; 29; 30; 31]%bv : list (bv 5)) idtac.
ra_join_val HS 840%nat 4%nat R10 E844. ra_join_val HS 840%nat 12%nat R21 E852.
lazymatch goal with |- SRr _ ?Wg (mkCfg ?msF ?mdF) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (tj_from0_at_fx B STK EV IMG _ _ FT (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) fx'' Ev k _ _ Wg msF mdF
(fun r Hr => eq_trans (Hf1b r Hr) (Hf1a r Hr)) Hf2b) end end.
* exact HBASE.
* unfold tj_EX, tj_F, tj_FL. cbn [c_ly c_fpos c_E0 c_sp1]. fold F FLg.
split; [intros n Hn; rewrite !ew_havoc_old by lia; exact (AG n Hn)|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E60|]. split; [exact E516|]. split; [exact E528|]. split; [exact E529|].
apply img_env_havoc_hi; [apply img_env_havoc_hi; [assumption | unfold A_LIM; lia] | unfold A_LIM; lia].
* cbn [c_regs c_ly c_S c_W c_mem c_md c_fpos c_buf c_cap]. exact HJ3.
* cbn [c_S c_fpos]. exact HFR.
* unfold INV_tjT, tj_lbody, tj_wrote, tj_split. cbn [c_ly c_S c_cap c_T c_now c_buf c_t].
split; [exact Hk0|]. split.
{ split; [exact Hperm|]. split; [exact (tj_keep_journal B LAWS STK EV IMG _ _ _ _ _ _ _ _ HBASE HJ3)|].
split; [exact Hcap3|]. split; [exact Hi|].
rewrite !ew_havoc_old by (cbn; lia).
split; [exact E721|]. split; [exact E722|]. split; [exact E723|]. split; [exact E734|]. split; [exact E740|]. exact E741. }
exists (acc ++ P3 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)
++ P4 reac_disco_table_json_c.box_tok (tj_e (mkTJCX fq ly S W regs mem md ch t now buf cap Nb T fpos sp1 E0) i)). split.
{ exists (L + r1), r2. split; [exact E852|]. split; [exact E844|]. split; [lia|]. split; [unfold r2; lia|].
rewrite !length_app, !Nat2Z.inj_add, LP3, LP4. fold L. lia. }
split; [rewrite !length_app, !Nat2Z.inj_add, LP3, LP4; fold L; lia|].
split; [rewrite HTX, <- !app_assoc; reflexivity|].
rewrite <- !app_assoc in G3. rewrite <- !app_assoc. exact G3.
* cbn [c_fq]. exact HS.
Qed.
End h.
End f.
End d.
