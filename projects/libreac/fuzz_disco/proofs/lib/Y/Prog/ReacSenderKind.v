(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:86-90
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 332-335, 358-363, 460-463 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1593-1596, 1605-1615 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:2082-2086 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:393-396. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue_defect.v, with its module paths, module names and numbers changed; 528 of its 630 lines of code are new or changed and 557 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YXcalls.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YA0o YCbm YA0q YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require FpStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacRivalKindOf ReacMasterOnlyCadenceNs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
reac_rate_snap_c reac_rival_kind_of_c reac_master_only_cadence_ns_c reac_sender_kind_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing} {PX : PAXcalls lib_both3_0_listing} {PO : PAObjImg lib_both3_0_listing} {PH : PAHiImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TMOC : treac_master_only_cadence_ns_spec B.
Hypothesis TRIVAL : treac_rival_kind_of_spec B.
Definition REAC_SENDER_KIND_STK : Z := 16 + REAC_MASTER_ONLY_CADENCE_NS_STK.
Definition treac_sender_kind_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (e now r d s c fs : Z) : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = @YK11.fp_csr fq /\
    apost_base (fx := fq') SEGS B REAC_SENDER_KIND_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (reac_sender_kind_model e r d s c fs now) /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\ W' = W /\
         (forall a : word, ~ (spZ regs - REAC_SENDER_KIND_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a)) W' c'.
Definition treac_sender_kind_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (e now fps r d s c fs : Z),
  afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
  getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
  getr regs 12 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
  (e <> 0 ->
     e + 40 <= 2 ^ 63 /\ in_app (e + 8) 32 /\ off_img (e + 8) 32 /\
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 /\
     (forall a, e + 8 <= a < e + 40 -> apresent (w_H W) mem a) /\
     -2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\ 0 <= fs < 2 ^ 64 /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c /\
     val_mem SEGS (mrestrict (w_H W) mem) (e + 32) 8 fs) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_sender_kind) regs mem md)
    (treac_sender_kind_post fq regs ly S W mem md e now r d s c fs).
Section w.
Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
Import YN3v YI04 YI09 YI08 YG0v YK04 YA0i YA0n YA0o YCbm YA0q.
Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0s YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC8g YM05.
Context {fx : YK11.FPState}.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run (PL := PL_both3_0) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Definition sk_regions : smem := [stack_region 16; got_regionP; bcell_regionP 36;
YP09.mkRegion (Some 10%nat) 8 40 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0)); YP09.mkChunk 12 (CVal 1 (SOff 33 0));
YP09.mkChunk 20 (CVal 4 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 35 0))]].
Definition sk_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4088 140737479966720 3); (32%nat, mkAF 0 4294967295 0);
(33%nat, mkAF 0 255 0); (34%nat, mkAF 0 4294967295 0); (36%nat, mkAF SB_RK SB_RK 0)] [] [].
Definition ss_sk : sstate := mkSS AF_both3_reac_sender_kind sr_atoms sk_regions None sk_facts.
Definition ss_sk0p : sstate := mkSS AF_both3_reac_sender_kind (sr_set sr_atoms 10%bv (SLit 0)) [stack_region 16] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition sk_SH : list shent := [mkSHE 10 8 40].
Definition sk_extra (r d c fs : Z) : list word := map (Z_to_bv 64) [r mod 2 ^ 32; d; c; fs; SB_RK].
Lemma sk_view_kept : forall H (m m' : word -> option byte) lo hi x,
(forall y : word, ~ (lo <= bv_unsigned y < hi) -> m' y = m y) -> ~ (lo <= x mod 2 ^ 64 < hi) ->
aview SEGS H m' x = aview SEGS H m x.
Proof.
intros H m m' lo hi x K Hx. unfold aview, mbyte, mrestrict. rewrite (K (Z_to_bv 64 x)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hx.
Qed.
Lemma sk_val_mem_kept : forall H (m m' : word -> option byte) lo hi a n v,
(forall y : word, ~ (lo <= bv_unsigned y < hi) -> m' y = m y) ->
(forall k, (k < n)%nat -> ~ (lo <= (a + Z.of_nat k) mod 2 ^ 64 < hi)) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' lo hi a n v K Hk V k Hkn. specialize (V k Hkn). unfold mbyte, mrestrict in *.
rewrite (K (Z_to_bv 64 (a + Z.of_nat k))); [exact V|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact (Hk k Hkn).
Qed.
Lemma sk_apresent_kept : forall H (m m' : word -> option byte) lo hi a,
(forall y : word, ~ (lo <= bv_unsigned y < hi) -> m' y = m y) -> ~ (lo <= a mod 2 ^ 64 < hi) ->
apresent H m a -> apresent H m' a.
Proof.
intros H m m' lo hi a K Hx [Hh [b Hb]]. split; [exact Hh|]. exists b.
rewrite (K (Z_to_bv 64 a)); [exact Hb|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). exact Hx.
Qed.
Lemma sk_garr8_kept : forall H (m m' : word -> option byte) lo hi base l,
(forall y : word, ~ (lo <= bv_unsigned y < hi) -> m' y = m y) ->
(forall j, (j < length l)%nat -> ~ (lo <= (base + Z.of_nat j) mod 2 ^ 64 < hi)) ->
garr8 SEGS (mrestrict H m) base l -> garr8 SEGS (mrestrict H m') base l.
Proof.
intros H m m' lo hi base l K Hj G j Hjl. destruct (G j Hjl) as [V R]. split; [|exact R].
apply (sk_val_mem_kept H m m' lo hi _ _ _ K); [|exact V].
intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Nat2Z.inj_0, Z.add_0_r. exact (Hj j Hjl).
Qed.
Lemma sk_kept_join : forall (m0 m1 m2 : word -> option byte) lo1 hi1 lo2 hi2 lo hi,
(forall y : word, ~ (lo1 <= bv_unsigned y < hi1) -> m1 y = m0 y) ->
(forall y : word, ~ (lo2 <= bv_unsigned y < hi2) -> m2 y = m1 y) ->
lo <= lo1 -> hi1 <= hi -> lo <= lo2 -> hi2 <= hi ->
forall y : word, ~ (lo <= bv_unsigned y < hi) -> m2 y = m0 y.
Proof. intros m0 m1 m2 lo1 hi1 lo2 hi2 lo hi K1 K2 H1 H2 H3 H4 y Hy. rewrite K2 by lia. apply K1. lia. Qed.
Lemma U_addiw_m1_ltu1 : forall E n r, ew E n = Z_to_bv 64 (r mod 2 ^ 32) -> -2 ^ 31 <= r < 2 ^ 31 ->
(1 <? U E (SAluw ALU_ADD (SExt true 32 (SOff n 0)) (SLit (-1)))) = negb ((r =? 1) || (r =? 2)).
Proof.
intros E n r H Hr. rewrite U_of_S, S_SAluw, (U_sx32_val E n (r mod 2 ^ 32) H) by (apply Z.mod_pos_bound; lia).
rewrite U_SLit. cbn [zalu_raw]. unfold zcanon, M64, bv_swrap, bv_wrap.
replace (bv_half_modulus 32) with 2147483648 by reflexivity. replace (bv_modulus 32) with 4294967296 by reflexivity.
replace (bv_modulus 64) with (2 ^ 64) by reflexivity.
apply Bool.eq_iff_eq_true. rewrite Z.ltb_lt, negb_true_iff, orb_false_iff, !Z.eqb_neq.
destruct (Z.ltb_spec (r mod 2 ^ 32) (2 ^ 31)); split; intros; Z.div_mod_to_equations; lia.
Qed.
Lemma sk_post_U : forall E now fs, ew E 11 = Z_to_bv 64 now -> ew E 35 = Z_to_bv 64 fs -> ew E 41 = Z_to_bv 64 (10 ^ 9) ->
0 <= fs < now -> now < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 11 0) (SMd M_MUL (SOff 35 0) (SLit (-1)))) (SOff 41 0)) (SLit 2)) (SLit 0))
= if now - fs <? 10 ^ 9 then 3 else 2.
Proof.
intros E now fs H11 H35 H41 Hf Hn.
rewrite !U_SAlu, U_SMd, !U_SLit, (U_atom E 11 now H11), (U_atom E 35 fs H35), (U_atom E 41 (10 ^ 9) H41) by lia.
cbn [zalu_raw zmd_raw].
assert (X : zcanon (now + zcanon (fs * zcanon (-1))) = now - fs).
{ unfold zcanon, M64. rewrite Zplus_mod_idemp_r. replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
replace (now + fs * (2 ^ 64 - 1)) with ((now - fs) + fs * 2 ^ 64) by ring. rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
rewrite X. destruct (now - fs <? 10 ^ 9); reflexivity.
Qed.
Lemma sk_entry : forall ly S W (regs : bvmap 5 word) mem md ch (e r d c fs : Z),
afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
in_app (e + 8) 32 -> off_img (e + 8) 32 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 ->
-2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= c < 2 ^ 32 -> 0 <= fs < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 32) 8 fs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (sk_extra r d c fs))) ss_sk
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_sender_kind)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx_RK sk_SH (Eimg (Ereg regs (sk_extra r d c fs))) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch e r d c fs HPRE H10 Re He8 Hia Hoi Hrad Rr Rd Rc Rfs M8 M12 M20 M32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (Heb : 4096 <= e + 8 /\ e + 40 <= 140737479966720) by (revert Hia C1; clear; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_val_range (A_OBJ 0)) as VR0. pose proof (pa_val_range (A_OBJ 12)) as VR12.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (sk_extra r d c fs))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (sk_extra r d c fs)) n)
by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 e) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 (r mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 fs) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 SB_RK) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E43 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Rm : 0 <= r mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia).
split.
- unfold ss_sk. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold sk_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 36 0) SB_RK);
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB_RK; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat e E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
-- apply (chunk_ok_val SEGS E _ e 8 4 _ (r mod 2 ^ 32)); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact (val_mem_mod32 _ _ _ M8).
-- apply (chunk_ok_val SEGS E _ e 12 1 _ d); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M12].
-- apply (chunk_ok_val SEGS E _ e 20 4 _ c); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M20].
-- apply (chunk_ok_val SEGS E _ e 32 8 _ fs); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M32].
+ apply pairwise_disjoint_of_extents. unfold sk_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat e E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by lia. rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by lia.
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hia Hoi C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [sk_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, E36, !unsigned_lit_small by (unfold SB_RK; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 Heb C1 C3 WS Hstk0 Rm Rd Rc He8. clear.
unfold SB_RK. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, sk_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E Bx_RK 10 (e + 8) 32 e 8 40 Hrad).
+ unfold U, Bx_RK. cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB_RK; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia. + lia.
+ intros x Hx. cbn [Z.min Z.max] in Hx. revert Hia Hx. clear. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.
Lemma sk_entry0 : forall ly S W (regs : bvmap 5 word) mem md ch,
afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
getr regs 10 = w64 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_sk0p
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_sender_kind)) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx_RK0 [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md ch HPRE H10. split; [|constructor].
apply (st_ok_pi_pin_reg' _ (mkSS AF_both3_reac_sender_kind sr_atoms [stack_region 16] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [])) _ 10%bv 0); [| cbn [restrict ms_regs mkst]; exact H10 | reflexivity].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Usp.
change (2 ^ 4) with 16.
revert Hslo Hshi H47 Hceil Hal16 C1 WS Hstk0. clear. intros.
repeat match goal with |- _ /\ _ => split end; lia.
Qed.
Ltac sk_side := first [ cbn [ew ewset Nat.eqb]; assumption | lia ].
Ltac sk_wr Usp :=
let rr := fresh "rr" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
intros rr a Hin Ha;
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change rs with rs' in Hin end;
cbn [In] in Hin; repeat destruct Hin as [Hin | Hin]; try contradiction; subst rr;
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
first [ lia | (cbn [ew ewset Nat.eqb] in Ha; rewrite Usp in Ha; lia) ].
Ltac sk_kept Usp :=
lazymatch goal with KEPT : forall x : word, ~ (?lo <= bv_unsigned x < ?hi) -> ?m1 x = ?m0 x, HF : frame_of ?Ex ?rs ?m1 ?m2 |- _ =>
let K2 := fresh "KEPT" in
pose proof (rk_kept_step Ex rs m0 m1 m2 lo hi HF ltac:(sk_wr Usp) KEPT) as K2; clear KEPT HF; rename K2 into KEPT end.
Ltac sk_U r d c fs now H :=
rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in H;
rewrite ?U_lit in H by lia;
rewrite ?(U_addiw_m1_ltu1 _ 32 r) in H by sk_side;
rewrite ?(U_sx32_eqk_u _ 34 c) in H by sk_side;
rewrite ?(U_atom _ 33 d) in H by sk_side;
rewrite ?(U_atom _ 35 fs) in H by sk_side;
rewrite ?(U_atom _ 11 now) in H by sk_side.
Ltac sk_bools :=
repeat match goal with
| H : negb _ = true |- _ => apply negb_true_iff in H
| H : negb _ = false |- _ => apply negb_false_iff in H
| H : (_ || _) = true |- _ => apply orb_true_iff in H
| H : (_ || _) = false |- _ => apply orb_false_iff in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : _ /\ _ |- _ => destruct H
end.
Ltac sk_tests :=
repeat match goal with
| |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
| |- context [?a <=? ?b] => destruct (Z.leb_spec a b)
| |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
end; cbn [negb orb]; first [reflexivity | exfalso; lia].
Lemma sk_getr_upd8 : forall (regs : bvmap 5 word) v, getr (regupd regs 8 v) 8 = v.
Proof.
intros regs v. unfold getr, regupd. destruct (bv_eqb _ _) eqn:Hb; [vm_compute in Hb; discriminate|]. apply FpStep.fp_rg_same.
Qed.
Lemma sk_tail_rival_ok : forall ly S W (regs : bvmap 5 word) mem md ch (regsT : bvmap 5 word) memT mdT (e now r d s c fs : Z),
afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
ajournal SEGS B REAC_SENDER_KIND_STK (spZ regs) [] ly S W mem md [] ly S W memT mdT 0 ->
(forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> memT x = mem x) ->
aregs_preserved regs regsT ->
getr regsT 1 = getr regs 1 -> getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
getr regsT 8 = getr regs 8 -> getr regsT 10 = getr regs 10 ->
getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 -> e <> 0 ->
e + 40 <= 2 ^ 63 -> in_app (e + 8) 32 -> off_img (e + 8) 32 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 ->
(forall a, e + 8 <= a < e + 40 -> apresent (w_H W) mem a) ->
-2 ^ 31 <= r < 2 ^ 31 -> 0 <= d < 2 ^ 8 -> 0 <= s < 2 ^ 8 -> 0 <= c < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s ->
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c ->
(negb (d =? 0) || (r =? 1) || (r =? 2)) = true ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_both3_reac_rival_kind_of)) memT (seg_rom SEGS)) mdT)
(treac_sender_kind_post fx regs ly S W mem md e now r d s c fs).
Proof.
intros ly S W regs mem md ch regsT memT mdT e now r d s c fs HPRE HRO HJ KEPT HPT T1 T2 T3 T4 T8 T10
H10 Re He8 He0 He40 Hia Hoi Hrad Hpr Rr Rd Rs Rc M8 M12 M16 M20 Hsel.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (WR : REAC_RIVAL_KIND_OF_STK = 4112) by reflexivity.
assert (Heb : 4096 <= e + 8 /\ e + 40 <= spZ regs - 4224) by (revert Hia C1 Hceil Hslo WS; clear; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL; intros; lia).
assert (UspT : spZ regsT = spZ regs) by (unfold spZ; rewrite T2; reflexivity).
assert (FAR : forall a, 0 <= a < spZ regs - 16 -> ~ (spZ regs - 16 <= a mod 2 ^ 64 < spZ regs)) by (intros a Ha; rewrite Z.mod_small by lia; lia).
assert (SHF : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_of_addr SHADOW_OFF x < spZ regs - 16) by (intros x Hx; unfold shadow_of_addr, SHADOW_OFF; split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ]; pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia).
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO) as HROT.
eapply SRr_mono.
{ eapply (TRIVAL fx ly S W regsT memT mdT ch e r d s c).
- eapply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 ch HJ).
+ rewrite UspT. lia.
+ reflexivity.
+ lia.
+ rewrite WR. lia.
+ rewrite WR, WS. lia.
+ rewrite T1. exact Hra.
+ unfold raZ. rewrite T1. exact Hra4.
+ rewrite T3. exact Hgp.
+ rewrite T4. exact Htp.
+ unfold s0Z. rewrite T8, UspT.
apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) _ ch (spZ regs) Hch); [lia | lia |].
intros a Ha. apply (sk_view_kept _ mem memT (spZ regs - 16) (spZ regs) a KEPT). rewrite Z.mod_small by lia. lia.
- exact HROT.
- rewrite T10. exact H10.
- exact Re.
- exact He8.
- intros _.
split; [lia|]. split; [apply (in_app_sub (e + 8) 32); [exact Hia | lia | lia | lia]|].
split; [unfold off_img in *; lia|].
split.
{ apply (range_addressable_agree (aview SEGS (w_H W) mem)).
- intros x Hx. apply (sk_view_kept _ mem memT (spZ regs - 16) (spZ regs) _ KEPT).
pose proof (SHF x ltac:(lia)) as Hs. rewrite Z.mod_small by lia. lia.
- eapply range_addressable_sub; [exact Hrad | lia | lia]. }
split; [intros a Ha; apply (sk_apresent_kept _ mem memT (spZ regs - 16) (spZ regs) a KEPT); [apply FAR; lia | apply Hpr; lia]|].
split; [exact Rr|]. split; [exact Rd|]. split; [exact Rs|]. split; [exact Rc|].
split; [apply (sk_val_mem_kept _ mem memT (spZ regs - 16) (spZ regs) _ _ _ KEPT); [intros k Hk; apply FAR; lia | exact M8]|].
split; [apply (sk_val_mem_kept _ mem memT (spZ regs - 16) (spZ regs) _ _ _ KEPT); [intros k Hk; apply FAR; lia | exact M12]|].
split; [apply (sk_val_mem_kept _ mem memT (spZ regs - 16) (spZ regs) _ _ _ KEPT); [intros k Hk; apply FAR; lia | exact M16]|].
apply (sk_val_mem_kept _ mem memT (spZ regs - 16) (spZ regs) _ _ _ KEPT); [intros k Hk; apply FAR; lia | exact M20]. }
cbv beta. intros W2 c2 _ Hpost.
unfold treac_rival_kind_of_post, apost_base in Hpost.
destruct Hpost as (fq2 & ly2 & S2 & regs2 & mem2 & md2 & Hc2 & Hfr2 & Hcsr2 & HJ2 & HP2 & HR10 & Hperm & HW2 & K2). subst c2 W2.
unfold treac_sender_kind_post. cbv beta.
exists fx. split; [intros ? _ _ _; reflexivity|]. split; [reflexivity|].
exists fq2, ly2, S2, regs2, mem2, md2.
split; [rewrite T1; reflexivity|].
split; [exact Hfr2|]. split; [exact Hcsr2|].
split.
{ rewrite UspT in HJ2.
pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJ2 ltac:(rewrite WS, WR; lia) ltac:(lia) ltac:(intros a X; exfalso; exact (inFP_nil _ X))) as HJ3. exact HJ3. }
split; [exact (aregs_preserved_trans _ _ _ HPT HP2)|].
split.
{ rewrite HR10. unfold reac_sender_kind_model. rewrite (proj2 (Z.eqb_neq e 0) He0), Hsel. reflexivity. }
split; [exact Hperm|]. split; [reflexivity|].
intros a Ha. rewrite UspT in K2. rewrite K2.
- apply KEPT. change REAC_SENDER_KIND_STK with 4224 in Ha. lia.
- change REAC_SENDER_KIND_STK with 4224 in Ha.
change REAC_RIVAL_KIND_OF_STK with 4112. lia.
Qed.
Ltac sk_go run br leafm Usp Bsp :=
lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
paj_run_tok run HS HJ SHOK Bsp; [awr_ok_tac; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Usp |];
sk_kept Usp;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
lazymatch goal with
| HS' : st_ok _ _ (setpc _ _) (restrict _ _) |- _ => idtac
| HS' : st_ok_pi _ _ ?Ex ?ss0 _, SHOK' : sh_ok _ ?Bx ?SH _ _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bx SH ss0) in
let why := lazymatch paj_tables run with (?tpi, ?tw) => psym_why_tok tpi tw K Bx Bsp SH (start K Bx Bsp SH ss0) end in
lazymatch why with
| SR_jalr _ => leafm
| SR_branch _ _ _ => psrr_branch_tok run br HS' SHOK' Bsp; [sk_go run br leafm Usp Bsp | sk_go run br leafm Usp Bsp]
end end end.
Ltac sk_leaf ret fq FK FC ly S Perm Hra Hsegs HAE E1 modelt :=
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
let R10 := fresh "R10" in let R1 := fresh "R1" in
prreg HS (10%bv : bv 5) R10; prreg HS (1%bv : bv 5) R1;
eapply (ret _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat';
unfold treac_sender_kind_post; cbv beta;
exists fq; split; [FK|]; split; [FC|]; apply apost_base_same_fx;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS);
  [repeat first [exact HAE | apply rk_agree_ewset; [cbv; lia|]] | vm_compute; reflexivity]|];
split; [cbn [ms_regs]; rewrite R10; modelt|];
split; [Perm|]; split; [reflexivity|];
lazymatch goal with K : forall x : word, ~ _ -> _ x = _ x |- _ =>
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; apply K; change REAC_SENDER_KIND_STK with 4224 in Hx; lia end
end.
Lemma sk_walk : forall ly S W (regs : bvmap 5 word) mem md ch (e now fps r d s c fs : Z),
afn_pre SEGS B REAC_SENDER_KIND_STK ly S W regs mem md ch ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 e -> 0 <= e < 2 ^ 64 -> e mod 8 = 0 ->
getr regs 11 = w64 now -> 0 <= now < 2 ^ 64 ->
getr regs 12 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
(e <> 0 ->
e + 40 <= 2 ^ 63 /\ in_app (e + 8) 32 /\ off_img (e + 8) 32 /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (e + 8) 32 /\
(forall a, e + 8 <= a < e + 40 -> apresent (w_H W) mem a) /\
-2 ^ 31 <= r < 2 ^ 31 /\ 0 <= d < 2 ^ 8 /\ 0 <= s < 2 ^ 8 /\ 0 <= c < 2 ^ 32 /\ 0 <= fs < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 8) 4 r /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 12) 1 d /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 16) 1 s /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 20) 4 c /\
val_mem SEGS (mrestrict (w_H W) mem) (e + 32) 8 fs) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_sender_kind) regs mem md)
(treac_sender_kind_post fx regs ly S W mem md e now r d s c fs).
Proof.
intros ly S W regs mem md ch e now fps r d s c fs HPRE HRO H10 Re He8 H11 Rnow H12 Rfps HF Hra65 Hg65 Hc6 Hc3.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof (ajournal_init SEGS B REAC_SENDER_KIND_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_SENDER_KIND_STK = 4224) by reflexivity.
assert (KEPT : forall x : word, ~ (spZ regs - 16 <= bv_unsigned x < spZ regs) -> mem x = mem x) by reflexivity.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_sender_kind)) with (Z_to_bv 64 (BASE + AF_both3_reac_sender_kind)).
destruct (Z.eq_dec e 0) as [He0 | He0].
- subst e. clear HF.
destruct (sk_entry0 ly S W regs mem md ch HPRE H10) as [HS SHOK].
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
sk_go RUN BR ltac:(idtac; sk_leaf RET fx ltac:(intros ? _ _ _; reflexivity) ltac:(reflexivity) ly S ltac:(apply Permutation_refl) Hra Hsegs HAE E1 ltac:(reflexivity)) Usp Bspan_RK.
- destruct (HF He0) as (He40 & Hia & Hoi & Hrad & Hpr & Rr & Rd & Rs & Rc & Rfs & M8 & M12 & M16 & M20 & M32). clear HF.
destruct (sk_entry ly S W regs mem md ch e r d c fs HPRE H10 Re He8 Hia Hoi Hrad Rr Rd Rc Rfs M8 M12 M20 M32) as [HS SHOK].
remember (Eimg (Ereg regs (sk_extra r d c fs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (sk_extra r d c fs)) n) by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = Z_to_bv 64 now) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = getr regs 12) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 12 12%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 (r mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 d) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 c) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 fs) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (sk_extra r d c fs)) E) by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
clear HE EL.
sk_go RUN BR ltac:(idtac; sk_leaf RET fx ltac:(intros ? _ _ _; reflexivity) ltac:(reflexivity) ly S ltac:(apply Permutation_refl) Hra Hsegs HAE E1
  ltac:(repeat match goal with H : branch_taken _ _ _ = _ |- _ => sk_U r d c fs now H; revert H end; intros;
        sk_bools; unfold w64, reac_sender_kind_model; f_equal; sk_tests)) Usp Bspan_RK.
all: lazymatch goal with
| HS' : st_ok _ ?Ex (setpc _ (pa_sigma AS_reac_rival_kind_of)) (restrict _ ?msT), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  prreg HS' (1%bv : bv 5) T1; prreg HS' (2%bv : bv 5) T2; prreg HS' (3%bv : bv 5) T3; prreg HS' (4%bv : bv 5) T4;
  prreg HS' (8%bv : bv 5) T8; prreg HS' (10%bv : bv 5) T10;
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (sk_extra r d c fs) HS'
    ltac:(repeat first [exact HAE | apply rk_agree_ewset; [cbv; lia|]]) ltac:(vm_compute; reflexivity)) as HPT;
  rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS' eq_refl); cbn [ss_pc setpc]; rewrite pa_sigma_reac_rival_kind_of;
  apply (sk_tail_rival_ok ly S W regs mem md ch _ _ _ e now r d s c fs HPRE HRO HJ ltac:(assumption) HPT);
  [ rewrite T1; cbn [ew ewset Nat.eqb]; exact E1
  | rewrite T2; cbn [ew ewset Nat.eqb]; exact E2
  | rewrite T3; cbn [ew ewset Nat.eqb]; exact E3
  | rewrite T4; cbn [ew ewset Nat.eqb]; exact E4
  | rewrite T8; cbn [ew ewset Nat.eqb]; exact E8
  | rewrite T10; cbn [ew ewset Nat.eqb]; exact E10
  | exact H10 | exact Re | exact He8 | exact He0 | exact He40 | exact Hia | exact Hoi | exact Hrad | exact Hpr
  | exact Rr | exact Rd | exact Rs | exact Rc | exact M8 | exact M12 | exact M16 | exact M20
  | repeat match goal with H : branch_taken _ _ _ = _ |- _ => sk_U r d c fs now H; revert H end;
    destruct (d =? 0), (r =? 1), (r =? 2); cbn [negb orb]; intros; first [reflexivity | discriminate] ]
| _ => idtac
end.
lazymatch goal with HS' : st_ok _ ?Ex (setpc ?ssc (pa_sigma AS_reac_master_only_cadence_ns)) (restrict _ ?msc) |- _ =>
prreg HS' (1%bv : bv 5) Q1; prreg HS' (2%bv : bv 5) Q2; prreg HS' (3%bv : bv 5) Q3; prreg HS' (4%bv : bv 5) Q4;
prreg HS' (10%bv : bv 5) Q10;
pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS' eq_refl) as Hms;
rewrite Hms in HS' |- *; clear Hms; cbn [ss_pc setpc] in HS' |- *;
rewrite restrict_mkst_fx in HS';
rewrite pa_sigma_reac_master_only_cadence_ns;
set (regsc := ms_regs msc) in *; set (memc := ms_mem msc) in *; rename HS' into HSc
end.
assert (Qsp : spZ regsc = spZ regs + -16).
{ unfold spZ at 1. rewrite Q2. cbn [ew ewset Nat.eqb]. rewrite Usp. apply unsigned_lit_small. lia. }
assert (HRA : getr regsc 1 = Z_to_bv 64 (BASE + 34400)) by (rewrite Q1; reflexivity).
pose proof (pa_base_lo (PL := PL_both3_0) (PI := PI)) as HBlo. pose proof (@pa_B_ok _ _ PI) as HBok.
unfold YImgTop.IMG_LO in HBlo.
assert (FAR : forall a, 0 <= a < spZ regs - 16 -> ~ (spZ regs - 16 <= a mod 2 ^ 64 < spZ regs)) by (intros a Ha; rewrite Z.mod_small by lia; lia).
assert (Hsp46 : 2 ^ 46 <= spZ regs - 4224) by (revert Hceil Hslo C1 WS; clear; intros; lia).
pose proof (pa_obj_img_all 65 ltac:(vm_compute; lia)) as HO65. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HO65.
pose proof (pa_hi_img 99 ltac:(vm_compute; lia)) as HH99. pose proof (pa_hi_img 98 ltac:(vm_compute; lia)) as HH98.
unfold YImgTop.IMG_TOP in HH99, HH98.
eapply SRr_bind.
{ eapply (TMOC fx ly S W regsc memc _ [] fps).
- eapply (afn_pre_at SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (-16) [] HJ).
+ rewrite FpStep.fp_spZ_upd by (cbv; lia). exact Qsp.
+ reflexivity.
+ lia.
+ unfold REAC_MASTER_ONLY_CADENCE_NS_STK, ReacRateSnap.REAC_RATE_SNAP_STK, ESTACK. lia.
+ rewrite WS. unfold REAC_MASTER_ONLY_CADENCE_NS_STK, ReacRateSnap.REAC_RATE_SNAP_STK, ESTACK. lia.
+ rewrite FpStep.fp_getr_upd by (cbv; lia). rewrite HRA. apply ret_ok_codeptr_v; [lia | reflexivity].
+ unfold raZ. rewrite FpStep.fp_getr_upd by (cbv; lia). rewrite HRA, unsigned_lit_small by lia. lia.
+ rewrite FpStep.fp_getr_upd by (cbv; lia). rewrite Q3. cbn [ew ewset Nat.eqb]. rewrite E3. exact Hgp.
+ rewrite FpStep.fp_getr_upd by (cbv; lia). rewrite Q4. cbn [ew ewset Nat.eqb]. rewrite E4. exact Htp.
+ unfold s0Z. rewrite sk_getr_upd8, unsigned_lit_small by lia. apply achain_low. lia.
- exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HRO).
- rewrite Q10. cbn [ew ewset Nat.eqb]. rewrite E12. exact H12.
- exact Rfps.
- apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Hra65].
intros x Hx. apply (sk_view_kept _ mem memc (spZ regs - 16) (spZ regs) _ KEPT).
unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_le_upper_bound x 8 (2 ^ 25) ltac:(lia) ltac:(lia)). pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
rewrite Z.mod_small by lia. lia.
- apply (sk_garr8_kept _ mem memc (spZ regs - 16) (spZ regs) _ _ KEPT); [|exact Hg65].
intros j Hj. change (length (map (fun b : byte => bv_unsigned b) RATES)) with 12%nat in Hj. apply FAR. lia.
- apply (sk_val_mem_kept _ mem memc (spZ regs - 16) (spZ regs) _ _ _ KEPT); [|exact Hc6].
intros k Hk. apply FAR. lia.
- apply (sk_val_mem_kept _ mem memc (spZ regs - 16) (spZ regs) _ _ _ KEPT); [|exact Hc3].
intros k Hk. apply FAR. lia. }
cbv beta. intros W2 c2 _ (fq' & FK & FC & fq2 & ly2 & S2 & regs2 & mem2 & md2 & Hcf & Hfr2 & Hcsr2 & HJm & HPm & HAm & Hpm & HWm & Km).
subst c2 W2.
rewrite Qsp in HJm, Km.
pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HJm
ltac:(rewrite WS; unfold REAC_MASTER_ONLY_CADENCE_NS_STK, ReacRateSnap.REAC_RATE_SNAP_STK, ESTACK; lia) ltac:(lia)
ltac:(intros a X; exfalso; exact (inFP_nil _ X))) as HJ3.
cbn [app] in HJ3. change (0 + 0) with 0 in HJ3. clear HJ HJm. rename HJ3 into HJ.
pose proof (FpStep.fp_st_ok_fx SEGS fx fq2 _ _ _ _ _ _ HSc) as HSq. clear HSc.
jafter_call_keep_pi HSq 37%nat regs2 (mrestrict (w_H W) mem2) HPm [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_cons; [|apply Forall_nil].
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; cbn [ew ewset Nat.eqb]; rewrite Usp; intros a Ha.
- unfold mbyte, mrestrict. rewrite (Km (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by lia. unfold REAC_MASTER_ONLY_CADENCE_NS_STK, ReacRateSnap.REAC_RATE_SNAP_STK, ESTACK. lia.
- intros _. apply (apresent_writable SEGS). pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJp & _). apply HJp. lia. }
pose proof (sk_kept_join mem memc mem2 _ _ _ _ (spZ regs - 4224) (spZ regs) KEPT Km
ltac:(lia) ltac:(lia) ltac:(unfold REAC_MASTER_ONLY_CADENCE_NS_STK, ReacRateSnap.REAC_RATE_SNAP_STK, ESTACK; lia) ltac:(lia)) as KEPT3.
clear KEPT Km. rename KEPT3 into KEPT.
clear HSq. rewrite <- restrict_mkst_fx in HS2. rewrite HRA.
remember (havoc E 37 (map (getr regs2) CLOB)) as E' eqn:HE' in HS2.
assert (HEI' : img_env VAL A_LIM E') by (rewrite HE'; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (HAE' : env_agree 32 (Ereg regs (sk_extra r d c fs)) E') by (rewrite HE'; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (E1' : ew E' 1 = getr regs 1) by (rewrite HE', ew_havoc_old by lia; exact E1).
assert (Usp' : bv_unsigned (ew E' 2) = spZ regs) by (rewrite HE', ew_havoc_old by lia; exact Usp).
assert (A41 : ew E' 41 = getr regs2 10) by (rewrite HE'; reflexivity).
assert (E11' : ew E' 11 = Z_to_bv 64 now) by (rewrite HE', ew_havoc_old by lia; exact E11).
assert (E35' : ew E' 35 = Z_to_bv 64 fs) by (rewrite HE', ew_havoc_old by lia; exact E35).
clear HE'.
lazymatch type of HS2 with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS2 end.
repeat match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end.
assert (SHOK' : sh_ok SEGS Bx_RK0 [] E' (mrestrict (w_H W) mem2)) by constructor.
sk_go (paj_run (fx := fq2) (PL := PL_both3_0) (PI := PI) B LAWS) (paj_branch (fx := fq2) (PI := PI))
ltac:(idtac; lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  pose proof (st_ok_pi_restrict_reg _ _ _ _ 10%bv HS) as R10;
  let e := eval vm_compute in (sr_get (ss_regs ssx) 10%bv) in change (sr_get (ss_regs ssx) 10%bv) with e in R10;
  cbn [ms_regs restrict mkst] in R10;
  prreg HS (1%bv : bv 5) R1;
  eapply (paj_ret_at (fx := fq2) (PL := PL_both3_0) (PI := PI) _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  unfold treac_sender_kind_post; cbv beta;
  exists fq'; split; [exact FK|]; split; [exact FC|];
  exists fq2, ly2, S2, (ms_regs msc), (ms_mem msc); eexists;
  split; [cbn [ms_regs]; rewrite R1, E1', Hra; reflexivity|];
  split; [exact Hfr2|]; split; [exact Hcsr2|];
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ _ _ HS);
    [repeat first [exact HAE' | apply rk_agree_ewset; [cbv; lia|]] | vm_compute; reflexivity]|];
  split; [cbn [ms_regs]; rewrite R10;
    repeat match goal with H : branch_taken _ _ _ = _ |- _ => sk_U r d c fs now H; revert H end; intros; sk_bools;
    rewrite denot_lit_U; unfold w64; f_equal;
    rewrite (sk_post_U _ now fs) by first [cbn [ew ewset Nat.eqb]; rewrite A41; exact HAm | cbn [ew ewset Nat.eqb]; assumption | lia];
    unfold reac_sender_kind_model; sk_tests|];
  split; [exact Hpm|]; split; [reflexivity|];
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; apply KEPT; change REAC_SENDER_KIND_STK with 4224 in Hx; lia
end) Usp' Bspan_RK.
Qed.
End w.
Theorem pb_reac_sender_kind : treac_sender_kind_spec.
Proof. intros fq. exact (sk_walk (fx := fq)). Qed.
End h.
End f.
End d.
