(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 593 of its 625 lines of code are new or changed and 459 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalarStr.v, with its numbers changed; 586 of its 798 lines of code are new or changed and 413 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JsonScalarBase JsonScalarStr.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef StrlenDef MemchrDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Rt Require Import McConsts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Default Proof Using "All".
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Section h.
Context {B : asyms}.
Hypothesis ASTRLEN : forall fq : YK11.FPState,
  astrlen_realizesM (fx := fq) SEGS B MC_CONSTS_LO MC_CONSTS_HI (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fq : YK11.FPState,
  abcmp_realizes (fx := fq) SEGS B (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_bcmp).
Section J.
Context {fq : YK11.FPState} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W0 : world SEGS}
  {mem0 : word -> option byte} {md0 : Model} {own : list (Z * Z)} {lyc : alayout} {Sc : astate} {W : world SEGS}
  {memc : word -> option byte} {k : Z} {regs0 : bvmap 5 word} {b i n v : Z} {BS : list byte} {mdc : Model}.
Context `{JHI : @JH rc SK PI B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs0 b i n v BS mdc}.
Let LAWS : AR_laws SEGS B := jh_LAWS.
Let HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k := jh_HJ0.
Let Hvimg : off_img v 20 := jh_Hvimg.
Let Hsp16 : spZ regs0 mod 16 = 0 := jh_Hsp16.
Let HspSTK : sp0 - STK <= spZ regs0 - TJSON_SCALAR_STK := jh_HspSTK.
Let Hsp0 : spZ regs0 <= sp0 := jh_Hsp0.
Let Hv0 : 0 < v := jh_Hv0.
Let Hv8 : v mod 8 = 0 := jh_Hv8.
Let Hv63 : v + 20 <= 2 ^ 63 := jh_Hv63.
Let Hvw : spZ regs0 <= v \/ v + 20 <= spZ regs0 - TJSON_SCALAR_STK := jh_Hvw.
Let Hra : YK0s.ret_ok (getr regs0 1) := jh_Hra.
Let RUN := paj_run (fx := fq) B LAWS.
Let RUNTO := paj_run_to (fx := fq) B LAWS.
Let BR := paj_branch (fx := fq) (PI := PI).
Let HLn : Z.of_nat (length BS) = n := jh_HLn.
Let HBS : garr8 SEGS (mrestrict (w_H W) memc) b BZ := jh_HBS.
Let Hb0 : 0 < b := jh_Hb0.
Let Hbam : amem_range b n := jh_Hbam.
Let Hbw : b + n <= spZ regs0 - TJSON_SCALAR_STK \/ spZ regs0 <= b := jh_Hbw.
Let Hvam : amem_range v 20 := jh_Hvam.
Let Hvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 := jh_Hvra.
Let Hvaw : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  apresent (w_H W) memc a := jh_Hvaw.
Let Hbv : b + n <= v \/ v + 20 <= b := jh_Hbv.
Let Hbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n := jh_Hbra.
Context {t1 t2 t3 : Z}.
Hypothesis HL8 : VAL (A_OBJ 20) mod 8 = 0.
Hypothesis HLimg : forall x, VAL (A_OBJ 20) <= x < VAL (A_OBJ 20) + 24 -> in_img SEGS x.
Hypothesis HLra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (VAL (A_OBJ 20)) 24.
Hypothesis HLv1 : val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 20)) 8 t1.
Hypothesis HLv2 : val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 20) + 8) 8 t2.
Hypothesis HLv3 : val_mem SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ 20) + 16) 8 t3.
Hypothesis HS1 : jsstr_ok W memc t1 [116; 114; 117; 101].
Hypothesis HS2 : jsstr_ok W memc t2 [102; 97; 108; 115; 101].
Hypothesis HS3 : jsstr_ok W memc t3 [110; 117; 108; 108].
Hypothesis Hcv : consts_view SEGS MC_CONSTS_LO MC_CONSTS_HI W memc.
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Htp : getr regs0 4 = w64 (as_tp B).
Hypothesis Hboff : off_img b n.
Definition JS_LIT : Z := 0x3114.
Definition js_lit_spec : Prop := forall Q, JEPI_K Q -> forall R M md,
  JINV R M md -> getr R 18 = w64 (b + i) -> getr R 23 = w64 i -> getr R 26 = w64 v ->
  getr R 8 = w64 (SHADOW_OFF + (b + i) / 8) -> 0 <= i < n -> jbyte BZ i <> 34 ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_LIT)) M (seg_rom SEGS)) md) Q.
Definition litreg : YP09.region := YP09.mkRegion (Some (A_OBJ 20)) 0 24 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 46 0)); YP09.mkChunk 8 (CVal 8 (SOff 47 0)); YP09.mkChunk 16 (CVal 8 (SOff 48 0))].
Definition jlx : list word := map (Z_to_bv 64) [t1; t2; t3].
Definition JL (R : bvmap 5 word) : env := havoc (JE R i 0) 46 jlx.
Lemma jl_havoc_above : forall E kk ws q, (kk + length ws <= q)%nat -> ew (havoc E kk ws) q = ew E q.
Proof. intros E kk ws q Hq. unfold havoc. cbn [ew]. destruct (q <? kk)%nat eqn:Hlt; [reflexivity|]. apply nth_overflow. lia. Qed.
Lemma jl_low_atoms : forall R q, (q < 46)%nat -> ew (JL R) q = ew (JE R i 0) q.
Proof. intros R q Hq. unfold JL. apply ew_havoc_old. exact Hq. Qed.
Lemma jl_img : forall R, ew (JL R) (A_OBJ 20) = Z_to_bv 64 (VAL (A_OBJ 20)).
Proof. intros R. unfold JL. rewrite jl_havoc_above by (cbn; unfold A_OBJ, A_TEXT; lia). unfold JE. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM; lia. Qed.
Lemma jl_tpos : 0 < t1 < 2 ^ 63 /\ 0 < t2 < 2 ^ 63 /\ 0 < t3 < 2 ^ 63.
Proof.
destruct HS1 as (_ & _ & A1 & A2 & _). destruct HS2 as (_ & _ & B1 & B2 & _). destruct HS3 as (_ & _ & C1 & C2 & _).
cbn [length Z.of_nat] in *. lia.
Qed.
Lemma jlstate : forall R M md pc,
  JINV R M md -> getr R 26 = w64 v -> 0 <= i <= n ->
  st_ok_pi SEGS VAL (JL R) (mkSS pc sr_atoms [litreg; vreg 26; jframe; jbytes 0] None
    (mkFacts ((A_OBJ 20, mkAF 0x10000 0x5fe000 3) :: (26%nat, mkAF 1 JVHI 3) :: jatoms 0) [] []))
    (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + pc)) M (seg_rom SEGS))).
Proof.
intros R M md pc HI H26 Hin.
pose proof (jvstate R M md pc i 26 26%bv [] HI ltac:(lia) ltac:(lia) eq_refl H26 I) as HS0.
pose proof (st_ok_pi_havoc_hi 46 _ _ _ jlx HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0. fold (JL R) in HS.
pose proof HI as (HJ & HSL & HK & HPR & H2 & _).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof jl_tpos as Htp'.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam; lia).
assert (UV : bv_unsigned (ew (JL R) 26) = v) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 26 26%bv); [lia | reflexivity | exact H26 | lia]).
assert (Usp : bv_unsigned (ew (JL R) 2) = spZ regs0 - 128) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 2 2%bv); [lia | reflexivity | exact H2 | lia]).
assert (UP : bv_unsigned (ew (JL R) 45) = b + i) by (rewrite jl_low_atoms by lia; rewrite jE_P; apply unsigned_lit_small; lia).
assert (EL : ew (JL R) (A_OBJ 20) = Z_to_bv 64 (VAL (A_OBJ 20))) by apply jl_img.
assert (ET1 : ew (JL R) 46 = Z_to_bv 64 t1) by (unfold JL; exact (ew_havoc_new _ 46 jlx 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (ET2 : ew (JL R) 47 = Z_to_bv 64 t2) by (unfold JL; exact (ew_havoc_new _ 46 jlx 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (ET3 : ew (JL R) 48 = Z_to_bv 64 t3) by (unfold JL; exact (ew_havoc_new _ 46 jlx 2 (Z_to_bv 64 0) ltac:(cbn; lia))).
pose proof (pa_val_range (A_OBJ 20)) as HLr.
pose proof (HLimg (VAL (A_OBJ 20)) ltac:(lia)) as HLi0. pose proof (pa_segs_low _ HLi0) as HLlo.
pose proof (HLimg (VAL (A_OBJ 20) + 23) ltac:(lia)) as HLi1. pose proof (pa_segs_low _ HLi1) as HLhi.
assert (UL : base_val (JL R) (Some (A_OBJ 20)) = VAL (A_OBJ 20)) by (cbn [base_val]; rewrite EL; apply unsigned_lit_small; lia).
pose proof (pa_img_range _ HLi0) as HLR0. pose proof (pa_img_range _ HLi1) as HLR1.
try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HLR0, HLR1).
apply (st_ok_pi_add_fact _ _ _ (A_OBJ 20) (mkAF 0x10000 0x5fe000 3)) in HS.
2:{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EL, unsigned_lit_small by lia. change (2 ^ 3) with 8. lia. }
apply (st_ok_pi_add_region _ _ _ litreg) in HS.
- jnorm HS. exact HS.
- reflexivity.
- unfold region_ok, litreg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite UL.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  assert (KL : forall a, VAL (A_OBJ 20) <= a < VAL (A_OBJ 20) + 24 -> aview SEGS (w_H W) M a = aview SEGS (w_H W) memc a).
  { intros a Ha. pose proof (pa_segs_low _ (HLimg a Ha)). apply HK; lia. }
  repeat apply Forall_cons; try apply Forall_nil.
  + refine (chunk_ok_val SEGS _ _ _ 0 8 (SOff 46 0) t1 _ _ _ _);
    [cbn [sv_denot]; rewrite ET1, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia | cbn; lia |].
    rewrite Z.add_0_r. apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc M); [intros x Hx; apply KL; lia | exact HLv1].
  + refine (chunk_ok_val SEGS _ _ _ 8 8 (SOff 47 0) t2 _ _ _ _);
    [cbn [sv_denot]; rewrite ET2, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia | cbn; lia |].
    apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc M); [intros x Hx; apply KL; lia | exact HLv2].
  + refine (chunk_ok_val SEGS _ _ _ 16 8 (SOff 48 0) t3 _ _ _ _);
    [cbn [sv_denot]; rewrite ET3, unsigned_lit_small, Z.add_0_r by lia; reflexivity | lia | cbn; lia |].
    apply (val_mem_aview_kept_x SEGS (w_H W) (w_H W) memc M); [intros x Hx; apply KL; lia | exact HLv3].
- cbn [ss_mem add_atom all_disjoint]. unfold extent_disjoint, litreg, vreg, jframe, jbytes.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite EL, (unsigned_lit_small (VAL (A_OBJ 20))) by lia.
  rewrite UV, Usp, UP. pose proof Hvimg as Hvo. unfold off_img in Hvo. try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hvo).
  pose proof alloc_ceiling_val as Hcl. pose proof Hboff as Hbo. unfold off_img in Hbo. try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hbo).
  repeat split; lia.
Qed.
Lemma jl_shok : forall E M, JKEEP M ->
  bv_unsigned (ew E 9) = SHADOW_OFF -> bv_unsigned (ew E 26) = v -> ew E (A_OBJ 20) = Z_to_bv 64 (VAL (A_OBJ 20)) ->
  sh_ok SEGS (SOff 9 0) [mkSHE 26 0 20; mkSHE (A_OBJ 20) 0 24] E (mrestrict (w_H W) M).
Proof.
intros E M HK U9 U26 EL.
pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam; lia).
pose proof (pa_val_range (A_OBJ 20)) as HLr.
pose proof (HLimg (VAL (A_OBJ 20)) ltac:(lia)) as HLi0. pose proof (HLimg (VAL (A_OBJ 20) + 23) ltac:(lia)) as HLi1.
pose proof (pa_segs_low _ HLi0) as HLlo. pose proof (pa_segs_low _ HLi1) as HLhi.
pose proof (pa_img_range _ HLi0) as HLR0. pose proof (pa_img_range _ HLi1) as HLR1.
try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HLR0, HLR1).
assert (UB : U E (SOff 9 0) = SHADOW_OFF) by (rewrite U_SOff, U9, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia).
constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) M E (SOff 9 0) 26 v 20 v 0 20).
  + apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) M) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s Hs Hn; apply HK; assumption | lia | lia | lia | exact Hvra].
  + exact UB.
  + rewrite U_SOff, U26, Z.add_0_r; apply zcanon_id; unfold M64; lia.
  + lia.
  + lia.
  + intros x Hx. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF in *. lia.
- apply (shent_ok_of_range SEGS (w_H W) M E (SOff 9 0) (A_OBJ 20) (VAL (A_OBJ 20)) 24 (VAL (A_OBJ 20)) 0 24).
  + apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) M) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s Hs Hn; apply HK; assumption | lia | lia | lia | exact HLra].
  + exact UB.
  + rewrite U_SOff, EL, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id; unfold M64; lia.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
Lemma jl_low : forall a, in_img SEGS a -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0).
Proof.
intros a Ha. pose proof (pa_segs_low a Ha). pose proof jwin_lo as Hwl. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). lia.
Qed.
Lemma jl_arr : forall H m a L (t : nat), garr8 SEGS (mrestrict H m) a L -> (t < length L)%nat ->
  aview SEGS H m (a + Z.of_nat t) = Some (nth t L 0).
Proof.
intros H m a L t HG Ht. destruct (HG t Ht) as [Hv Hr]. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv.
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite le_byte_1_0 by lia. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.
Lemma jl_ecall : forall regsT memT mdT raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k -> spZ regsT = spZ regs0 - 128 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  ecall_pre SEGS B lyc Sc W regsT memT mdT.
Proof.
intros regsT memT mdT raw HJ Hsp Hgp' Htp' Hra' Hraw.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
apply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k regsT (spZ regs0 - 128 - sp0) HJ);
  [lia | pose proof Hsp16 as Hs16; clear - Hal16 Hs16; Z.div_mod_to_equations; lia | lia | lia | rewrite Hra'; exact Hraw | exact Hgp' | exact Htp'].
Qed.
Lemma jl_strlen : forall regsT memT mdT x (s : list Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k -> JKEEP memT ->
  jsstr_ok W memc x s ->
  getr regsT 10 = w64 x -> spZ regsT = spZ regs0 - 128 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdT)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (Z.of_nat (length s)) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - ESTACK <= a < spZ regsT) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros regsT memT mdT x s raw HJ HK Hs Ha0 Hsp Hgp' Htp' Hra' Hraw.
pose proof pa_segs_low as Hsegs. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as Hcl.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct Hs as (Hc256 & Hg & Hx0 & Hx63 & Hx32 & Ham & Hxra & Hxhull & Htail & Hximg).
assert (Hxi : forall a, x <= a < x + Z.of_nat (length s) + 1 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0))
  by (intros a Ha; apply jl_low; apply Hximg; lia).
assert (Hxlo : x + Z.of_nat (length s) + 1 <= kLowMemEnd)
  by (pose proof (Hsegs (x + Z.of_nat (length s)) (Hximg (x + Z.of_nat (length s)) ltac:(lia))); lia).
pose proof (jl_ecall regsT memT mdT raw HJ Hsp Hgp' Htp' Hra' Hraw) as HPRE.
assert (Hrd : forall t, (t < length s + 1)%nat -> aview SEGS (w_H W) memT (x + Z.of_nat t) = Some (nth t (s ++ [0]) 0)).
{ intros t Ht. destruct (Hxi (x + Z.of_nat t) ltac:(lia)) as [Ha1' Ha2']. rewrite (HK _ Ha1' Ha2').
  apply jl_arr; [exact Hg | rewrite length_app; cbn [length]; lia]. }
eapply SRr_mono.
{ apply (ASTRLEN fq lyc Sc W regsT memT mdT x (Z.of_nat (length s)) HPRE Ha0 Hx0 ltac:(lia) ltac:(lia) ltac:(lia)).
  - split; [lia|]. split.
    + intros t Ht. replace (x + t) with (x + Z.of_nat (Z.to_nat t)) by lia. rewrite Hrd by lia.
      eexists; split; [reflexivity|]. rewrite app_nth1 by lia.
      rewrite Forall_forall in Hc256.
      pose proof (Hc256 (nth (Z.to_nat t) s 0) (@nth_In _ (Z.to_nat t) s 0 ltac:(lia))). lia.
    + intros _. rewrite Hrd by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - intros a Ha. split; [|rewrite Hsp; lia].
    replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia. rewrite Hrd by lia. discriminate.
  - exact Ham.
  - apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s' Hs' Hn; apply HK; assumption | lia | lia | lia | exact Hxra].
  - apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s' Hs' Hn; apply HK; assumption | lia | lia | lia | lia | exact Hxhull].
  - intros a Ha. rewrite HK by (Z.div_mod_to_equations; lia). apply Htail. exact Ha.
  - apply (consts_view_keep SEGS _ _ W memc memT Hcv). intros a Ha. unfold MC_CONSTS_LO, MC_CONSTS_HI in Ha.
    apply HK; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra'; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS Hsegs STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k mem2 md2
    (fun a => spZ regsT - ESTACK <= a < spZ regsT) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
Hypothesis Hbhull : shadow_hull_vis (aview SEGS (w_H W) memc) b n.
Lemma jl_hull_sub : forall (rd : Z -> option Z) a nn a' n', 0 <= a -> a <= a' -> 0 < n' -> a' + n' <= a + nn ->
  shadow_hull_vis rd a nn -> shadow_hull_vis rd a' n'.
Proof.
intros rd a nn a' n' H0 H1 H2 H3 H s Hs. apply H. unfold shadow_addr in *.
assert (M : forall x y, x <= y -> (SHADOW_OFF + x / 8) / 8 * 8 <= (SHADOW_OFF + y / 8) / 8 * 8).
{ intros x y Hxy. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
pose proof (M a a' H1). pose proof (M (a' + n' - 1) (a + nn - 1) ltac:(lia)). lia.
Qed.
Lemma jprefix_iff : forall (s L : list Z), (length s <= length L)%nat ->
  (jprefix s L = true <-> forall t, (t < length s)%nat -> nth t L 0 = nth t s 0).
Proof.
induction s as [|a s IH]; intros L HL; cbn [jprefix length] in *.
- split; [intros _ t Ht; lia | reflexivity].
- destruct L as [|c L]; cbn [length] in HL; [lia|].
  rewrite Bool.andb_true_iff, Z.eqb_eq, (IH L ltac:(lia)). split.
  + intros [-> Hr] [|t] Ht; cbn [nth]; [reflexivity | apply Hr; lia].
  + intros Hall. split; [symmetry; exact (Hall 0%nat ltac:(lia))|].
    intros t Ht. exact (Hall (Datatypes.S t) ltac:(lia)).
Qed.
Lemma jl_bview : forall M, JKEEP M -> forall t, 0 <= t < n -> aview SEGS (w_H W) M (b + t) = Some (jbyte BZ t).
Proof.
intros M HK t Ht. pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
rewrite HK by lia. replace (b + t) with (b + Z.of_nat (Z.to_nat t)) by lia.
unfold jbyte. apply jl_arr; [exact HBS|]. pose proof jlen_BZ as HL. unfold jlen in HL. lia.
Qed.
Lemma jl_bcmp : forall regsT memT mdT p (s : list Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdT k -> JKEEP memT ->
  jsstr_ok W memc p s -> 0 <= i -> i + Z.of_nat (length s) <= n ->
  getr regsT 10 = w64 (b + i) -> getr regsT 11 = w64 p -> getr regsT 12 = w64 (Z.of_nat (length s)) ->
  spZ regsT = spZ regs0 - 128 ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
     c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
     aregs_preserved regsT regs2 /\
     (getr regs2 10 = w64 0 <-> jprefix s (skipn (Z.to_nat i) BZ) = true) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros regsT memT mdT p s raw HJ HK Hs Hi0 Hin Ha0 Ha1 Ha2 Hsp Hgp' Htp' Hra' Hraw.
pose proof pa_segs_low as Hsegs. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl. pose proof jb_hi as Hbhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as Hcl.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct Hs as (Hc256 & Hg & Hx0 & Hx63 & Hx32 & Ham & Hxra & Hxhull & Htail & Hximg).
assert (Hxi : forall a, p <= a < p + Z.of_nat (length s) + 1 -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0))
  by (intros a Ha; apply jl_low; apply Hximg; lia).
assert (Hxlo : p + Z.of_nat (length s) + 1 <= kLowMemEnd)
  by (pose proof (Hsegs (p + Z.of_nat (length s)) (Hximg (p + Z.of_nat (length s)) ltac:(lia))); lia).
assert (Hrd : forall t, (t < length s + 1)%nat -> aview SEGS (w_H W) memT (p + Z.of_nat t) = Some (nth t (s ++ [0]) 0)).
{ intros t Ht. destruct (Hxi (p + Z.of_nat t) ltac:(lia)) as [Ha1' Ha2']. rewrite (HK _ Ha1' Ha2').
  apply jl_arr; [exact Hg | rewrite length_app; cbn [length]; lia]. }
pose proof Hbam as Hbm. unfold amem_range in Hbm, Ham.
eapply SRr_mono.
{ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS Hsegs (@pa_sigma _ disco_listing PI DS___interceptor_trampoline_bcmp) (ABCMP fq) W regsT memT
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdT k (b + i) p (Z.of_nat (length s)) (spZ regs0 - 128 - sp0) raw HJ);
  [ exact Ha0 | exact Ha1 | exact Ha2 | lia | lia | lia | lia | lia | lia
  | pose proof Hsp16 as Hs16; clear - Hal16 Hs16; Z.div_mod_to_equations; lia | lia | lia
  | exact Hgp' | exact Htp' | exact Hra' | exact Hraw
  | intros a Ha; split; [replace a with (b + (a - b)) by lia; rewrite (jl_bview memT HK (a - b)) by lia; discriminate | rewrite Hsp; lia]
  | intros a Ha; split; [replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia; rewrite Hrd by lia; discriminate | rewrite Hsp; lia]
  | intros a Ha; lia | intros a Ha; lia
  | unfold amem_range; lia | unfold amem_range; lia
  | apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s' Hs' Hn; apply HK; assumption | lia | lia | lia | apply (range_addressable_sub _ _ b n); [exact Hbra | lia | lia]]
  | intros Hn0; apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s' Hs' Hn; apply HK; assumption | lia | lia | lia | lia | apply (jl_hull_sub _ b n); [lia | lia | lia | lia | exact Hbhull]]
  | apply (range_addressable_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s' Hs' Hn; apply HK; assumption | lia | lia | lia | apply (range_addressable_sub _ _ p (Z.of_nat (length s) + 1)); [exact Hxra | lia | lia]]
  | intros Hn0; apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) memc) (aview SEGS (w_H W) memT) (spZ regs0 - TJSON_SCALAR_STK) (spZ regs0));
    [intros s' Hs' Hn; apply HK; assumption | lia | lia | lia | lia | apply (jl_hull_sub _ p (Z.of_nat (length s) + 1)); [lia | lia | lia | lia | exact Hxhull]] ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vres & -> & HJ2 & HP & Hr10 & Hcmp & Hfr & Hpres2).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [|split; [rewrite <- Hsp in Hfr; replace (spZ regs0 - 128 - sp0) with (spZ regsT - sp0) in Hfr by lia;
  intros a Ha Hna; apply Hfr; [exact Ha | lia] | exact Hpres2]].
rewrite Hr10, Hcmp. pose proof jlen_BZ as HL. unfold jlen in HL.
rewrite jprefix_iff by (rewrite length_skipn; lia). split.
- intros Hall t Ht. specialize (Hall (Z.of_nat t) ltac:(lia)).
  replace (b + i + Z.of_nat t) with (b + (i + Z.of_nat t)) in Hall by lia.
  rewrite (jl_bview memT HK (i + Z.of_nat t)) in Hall by lia.
  rewrite Hrd in Hall by lia. rewrite app_nth1 in Hall by lia. injection Hall as Hall.
  rewrite nth_skipn. unfold jbyte in Hall. rewrite <- Hall. f_equal. lia.
- intros Hall t Ht. replace (b + i + t) with (b + (i + t)) by lia. rewrite (jl_bview memT HK (i + t)) by lia.
  replace (p + t) with (p + Z.of_nat (Z.to_nat t)) by lia. rewrite Hrd by lia. rewrite app_nth1 by lia.
  f_equal. rewrite <- (Hall (Z.to_nat t) ltac:(lia)). rewrite nth_skipn. unfold jbyte. f_equal. lia.
Qed.
Lemma jkeep_callw : forall (memT mem2 : word -> option byte) w, 0 <= w <= 2 * ESTACK -> JKEEP memT ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 128 - w <= a < spZ regs0 - 128) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) -> JKEEP mem2.
Proof.
intros memT mem2 w Hw HK Hf a Ha Hn. assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hf by lia. apply HK; assumption.
Qed.
Lemma jkept_regionw : forall Eh (memT mem2 : word -> option byte) w,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 128 - w <= a < spZ regs0 - 128) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
  forall (nb : nat) base lo hi wlo whi cs, bv_unsigned (ew Eh nb) = base ->
  (forall a, base + lo <= a < base + hi -> 0 <= a < 2 ^ 64 /\ ~ (spZ regs0 - 128 - w <= a < spZ regs0 - 128)) ->
  region_kept SEGS Eh (mrestrict (w_H W) memT) (mrestrict (w_H W) mem2) (YP09.mkRegion (Some nb) lo hi wlo whi cs).
Proof.
intros Eh memT mem2 w Hf Hp nb base lo hi wlo whi cs Hb Hin.
apply (region_kept_aview Eh (w_H W) memT mem2 nb base lo hi wlo whi cs Hb); [|exact Hp].
intros a Ha. destruct (Hin a Ha). apply Hf; assumption.
Qed.
Lemma Lbr_ltu_subv : forall E (na nb nk : nat) xa xb xk, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  bv_unsigned (ew E nk) = xk -> 0 <= xa - xb < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_ADD (SOff na 0) (SMd M_MUL (SOff nb 0) (SLit (-1))))) (sv_denot E (SOff nk 0))
  = (xa - xb <? xk).
Proof.
intros E na nb nk xa xb xk Ha Hb Hk Hr. pose proof (bv_unsigned_in_range 64 (ew E nk)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite branch_ltu_U, U_SAlu, U_SMd, !U_SOff, U_SLit, Ha, Hb, Hk. rewrite Hk in R. cbn [zalu_raw zmd_raw].
rewrite (zcanon_id (xk + 0)) by (unfold M64; lia). rewrite (Z.add_0_r xk). f_equal. unfold zcanon, M64. rewrite !Z.add_0_r, <- Zmult_mod, <- Zplus_mod.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma jl_model : 0 <= i < n -> jbyte BZ i <> 34 ->
  jscalar BZ i = match jlit BZ i jlit_words with Some t => Some t | None => jnum BZ i end.
Proof. intros Hi Hq. unfold jscalar. rewrite jlen_BZ, (proj2 (Z.leb_gt _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _) Hq). reflexivity. Qed.
Lemma jlit_miss_len : forall w ws, n - i < Z.of_nat (length w) -> jlit BZ i (w :: ws) = jlit BZ i ws.
Proof. intros w ws H. cbn [jlit]. rewrite jlen_BZ, (proj2 (Z.leb_gt _ _)) by lia. reflexivity. Qed.
Lemma jlit_miss_cmp : forall w ws, ~ (jprefix w (skipn (Z.to_nat i) BZ) = true) -> jlit BZ i (w :: ws) = jlit BZ i ws.
Proof. intros w ws H. cbn [jlit]. destruct (jprefix w (skipn (Z.to_nat i) BZ)); [contradiction|]. rewrite andb_false_r. reflexivity. Qed.
Lemma jlit_hit : forall w ws, Z.of_nat (length w) <= n - i -> jprefix w (skipn (Z.to_nat i) BZ) = true ->
  jlit BZ i (w :: ws) = Some (i + Z.of_nat (length w), 3, i, Z.of_nat (length w)).
Proof. intros w ws H1 H2. cbn [jlit]. rewrite jlen_BZ, (proj2 (Z.leb_le _ _)) by lia. rewrite H2. reflexivity. Qed.

Lemma jl_sh_step : forall E c, bv_unsigned (ew E 9) = SHADOW_OFF -> bv_unsigned (ew E (A_OBJ 20)) = VAL (A_OBJ 20) -> 0 <= c <= 16 ->
  sv_denot E (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_SRL (SOff (A_OBJ 20) (c + 8)) (SLit 3))) =
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_SRL (SOff (A_OBJ 20) c) (SLit 3))) (SLit 1)).
Proof.
intros E c H9 HL Hc. pose proof (pa_val_range (A_OBJ 20)) as HLr.
pose proof (HLimg (VAL (A_OBJ 20)) ltac:(lia)) as HLi0. pose proof (pa_segs_low _ HLi0) as HLlo.
pose proof (HLimg (VAL (A_OBJ 20) + 23) ltac:(lia)) as HLi1. pose proof (pa_segs_low _ HLi1) as HLhi.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite !denot_lit_U. f_equal. rewrite !U_SAlu, !U_SOff, !U_SLit, H9, HL. cbn [zalu_raw].
rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
rewrite (zcanon_id 1) by (unfold M64; lia).
rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
rewrite (zcanon_id (VAL (A_OBJ 20) + c)) by (unfold M64; lia).
rewrite (zcanon_id (VAL (A_OBJ 20) + (c + 8))) by (unfold M64; lia).
rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (D : (VAL (A_OBJ 20) + (c + 8)) / 8 = (VAL (A_OBJ 20) + c) / 8 + 1).
{ replace (VAL (A_OBJ 20) + (c + 8)) with ((VAL (A_OBJ 20) + c) + 1 * 8) by lia. apply Z.div_add. lia. }
rewrite D.
assert (B1 : 0 <= (VAL (A_OBJ 20) + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id ((VAL (A_OBJ 20) + c) / 8)) by (unfold M64; lia).
rewrite (zcanon_id ((VAL (A_OBJ 20) + c) / 8 + 1)) by (unfold M64; lia).
rewrite (zcanon_id (SHADOW_OFF + 0 + (VAL (A_OBJ 20) + c) / 8)) by (unfold M64, SHADOW_OFF; lia).
f_equal. lia.
Qed.
Definition jlwin_ok (r : YP09.region) : bool :=
  jwin_ok r || (match YP09.r_base r with Some nb => Nat.eqb nb 26 | None => false end && (0 <=? YP09.r_wlo r) && (YP09.r_whi r <=? 20)).
Lemma jl_wr : forall Eh rs, forallb jlwin_ok rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 - 128 -> bv_unsigned (ew Eh 26) = v ->
  forall a, in_wrange Eh rs a -> (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) \/ (v <= a < v + 20).
Proof.
intros Eh rs Hok H2 H26 a (r & Hin & Ha). rewrite forallb_forall in Hok. specialize (Hok r Hin).
unfold jlwin_ok in Hok. destruct (jwin_ok r) eqn:Hw.
- left. apply (jwin_std Eh [r]); [cbn; rewrite Hw; reflexivity | exact H2 | exists r; split; [left; reflexivity | exact Ha]].
- cbn [orb] in Hok. right. destruct (YP09.r_base r) as [nb|] eqn:Hb; [|discriminate].
  apply andb_prop in Hok as [Hok H1]. apply andb_prop in Hok as [H0 H0']. apply Nat.eqb_eq in H0. subst nb.
  apply Z.leb_le in H0', H1. cbn [base_val] in Ha. rewrite H26 in Ha. lia.
Qed.
Lemma jl_awr : forall Eh rs, forallb jlwin_ok rs = true -> bv_unsigned (ew Eh 2) = spZ regs0 - 128 -> bv_unsigned (ew Eh 26) = v ->
  awr_ok Eh rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
intros Eh rs Hok H2 H26 a Ha. assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
destruct (jl_wr Eh rs Hok H2 H26 a Ha) as [Hs|Hv']; [left; lia | apply Hvaw; exact Hv'].
Qed.
Lemma jl_denot_add : forall E (na nb : nat) xa xb, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb -> 0 <= xa + xb < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff na 0) (SOff nb 0)) = Z_to_bv 64 (xa + xb).
Proof.
intros E na nb xa xb Ha Hb Hr. rewrite denot_lit_U. f_equal. rewrite U_SAlu, !U_SOff, Ha, Hb, !Z.add_0_r. cbn [zalu_raw].
pose proof (bv_unsigned_in_range 64 (ew E na)) as R1. pose proof (bv_unsigned_in_range 64 (ew E nb)) as R2.
change (bv_modulus 64) with (2 ^ 64) in R1, R2. rewrite Ha in R1. rewrite Hb in R2.
rewrite (zcanon_id xa), (zcanon_id xb), (zcanon_id (xa + xb)) by (unfold M64; lia). reflexivity.
Qed.

Lemma js_lit : js_nument_spec -> js_lit_spec.
Proof.
intros HNUM Q HQ R M md HI H18 H23 H26 H8 Hin Hq.
pose proof (jlstate R M md JS_LIT HI H26 ltac:(lia)) as HS0.
pose proof (st_ok_pi_submem _ _ _ [litreg; jframe; jbytes 0] HS0 ltac:(cbn [ss_mem]; submem_tac) ltac:(vm_compute; reflexivity)) as HS.
clear HS0. jnorm HS.
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as Hcl.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam; lia).
pose proof jl_tpos as Htp'.
pose proof (pa_val_range (A_OBJ 20)) as HLr.
pose proof (HLimg (VAL (A_OBJ 20)) ltac:(lia)) as HLi0. pose proof (pa_segs_low _ HLi0) as HLlo.
pose proof (HLimg (VAL (A_OBJ 20) + 23) ltac:(lia)) as HLi1. pose proof (pa_segs_low _ HLi1) as HLhi.
pose proof (pa_img_range _ HLi0) as HLR0. pose proof (pa_img_range _ HLi1) as HLR1.
try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HLR0, HLR1).
pose proof Hvimg as Hvo. unfold off_img in Hvo. try (unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in Hvo).
assert (U2 : bv_unsigned (ew (JL R) 2) = spZ regs0 - 128) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 2 2%bv); [lia | reflexivity | exact H2 | lia]).
assert (U9 : bv_unsigned (ew (JL R) 9) = SHADOW_OFF) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]).
assert (U19 : bv_unsigned (ew (JL R) 19) = n) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 19 19%bv); [lia | reflexivity | exact H19 | lia]).
assert (U20 : bv_unsigned (ew (JL R) 20) = b) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U18 : bv_unsigned (ew (JL R) 18) = b + i) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (U23 : bv_unsigned (ew (JL R) 23) = i) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 23 23%bv); [lia | reflexivity | exact H23 | lia]).
assert (U26 : bv_unsigned (ew (JL R) 26) = v) by (rewrite jl_low_atoms by lia; apply (jU_reg R i 0 26 26%bv); [lia | reflexivity | exact H26 | lia]).
assert (U45 : bv_unsigned (ew (JL R) 45) = b + i) by (rewrite jl_low_atoms by lia; rewrite jE_P; apply unsigned_lit_small; lia).
assert (UL : bv_unsigned (ew (JL R) (A_OBJ 20)) = VAL (A_OBJ 20)) by (rewrite jl_img; apply unsigned_lit_small; lia).
assert (EL : ew (JL R) (A_OBJ 20) = Z_to_bv 64 (VAL (A_OBJ 20))) by apply jl_img.
assert (U261 : bv_unsigned (ew (JL R) 261) = VAL (A_OBJ 20)) by exact UL.
assert (ET1 : ew (JL R) 46 = Z_to_bv 64 t1) by (unfold JL; exact (ew_havoc_new _ 46 jlx 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (ET2 : ew (JL R) 47 = Z_to_bv 64 t2) by (unfold JL; exact (ew_havoc_new _ 46 jlx 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (ET3 : ew (JL R) 48 = Z_to_bv 64 t3) by (unfold JL; exact (ew_havoc_new _ 46 jlx 2 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (EF2 : ew (JL R) 2 = getr R 2) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF3 : ew (JL R) 3 = getr R 3) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF4 : ew (JL R) 4 = getr R 4) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF8 : ew (JL R) 8 = getr R 8) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF9 : ew (JL R) 9 = getr R 9) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF18 : ew (JL R) 18 = getr R 18) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF19 : ew (JL R) 19 = getr R 19) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EF20 : ew (JL R) 20 = getr R 20) by (rewrite jl_low_atoms by lia; apply jE_low; [lia | reflexivity]).
assert (EX : forall t, (t < 13)%nat -> ew (JL R) (32 + t) = getr regs0 (Z_to_bv 5 (snd (nth t JSAVED (0, 0)))))
  by (intros t Ht; rewrite jl_low_atoms by lia; apply jE_X; exact Ht).
assert (HLw : 0 <= VAL (A_OBJ 20) /\ VAL (A_OBJ 20) + 24 <= spZ regs0 - TJSON_SCALAR_STK) by lia.
pose proof (jl_model Hin Hq) as HJS.
set (E0 := JL R) in *.
assert (HEI : img_env VAL A_LIM E0) by (assert (HEJ : img_env VAL A_LIM (JE R i 0)) by apply Eimg_env;
  intros a Ha; unfold E0, JL; rewrite jl_havoc_above by (cbn; unfold A_TEXT in Ha; lia); exact (HEJ a Ha)).
assert (SHOK : sh_ok SEGS (SOff 9 0) [mkSHE 26 0 20; mkSHE (A_OBJ 20) 0 24] E0
  (mrestrict (w_H W) (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_LIT)) M (seg_rom SEGS)))))
  by (apply jl_shok; [exact MEQ | exact U9 | exact U26 | exact EL]).
set (Ec0 := E0) in HS, SHOK, HEI.
assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity).
clearbody Ec0.
change (JKEEP M) with (JKEEP (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_LIT)) M (seg_rom SEGS)))) in MEQ.
change (JPRES M) with (JPRES (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_LIT)) M (seg_rom SEGS)))) in PRS.

let rec go T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK JBspan T;
  [ lazymatch goal with
    | |- awr_ok _ _ _ _ _ _ _ _ _ => first [ apply jawr_std; [vm_compute; reflexivity | rewrite AG by lia; exact U2]
                                           | apply jl_awr; [vm_compute; reflexivity | rewrite AG by lia; exact U2 | rewrite AG by lia; exact U26] ]
    end ..
  | jpost Ecur ]
  end
with jpost Ecur :=
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    first [ let MEQ2 := fresh "MEQ" in
      pose proof (jkeep_run Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(rewrite AG by lia; exact U2) HFr MEQ) as MEQ2;
      clear MEQ HFr; rename MEQ2 into MEQ
    | let MEQV := fresh "MEQV" in
      pose proof (jkeepv_of Eh rs m1 m2 HFr (jl_wr Eh rs ltac:(vm_compute; reflexivity) ltac:(rewrite AG by lia; exact U2)
        ltac:(rewrite AG by lia; exact U26)) MEQ) as MEQV;
      clear MEQ HFr ]
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ _ |- _ => jrebase En Ecur
  | HS : st_ok _ ?En _ _ |- _ => jrebase En Ecur
  end;
  lazymatch goal with
  | HS : st_ok _ _ (setpc ?s _) _ |- _ =>
    let a0 := eval vm_compute in (sr_get (ss_regs s) (10%bv : bv 5)) in
    lazymatch a0 with
    | SOff 46%nat 0 => jstrlen t1 [116; 114; 117; 101] HS1 ET1
    | SOff 47%nat 0 => jstrlen t2 [102; 97; 108; 115; 101] HS2 ET2
    | SOff 48%nat 0 => jstrlen t3 [110; 117; 108; 108] HS3 ET3
    | _ => let a1 := eval vm_compute in (sr_get (ss_regs s) (11%bv : bv 5)) in
      lazymatch a1 with
      | SOff 46%nat 0 => jbcmp t1 [116; 114; 117; 101] HS1 ET1
      | SOff 47%nat 0 => jbcmp t2 [102; 97; 108; 115; 101] HS2 ET2
      | SOff 48%nat 0 => jbcmp t3 [110; 117; 108; 108] HS3 ET3
      end
    end; go JS_NUMENT
  | HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 12620 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv_ltu; first [exfalso; lia | go JS_NUMENT] | jcv_ltu; first [exfalso; lia | go JS_NUMENT]]
    | 12644 => psrr_branch_tok RUN BR HS SHOK JBspan; [jcv_eq; go JS_NUMENT | jcv_eq; go JS_NUMENT]
    | 12600 => jfixsh; go JS_NUMENT
    | 12820 => jaddv; go JS_EPI
    | 12740 => jexit_epi
    | 12664 => jexit_num
    end
  end
with jfixsh :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict ?Hh ?msx) |- _ =>
  let x23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
  lazymatch x23 with SAlu ALU_ADD (SAlu ALU_ADD (SOff 9%nat 0) (SAlu ALU_SRL (SOff 261%nat ?c) (SLit 3))) (SLit 1) =>
  let c8 := eval vm_compute in (c + 8) in
  let HS2 := fresh "HS" in let E23 := fresh "E23" in
  assert (E23 : sv_denot Ec (SAlu ALU_ADD (SOff 9 0) (SAlu ALU_SRL (SOff 261 c8) (SLit 3))) = getr (ms_regs msx) (23%bv : bv 5))
    by (rewrite (st_ok_pi_restrict_reg Hh _ _ _ (23%bv : bv 5) HS); change (sr_get (ss_regs ss) (23%bv : bv 5)) with x23;
        exact (jl_sh_step Ec c ltac:(rewrite AG by lia; exact U9) ltac:(rewrite AG by (cbn; lia); exact UL) ltac:(lia)));
  pose proof (ast_ok_pi_set_reg_fp _ _ _ (23%bv : bv 5) _ HS ltac:(vm_compute; reflexivity) E23) as HS2;
  clear HS E23; rename HS2 into HS; jnorm HS
  end end
with jaddv :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict ?Hh ?msx) |- _ =>
  apply (st_ok_pi_add_region _ _ _ (vreg 26)) in HS;
  [ jnorm HS
  | reflexivity
  | unfold region_ok, vreg; cbn [ms_mem restrict YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite AG by lia; rewrite U26;
    split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
    intros o Ho; apply (apresent_writable SEGS); apply PRS; apply Hvaw; lia
  | cbn [ss_mem all_disjoint]; unfold extent_disjoint, vreg; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite !AG by (cbn; lia); rewrite U26, U2, U261, U45; repeat split; lia ]
  end
with jcv_ltu :=
  lazymatch goal with Hc : branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_ADD (SOff ?na 0) (SMd M_MUL (SOff ?nb 0) (SLit (-1))))) (sv_denot _ (SOff ?nk 0)) = _,
    EKL : ew _ ?nk = w64 ?len |- _ =>
    rewrite (Lbr_ltu_subv Ex na nb nk n i len ltac:(rewrite AG by lia; exact U19) ltac:(rewrite AG by lia; exact U23)
      ltac:(rewrite EKL; unfold w64; apply unsigned_lit_small; lia) ltac:(lia)) in Hc;
    first [apply Z.ltb_lt in Hc | apply Z.ltb_ge in Hc]; let bf := fresh "BF" in rename Hc into bf
  end
with jcv_eq :=
  lazymatch goal with Hc : branch_taken BC_EQ (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit 0)) = ?bb,
    MW : ew ?Ex ?nn = ?w, HRm : (?w = w64 0 <-> ?P) |- _ =>
    lazymatch bb with
    | true => let Hm := fresh "BM" in pose proof (proj1 HRm (proj1 (Lbr_eq0 Ex nn w MW) Hc)) as Hm
    | false => let Hm := fresh "BF" in
      assert (Hm : ~ P) by (let X := fresh in intros X; apply (proj2 HRm) in X; apply (proj2 (Lbr_eq0 Ex nn w MW)) in X;
        rewrite X in Hc; discriminate Hc)
    end; clear Hc HRm MW
  end
with jrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  (let E2 := fresh "Ec" in set (E2 := En) in *;
   let AG2 := fresh "AG" in
   assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
     by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
   try (lazymatch goal with EKL : ew Ecur ?kL = ?wv |- _ =>
     let EKL2 := fresh "EKL" in
     assert (EKL2 : ew E2 kL = wv) by (subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact EKL);
     clear EKL; rename EKL2 into EKL end);
   clear AG; rename AG2 into AG)
with jstrlen tk sk HSk ETk :=
  lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX) |- _ =>
  try clear EKL;
  let K := run_K_hi HS in
  let K4 := eval vm_compute in (K + 4)%nat in
  let Ra0 := fresh "Ra0" in let Rra := fresh "Rra" in
  let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
  prreg HS (10%bv : bv 5) Ra0; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  rewrite ?AG in Ra0, Qsp, Qgp, Qtp by lia;
  let HspU := fresh "HspU" in
  assert (HspU : spZ (ms_regs msX) = spZ regs0 - 128) by (unfold spZ at 1; rewrite Qsp; exact U2);
  pmkst HS;
  let raw := lazymatch type of Rra with _ = ?r => r end in
  eapply SRr_bind;
  [ apply (jl_strlen (ms_regs msX) (ms_mem msX) _ tk sk raw HJ MEQ HSk);
    [ rewrite Ra0, ETk; reflexivity
    | exact HspU
    | rewrite Qgp, EF3, H3; exact Hgp
    | rewrite Qtp, EF4, H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity] ]
  | cbv beta;
    let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
    let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let HR := fresh "HR" in let Hfr2 := fresh "Hfr2" in
    let Hpres2 := fresh "Hpres2" in let HPP := fresh "HPP" in
    intros W2 c2 _ HPP; destruct HPP as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR & Hfr2 & Hpres2);
    rewrite HspU in Hfr2; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HR;
    let HS2 := fresh "HS" in
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
    match type of HS2 with ?tt -> _ => let HRK := fresh in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (eapply (jkept_regionw _ _ _ _ Hfr2 Hpres2); [rewrite AG by lia; eassumption | intros; lia])
    | rewrite <- restrict_mkst_fx in HS2;
      lazymatch type of HS2 with st_ok_pi _ _ ?En _ _ =>
        let E2 := fresh "Ec" in set (E2 := En) in HS2;
        let HEI2 := fresh "HEI" in let AG2 := fresh "AG" in
        let MEQ2 := fresh "MEQ" in let PRS2 := fresh "PRS" in let SHOK2 := fresh "SHOK" in
        assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc_hi; [assumption | cbv; lia]);
        assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
          by (intros kk Hkk; subst E2; rewrite ew_havoc_old by lia; apply AG; exact Hkk);
        assert (EKL : ew E2 K4 = w64 (Z.of_nat (length sk)))
          by (subst E2; change K4 with (K + 4)%nat; rewrite (ew_havoc_new _ K _ 4 (Z_to_bv 64 0)) by (cbn; lia); exact HR);
        cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in EKL;
        pose proof (jkeep_callw (ms_mem msX) mem2 ESTACK ltac:(lia) MEQ Hfr2) as MEQ2;
        assert (PRS2 : JPRES mem2) by (intros a Ha; apply Hpres2; apply PRS; exact Ha);
        assert (SHOK2 : sh_ok SEGS (SOff 9 0) [mkSHE 26 0 20; mkSHE (A_OBJ 20) 0 24] E2 (mrestrict (w_H W) mem2))
          by (apply jl_shok; [exact MEQ2 | rewrite AG2 by lia; exact U9 | rewrite AG2 by lia; exact U26 | rewrite AG2 by (cbn; lia); exact EL]);
        clearbody E2;
        clear HS HJ MEQ PRS SHOK AG Ra0 Rra Qsp Qgp Qtp HspU HP2 Hfr2 Hpres2 HR;
        repeat match goal with H : img_env _ _ ?Ex |- _ => lazymatch Ex with E2 => fail | _ => clear H end end;
        rename HS2 into HS; rename HJ2 into HJ; rename MEQ2 into MEQ; rename PRS2 into PRS; rename SHOK2 into SHOK;
        rename AG2 into AG
      end ] ]
  end
with jbcmp tk sk HSk ETk :=
  lazymatch goal with HS : st_ok _ ?Ec ?ssc (restrict (w_H W) ?msX) |- _ =>
  let K := run_K_hi HS in
  let K4 := eval vm_compute in (K + 4)%nat in
  let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let Ra2 := fresh "Ra2" in let Rra := fresh "Rra" in
  let Qsp := fresh "Qsp" in let Qgp := fresh "Qgp" in let Qtp := fresh "Qtp" in
  prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2; prreg HS (1%bv : bv 5) Rra;
  prreg HS (2%bv : bv 5) Qsp; prreg HS (3%bv : bv 5) Qgp; prreg HS (4%bv : bv 5) Qtp;
  rewrite ?AG in Ra0, Ra1, Qsp, Qgp, Qtp by lia;
  let HspU := fresh "HspU" in
  assert (HspU : spZ (ms_regs msX) = spZ regs0 - 128) by (unfold spZ at 1; rewrite Qsp; exact U2);
  pmkst HS;
  let raw := lazymatch type of Rra with _ = ?r => r end in
  let kL := lazymatch goal with EKL : ew _ ?kk = w64 _ |- _ => kk end in
  eapply SRr_bind;
  [ apply (jl_bcmp (ms_regs msX) (ms_mem msX) _ tk sk raw HJ MEQ HSk ltac:(lia) ltac:(cbn [length Z.of_nat]; lia));
    [ rewrite Ra0, EF18; exact H18
    | rewrite Ra1, ETk; reflexivity
    | rewrite Ra2, EKL; reflexivity
    | exact HspU
    | rewrite Qgp, EF3, H3; exact Hgp
    | rewrite Qtp, EF4, H4; exact Htp
    | exact Rra
    | apply ret_ok_codeptr_v; [lia | reflexivity] ]
  | cbv beta;
    let W2 := fresh "W2" in let c2 := fresh "c2" in let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
    let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let HR := fresh "HRb" in let Hfr2 := fresh "Hfr2" in
    let Hpres2 := fresh "Hpres2" in let HPP := fresh "HPP" in
    intros W2 c2 _ HPP; destruct HPP as (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HR & Hfr2 & Hpres2);
    rewrite HspU in Hfr2;
    let HS2 := fresh "HS" in
    jafter_call_keep_hi HS K regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2;
    match type of HS2 with ?tt -> _ => let HRK := fresh in assert (HRK : tt); [|specialize (HS2 HRK); clear HRK] end;
    [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
      (eapply (jkept_regionw _ _ _ _ Hfr2 Hpres2); [rewrite AG by lia; eassumption | intros; lia])
    | rewrite <- restrict_mkst_fx in HS2;
      lazymatch type of HS2 with st_ok_pi _ _ ?En _ _ =>
        let E2 := fresh "Ec" in set (E2 := En) in HS2;
        let HEI2 := fresh "HEI" in let AG2 := fresh "AG" in let MW := fresh "MW" in
        let MEQ2 := fresh "MEQ" in let PRS2 := fresh "PRS" in let SHOK2 := fresh "SHOK" in let EKL2 := fresh "EKL" in
        assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply img_env_havoc_hi; [assumption | cbv; lia]);
        assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
          by (intros kk Hkk; subst E2; rewrite ew_havoc_old by lia; apply AG; exact Hkk);
        assert (MW : ew E2 K4 = getr regs2 10)
          by (subst E2; change K4 with (K + 4)%nat; rewrite (ew_havoc_new _ K _ 4 (Z_to_bv 64 0)) by (cbn; lia); reflexivity);
        assert (EKL2 : ew E2 kL = ew Ec kL) by (subst E2; rewrite ew_havoc_old by lia; reflexivity);
        lazymatch goal with EKL : ew Ec kL = _ |- _ => rewrite EKL in EKL2; clear EKL end;
        pose proof (jkeep_callw (ms_mem msX) mem2 (2 * ESTACK) ltac:(lia) MEQ Hfr2) as MEQ2;
        assert (PRS2 : JPRES mem2) by (intros a Ha; apply Hpres2; apply PRS; exact Ha);
        assert (SHOK2 : sh_ok SEGS (SOff 9 0) [mkSHE 26 0 20; mkSHE (A_OBJ 20) 0 24] E2 (mrestrict (w_H W) mem2))
          by (apply jl_shok; [exact MEQ2 | rewrite AG2 by lia; exact U9 | rewrite AG2 by lia; exact U26 | rewrite AG2 by (cbn; lia); exact EL]);
        clearbody E2;
        clear HS HJ MEQ PRS SHOK AG Ra0 Ra1 Ra2 Rra Qsp Qgp Qtp HspU HP2 Hfr2 Hpres2;
        repeat match goal with H : img_env _ _ ?Ex |- _ => lazymatch Ex with E2 => fail | _ => clear H end end;
        rename HS2 into HS; rename HJ2 into HJ; rename MEQ2 into MEQ; rename PRS2 into PRS; rename SHOK2 into SHOK;
        rename AG2 into AG; rename EKL2 into EKL
      end ] ]
  end
with jrg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; rewrite ?AG by lia;
    first [ reflexivity | rewrite ?EF2, ?EF3, ?EF4, ?EF8, ?EF9, ?EF18, ?EF19, ?EF20; assumption ]
  end
with jlit_dec :=
  unfold jlit_words;
  repeat first [ rewrite jlit_miss_len by (cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia) | rewrite jlit_miss_cmp by assumption ];
  try (rewrite jlit_hit by (first [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; lia | assumption]));
  cbn [jlit length Z.of_nat Pos.of_succ_nat Pos.succ]
with jexit_epi :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict ?Hh ?msx) |- _ =>
  lazymatch goal with EKL : ew Ec ?kL = w64 ?len |- _ =>
  let Q10 := fresh "Q10" in let HR0 := fresh "HR0" in let UV2 := fresh "UV2" in let UK2 := fresh "UK2" in
  let U182 := fresh "U18" in let U232 := fresh "U23" in let Hv := fresh "Hv" in
  pose proof (st_ok_pi_restrict_reg Hh _ _ _ (10%bv : bv 5) HS) as Q10;
  let e10 := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in change (sr_get (ss_regs ss) (10%bv : bv 5)) with e10 in Q10;
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0; cbn [ms_mem restrict] in HR0;
  assert (UV2 : bv_unsigned (ew Ec 26) = v) by (rewrite AG by lia; exact U26);
  assert (UK2 : bv_unsigned (ew Ec kL) = len) by (rewrite EKL; unfold w64; apply unsigned_lit_small; lia);
  assert (U182 : bv_unsigned (ew Ec 18) = b + i) by (rewrite AG by lia; exact U18);
  assert (U232 : bv_unsigned (ew Ec 23) = i) by (rewrite AG by lia; exact U23);
  pmkst HS;
  apply (HQ (ms_regs msx) (ms_mem msx) _ (i + len) HJ);
  [ jrg HS | jrg HS | jrg HS
  | rewrite Q10; rewrite (jl_denot_add Ec 23 kL i len U232 UK2 ltac:(lia)); reflexivity
  | lia
  | apply (jslots_of Ec _ msx 2 _ HS eq_refl);
    [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; tauto
    | rewrite AG by lia; exact U2
    | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by lia; apply EX; exact Ht ]
  | exact PRS
  | unfold JRES; change (map bv_unsigned BS) with BZ; rewrite HJS; jlit_dec;
    split; [lia|]; split; [|split; [|split]];
    [ pose proof (field_of_region Ec _ 26 v _ 0 20 0 20 0 8 (SOff 18 0) (b + i) HR0 UV2
        ltac:(clear; cbn [In]; tauto) ltac:(rewrite (jdenot_soff Ec 18 (b + i) 0 U182); f_equal; lia) ltac:(lia) ltac:(cbn; lia)) as Hv;
      rewrite Z.add_0_r in Hv; exact Hv
    | exact (field_of_region Ec _ 26 v _ 0 20 0 20 8 8 (SOff kL 0) len HR0 UV2
        ltac:(clear; cbn [In]; tauto) ltac:(rewrite (jdenot_soff Ec kL len 0 UK2); f_equal; lia) ltac:(lia) ltac:(cbn; lia))
    | exact (field_of_region Ec _ 26 v _ 0 20 0 20 16 4 (SLit 3) 3 HR0 UV2
        ltac:(clear; cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))
    | assumption ] ]
  end end
with jexit_num :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict ?Hh ?msx) |- _ =>
  let HR1 := fresh "HR1" in
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as HR1; cbn [ms_mem restrict] in HR1;
  pmkst HS;
  apply (HNUM Q HQ (ms_regs msx) (ms_mem msx) _);
  [ split; [exact HJ|]; split;
    [ apply (jslots_of Ec _ msx 1 _ HS eq_refl);
      [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; tauto
      | rewrite AG by lia; exact U2
      | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by lia; apply EX; exact Ht ]
    | split; [exact MEQ|]; split; [exact PRS|]; repeat split; jrg HS ]
  | unfold JSLOTS2; cbv beta; split;
    [ exact (field_of_region Ec _ 2 (spZ regs0 - 128) _ 0 128 0 128 8 8 (SOff 26 0) v HR1 ltac:(rewrite AG by lia; exact U2)
        ltac:(clear; cbn [In]; tauto) ltac:(rewrite (jdenot_soff Ec 26 v 0 ltac:(rewrite AG by lia; exact U26)); f_equal; lia)
        ltac:(lia) ltac:(cbn; lia))
    | exact (field_of_region Ec _ 2 (spZ regs0 - 128) _ 0 128 0 128 16 8 (SOff 23 0) i HR1 ltac:(rewrite AG by lia; exact U2)
        ltac:(clear; cbn [In]; tauto) ltac:(rewrite (jdenot_soff Ec 23 i 0 ltac:(rewrite AG by lia; exact U23)); f_equal; lia)
        ltac:(lia) ltac:(cbn; lia)) ]
  | jrg HS | jrg HS | lia
  | rewrite HJS; jlit_dec; reflexivity ]
  end in
go JS_NUMENT.
Qed.
End J.
End h.
End f.
End d.
