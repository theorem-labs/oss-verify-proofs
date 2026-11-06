(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExsB_Sym.v, with its module paths and module names changed; 866 of its 927 lines of code are new or changed and 312 lines of the source are left out. *)
(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan pin d663f82d7f488d30): segment S_FIT of
   lib/B/Prog/TxPut102B_Base.v (tp_seg_FIT): from the rejoin TP_PC_FIT (B' 0x852d0, +256) to the epilogue TP_PC_END
   (B' 0x85360, +400).
   rule 24: proves function tx_put (reuse search: the internal file REWALK-102-PLAN.md section T3)
   *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YGcallx YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMx YGcallMxmn YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import TxPutCall102 S1Ledger TxPutKeep102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import TxPut102B_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at TP_PC_FIT ----
   atoms: 8 = t (s0), 9 = n (s1), 18 = s (s2), 22 = the shadow offset (s6), 32 = b1, 33 = len0.
   Registers: s3 = t + 8, s10 = t >> 3 and s7 = shadow (t + 8) are rebuilt as the engine's own forms, so the token
   rule of the shadow checks (YCbn.v match_x) recognises them. Region: the record's b and n words at t. *)
Definition fit_Bx : sv := SOff 22 0.
Definition fit_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition fit_rec : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 16 0 16
    [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition fit_regions : smem := [fit_rec].
Definition fit_facts : facts :=
  mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (9%nat, mkAF 0 (2 ^ 28) 0);
           (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
           (33%nat, mkAF 0 (2 ^ 28) 0)] [] [].
Definition fit_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms 19%bv (SOff 8 8)) 26%bv (SAlu ALU_SRL (SOff 8 0) (SLit 3)))
    23%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 22 0)).
Definition ss_fit : sstate := mkSS (TP_OFF + TP_PC_FIT) fit_sr fit_regions None fit_facts.
Definition fit_SH : list shent := [mkSHE 8 0 16].
(* after the stretch at +380: atom 56 = b1 + len0 + n, the NUL byte; its region (written) and its shadow entry *)
Definition fit_nul : YP09.region := YP09.mkRegion (Some 56%nat) 0 1 0 1 [].
Definition fit_SH2 : list shent := [mkSHE 8 0 16; mkSHE 56 0 1].

Section fit. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance TP_PrhImg.
#[local] Existing Instance TP_PAListing.
#[local] Existing Instance TP_RL.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Definition fit_E (regs : bvmap 5 word) (b1 len0 : Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs (map (Z_to_bv 64) [b1; len0])).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
#[local] Notation ARX := (ARcfx B).
(* callee text (YGcallMxmn.v's aintrin_realizes_xm at ARcf): __asan_memcpy, at the listing's own
   SIGMA AS___asan_memcpy *)
Hypothesis AI : aintrin_realizes_xm segs B ARX OCpy (SIGMA AS___asan_memcpy).
Let LAWS : AR_laws_x segs B ARX cf_head := AR_laws_x_xs segs B (AR_laws_ok_cf segs B).
(* the world relation of the cuts after the GROW's realloc: the FIT cut's journal and keep are at it (TxPut102B_Base.v
   tp_at_FIT), and the segment's runs, keeps and the memcpy call's composition are over it *)
#[local] Notation RW := (wle' segs YGcfRehidePost.RZ_cf).

(* the engine's shift right by 3 of a non-negative value *)
Lemma fit_srl3' : forall E x v, U E x = v -> 0 <= v ->
  U E (SAlu ALU_SRL x (SLit 3)) = v / 8.
Proof.
intros E x v Hx Hv. pose proof (U_range E x) as Hr. rewrite Hx in Hr.
rewrite U_SAlu, Hx, U_SLit. rewrite (zcanon_id 3) by (unfold M64; lia). cbn [zalu_raw].
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64 in *. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma fit_srl3 : forall E x v, U E x = v -> 0 <= v ->
  U E (SAlu ALU_SRL x (SLit 3)) = zcanon (v / 8).
Proof.
intros E x v Hx Hv. rewrite (fit_srl3' E x v Hx Hv). pose proof (U_range E x) as Hr. rewrite Hx in Hr.
symmetry. apply zcanon_id. unfold M64 in *. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma fit_entry : forall (W : world segs) regs mem t n b1 len0,
  getr regs 8 = w64 t -> getr regs 9 = w64 n -> getr regs 22 = w64 SHADOW_OFF ->
  getr regs 19 = w64 (t + 8) -> getr regs 26 = w64 (t / 8) ->
  getr regs 23 = w64 (SHADOW_OFF + (t + 8) / 8) ->
  2 ^ 46 <= t <= 2 ^ 47 - 32 -> t mod 8 = 0 -> 0 <= n <= 2 ^ 28 ->
  4096 <= b1 <= 2 ^ 47 - 2 ^ 23 -> 0 <= len0 <= 2 ^ 28 ->
  (forall a, t <= a < t + 16 -> writable_at segs (mrestrict (w_H W) mem) a) ->
  val_mem segs (mrestrict (w_H W) mem) t 8 b1 -> val_mem segs (mrestrict (w_H W) mem) (t + 8) 8 len0 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF t 16 ->
  st_ok_pi segs VAL (fit_E regs b1 len0) ss_fit
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (TP_OFF + TP_PC_FIT))) mem (seg_rom segs)))
  /\ sh_ok segs fit_Bx fit_SH (fit_E regs b1 len0) (mrestrict (w_H W) mem).
Proof.
intros W regs mem t n b1 len0 R8 R9 R22 R19 R26 R23 Ht Hta Hn Hb1 Hl Hwr Mb Ml Hra.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := fit_E regs b1 len0).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (map (Z_to_bv 64) [b1; len0])) k)
  by (intros k Hk; subst E; unfold fit_E; apply Eimg_low; exact Hk).
assert (ER : forall (r : bv 5) k, Z.of_nat k = bv_unsigned r -> ew E k = getr regs r).
{ intros r k Hk. pose proof (u5_range r) as Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ k r Hk). }
assert (E32 : ew E 32 = Z_to_bv 64 b1) by (rewrite EL by (unfold A_TEXT; lia); reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 len0) by (rewrite EL by (unfold A_TEXT; lia); reflexivity).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (rewrite (ER 8%bv 8%nat eq_refl); exact R8).
assert (E9 : ew E 9 = Z_to_bv 64 n) by (rewrite (ER 9%bv 9%nat eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 22%bv 22%nat eq_refl); exact R22).
assert (Ut : bv_unsigned (ew E 8) = t) by (rewrite E8; apply unsigned_lit_small; lia).
assert (UT0 : U E (SOff 8 0) = t) by (rewrite U_SOff, Ut, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (UT8 : U E (SOff 8 8) = t + 8) by (rewrite U_SOff, Ut; apply zcanon_id; unfold M64; lia).
assert (UB : U E (SOff 22 0) = SHADOW_OFF)
  by (rewrite U_SOff, E22, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia);
      apply zcanon_id; unfold M64, SHADOW_OFF; lia).
split.
- unfold ss_fit. apply pa_entry_st_ok_full.
  + unfold fit_sr.
    apply regs_ok_rereg; [|reflexivity|].
    { apply regs_ok_rereg; [|reflexivity|].
      { apply regs_ok_rereg; [|reflexivity|].
        { subst E. unfold fit_E. apply regs_ok_Eimg_Ereg. }
        rewrite R19. change (w64 (t + 8)) with (sv_denot E (SLit (t + 8))). apply U_inj.
        rewrite U_SLit, UT8. apply zcanon_id. unfold M64. lia. }
      rewrite R26. change (w64 (t / 8)) with (sv_denot E (SLit (t / 8))). apply U_inj.
      rewrite U_SLit, (fit_srl3 E (SOff 8 0) t UT0 ltac:(lia)). reflexivity. }
    rewrite R23. change (w64 (SHADOW_OFF + (t + 8) / 8)) with (sv_denot E (SLit (SHADOW_OFF + (t + 8) / 8))).
    apply U_inj. rewrite U_SLit, U_SAlu, (fit_srl3' E (SOff 8 8) (t + 8) UT8 ltac:(lia)), UB.
    cbn [zalu_raw]. f_equal. lia.
  + vm_compute. reflexivity.
  + unfold fit_regions, fit_rec. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Ut.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwr; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val segs E _ t 0 8 (SOff 32 0) b1); [| lia | lia |].
      { cbn [sv_denot]. rewrite E32, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
      rewrite Z.add_0_r. exact Mb.
    * apply (chunk_ok_val segs E _ t 8 8 (SOff 33 0) len0); [| lia | lia | exact Ml].
      cbn [sv_denot]. rewrite E33, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  + exact (conj I I).
  + split; [|split; exact I].
    unfold fit_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E8, E9, E22, E32, E33.
    rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF in *; lia.
- unfold sh_ok, fit_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem E fit_Bx 8%nat t 16 t 0 16 Hra).
  + unfold fit_Bx. rewrite U_SOff, E22, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    apply zcanon_id. unfold M64, SHADOW_OFF. lia.
  + rewrite U_SOff, Ut, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* ---- memory facts the walk reads off the engine ---- *)
(* the record's checked bytes, by the shadow entry fit_SH *)
Lemma fit_shok : forall E (W : world segs) mem t,
  U E (SOff 22 0) = SHADOW_OFF -> U E (SOff 8 0) = t -> 2 ^ 46 <= t <= 2 ^ 47 - 32 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF t 16 ->
  sh_ok segs fit_Bx fit_SH E (mrestrict (w_H W) mem).
Proof.
intros E W mem t UB UT Ht Hra. unfold sh_ok, fit_SH. apply Forall_cons; [|apply Forall_nil].
apply (shent_ok_of_range segs (w_H W) mem E fit_Bx 8%nat t 16 t 0 16 Hra); [exact UB | exact UT | lia | lia |].
intros x Hx. unfold SHADOW_OFF. lia.
Qed.

(* a range on the real stack is addressable at every ARx state (AR_laws_x field 13, alx_zshadow_byte) *)
Lemma fit_ra_stack : forall ly S Hp (W : world segs) mem md x m,
  ARX ly S Hp W mem md -> ly_stk_lo ly <= x -> x + m <= ly_stk_hi ly ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x m.
Proof.
intros ly S Hp W mem md x m HAR Hlo Hhi y Hy. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. apply (alx_zshadow_byte segs B ARX LAWS ly S Hp W mem md y HAR). lia.
Qed.

(* a run's frame fact (frame_of off its write windows) gives the view off any superset of the windows *)
Lemma fit_keep_frame : forall E rs (W : world segs) m m' (Wr : Z -> Prop),
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall a, in_wrange E rs a -> Wr a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview segs (w_H W) m' a = aview segs (w_H W) m a.
Proof.
intros E rs W m m' Wr HF HW a Ha Hn. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
rewrite tpk_word_small by exact Ha. intros Hi. exact (Hn (HW a Hi)).
Qed.
Lemma fit_inw1 : forall E r a, in_wrange E [r] a ->
  base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r.
Proof. intros E r a (r' & [<- | []] & H). exact H. Qed.
Lemma fit_inw2 : forall E r1 r2 a, in_wrange E [r1; r2] a ->
  (base_val E (YP09.r_base r1) + YP09.r_wlo r1 <= a < base_val E (YP09.r_base r1) + YP09.r_whi r1) \/
  (base_val E (YP09.r_base r2) + YP09.r_wlo r2 <= a < base_val E (YP09.r_base r2) + YP09.r_whi r2).
Proof. intros E r1 r2 a (r' & [<- | [<- | []]] & H); [left | right]; exact H. Qed.

(* FuzzStrdupB.v's sd_garr8_aview / sd_garr8_move / sd_src_ok at this file's image binding *)
Lemma fit_garr8_aview : forall (W : world segs) m p l j, garr8 segs (mrestrict (w_H W) m) p l ->
  (j < length l)%nat -> aview segs (w_H W) m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m p l j H Hj. unfold aview. rewrite (garr8_mbyte segs _ p l j H Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (H j Hj)).
Qed.
Lemma fit_garr8_move : forall (W W' : world segs) m m' x d l, garr8 segs (mrestrict (w_H W) m) x l ->
  (forall j, (j < length l)%nat -> aview segs (w_H W') m' (d + Z.of_nat j) = aview segs (w_H W) m (x + Z.of_nat j)) ->
  garr8 segs (mrestrict (w_H W') m') d l.
Proof.
intros W W' m m' x d l H HA j Hj. destruct (H j Hj) as [V R]. split; [|exact R].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (V 0%nat Hkk). cbn [Z.of_nat] in V. rewrite Z.add_0_r in V.
specialize (HA j Hj). unfold aview in HA. rewrite V in HA. cbn [option_map] in HA.
destruct (mbyte segs (mrestrict (w_H W') m') (d + Z.of_nat j)) as [bb|] eqn:Eb; cbn [option_map] in HA;
  [|discriminate HA].
injection HA as Hb. f_equal. apply bv_eq. exact Hb.
Qed.
Lemma fit_src_ok : forall (W : world segs) regs m p l, garr8 segs (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok segs W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l H Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (fit_garr8_aview W m p l (Z.to_nat (a - p)) H) by lia. discriminate.
Qed.

(* the earlier tx_put walk's template's tp_hull_sub (blob 185d37e0973): a sub-range of a visible hull is visible *)
Lemma fit_hull_sub : forall (rd : reader) p m d k, shadow_hull_vis rd p m -> p <= d -> d + k <= p + m -> 0 < k ->
  shadow_hull_vis rd d k.
Proof.
intros rd p m d k Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + k - 1) (p + m - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* the shadow byte, and the shadow hull byte, of an application byte lie off every application range *)
Lemma fit_sh_off : forall b c x lo hi, amem_range b c -> b <= lo -> hi <= b + c -> 0 <= x < 2 ^ 47 ->
  ~ (lo <= shadow_of_addr SHADOW_OFF x < hi).
Proof.
intros b c x lo hi Ham Hlo Hhi Hx. pose proof asan_consts as (_ & _ & C3 & C4 & C5).
unfold amem_range, shadow_of_addr, SHADOW_OFF in *. rewrite C3, C4, C5 in Ham.
assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.
Lemma fit_hull_off : forall b c x m s lo hi, amem_range b c -> b <= lo -> hi <= b + c -> 0 <= x -> 0 < m ->
  x + m <= 2 ^ 47 -> shadow_addr x / 8 * 8 <= s < shadow_addr (x + m - 1) / 8 * 8 + 8 -> ~ (lo <= s < hi).
Proof.
intros b c x m s lo hi Ham Hlo Hhi Hx Hm Hxm Hs. pose proof asan_consts as (_ & _ & C3 & C4 & C5).
unfold amem_range, shadow_addr, SHADOW_OFF in *. rewrite C3, C4, C5 in Ham.
Z.div_mod_to_equations. lia.
Qed.

(* PRW_WalkEnv.v's s10_pairwise_perm: pairwise of a symmetric relation is invariant under permutation *)
Lemma fit_pairwise_perm : forall (A : Type) (R : A -> A -> Prop), (forall a b, R a b -> R b a) ->
  forall l l', Permutation l l' -> pairwise R l -> pairwise R l'.
Proof.
intros A R Hs l l' Pm. induction Pm as [|x l l' Pm IH|x y l|l l' l'' P1 IH1 P2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hx Hl]. split; [|exact (IH Hl)].
  rewrite Forall_forall in Hx |- *. intros z Hz. apply Hx. exact (Permutation_in _ (Permutation_sym Pm) Hz).
- destruct H as [Hy [Hx Hl]]. inversion Hy as [|? ? Hyx Hyl]; subst.
  split; [constructor; [apply Hs; exact Hyx | exact Hx] | split; [exact Hyl | exact Hl]].
- exact (IH2 (IH1 H)).
Qed.
Lemma fit_zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.

(* FuzzFreeB.v's ff_val_mem_chunk8 at any offset, and the one-byte zero chunk of the NUL store *)
Lemma fit_val_mem_chunk8 : forall (E : env) (m : word -> option byte) base off v,
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 8 v)) -> val_mem segs m (base + off) 8 (U E v).
Proof.
intros E m base off v HC. pose proof (U_range E v) as HR. unfold M64 in HR.
apply (prh_val_mem_hdr8 (L := B_prog_listing) (PA := PA) m (base + off) (U E v) HR).
intros k0 Hk0. destruct (HC (Z.of_nat k0) ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-. rewrite Hb2. reflexivity.
Qed.
Lemma fit_val_mem_chunk1z : forall (E : env) (m : word -> option byte) base,
  YP09.chunk_ok segs E m base (YP09.mkChunk 0 (CVal 1 (SLit 0))) -> val_mem segs m base 1 0.
Proof.
intros E m base HC k0 Hk0. assert (k0 = 0%nat) by lia. subst k0.
destruct (HC 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-. rewrite !Z.add_0_r in Hb2.
cbn [Z.of_nat]. rewrite Z.add_0_r, Hb2. try (f_equal; vm_compute; reflexivity).
Qed.

(* the run posts' models differ only in what is materialized *)
Lemma fit_sbm : forall l X Y m, same_but_materialized (with_vm_backing l X m) (with_vm_backing l Y m).
Proof. intros l X Y [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

(* ---- the journal and the keep across a stretch and across the memcpy call ---- *)
(* the call's own journal, from the call state, over tx_put's window STK_tx_put below sp0 (a fresh journal at wle: the
   call keeps the world). The walk's journal is at RW, taken from ANY entry state S0 (the cut journal rebased at the
   cut's depot, YCbqGwild.ajournal_xw_rebaseR) *)
Lemma fit_J0 : forall D {S0 : astate} ly3 S3 Hp3 (W3 : world segs) mem md k FPs,
  tp_pre B CTX0 D -> ajournal_xR (SK := SK) segs B prh_pst ARX RW (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) S0 (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem md k ->
  ajournal_x (SK := SK) segs B prh_pst ARX STK_tx_put (tp_sp0 D) FPs ly3 S3 Hp3 W3 mem md [] ly3 S3 Hp3 W3 mem md 0.
Proof.
intros D S0 ly3 S3 Hp3 W3 mem md k FPs HPRE HJ.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HFW & _). destruct HFPRE as (HPRE0 & _ & _ & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk & _). pose proof HFW as (Hd0 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _ & _ & HQT & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros p0 n0 i H1 H2; exfalso; exact (H2 H1)|].
split; [intros a Ha; apply Hpres; unfold tp_sp0 in *; lia|].
(* the fresh journal's wild-part budget (YCbqG.v's eighteenth conjunct since the P'' universe set): an unchanged depot *)
split; [|split; [intros; reflexivity | split; [exact HQT | apply wild_part_same]]].
unfold astk_ok, ly_bot in *. rewrite Etop, Elo, Ehi. unfold tp_sp0. exact Hstk.
Qed.

(* an engine stretch at one allocator state keeps tp_KR RW: its writes lie in the record (OR) or in FPs inside a live
   block, and FPs lies in the entry's FP or in a block made since entry *)
Lemma fit_K_exec : forall D {S0 : astate} ly3 S3 Hp3 (W3 : world segs) mem md mem' md' k (Wr : Z -> Prop) FPs,
  tp_pre B CTX0 D -> ajournal_xR (SK := SK) segs B prh_pst ARX RW (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) S0 (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem md k -> tp_KR B SK RW D ly3 S3 W3 mem md ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W3) mem' x = mrestrict (w_H W3) mem x) ->
  (forall a, Wr a -> inFP (tp_OR D) a \/
     (inFP FPs a /\ exists b m, In (b, m) (ablocks B ly3 S3) /\ b <= a < b + req_size m)) ->
  (forall a, inFP FPs a -> inFP (tp_FP D) a \/ in_tmp_block (ablocks B (tp_ly D) (tp_S D)) (ablocks B ly3 S3) a) ->
  same_but_materialized md md' ->
  tp_KR B SK RW D ly3 S3 W3 mem' md'.
Proof.
intros D S0 ly3 S3 Hp3 W3 mem md mem' md' k Wr FPs HPRE HJ HK Hfr HW HFP Hsame.
pose proof HPRE as (HFPRE & _). destruct HFPRE as (HPRE0 & _ & _ & _).
pose proof HPRE0 as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & _).
pose proof HJ as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
unfold tp_KR. eapply (cj_kept_transR (SK := SK) segs B prh_pst ARX LAWS RW (wle'_trans segs YGcfRehidePost.RZ_cf)
  STK_tx_put (tp_sp0 D) STK_tx_put (tp_sp0 D) (tp_OR D) (tp_FP D) FPs (tp_FP D)).
- exact HK.
- eapply (cj_kept_execR (SK := SK) segs B prh_pst ARX LAWS (@pa_segs_low _ _ PA) RW
    (wle'_refl segs YGcfRehidePost.RZ_cf)); [exact HAR | | | | exact Hfr |
    intros a Ha; right; exact (HW a Ha) | exact Hsame].
  + rewrite Elo. exact Hceil.
  + rewrite Elo. unfold tp_sp0. lia.
  + rewrite Ehi. unfold tp_sp0. lia.
- exact HAR0.
- exact HAR.
- lia.
- lia.
- intros a Ha. left. exact Ha.
- intros a Ha. destruct (HFP a Ha) as [H|H]; [left; exact H | right; left; exact H].
Qed.

(* the memcpy call: its own journal from the call state (fit_J0's, carried by aj_intrin_at_xm; the call keeps the
   world) lifted to RW (ajournal_xwR_mono) gives the walk's journal (ajournal_x_subR) and keep (cj_kept_of_journalR,
   cj_kept_transR) at the return *)
Lemma fit_K_call : forall D {S0 : astate} ly3 S3 Hp3 (W3 : world segs) mem md mem' md' k FPs,
  tp_pre B CTX0 D -> ajournal_xR (SK := SK) segs B prh_pst ARX RW (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) S0 (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem md k ->
  ablocks B (tp_ly D) S0 = ablocks B (tp_ly D) (tp_S D) -> tp_KR B SK RW D ly3 S3 W3 mem md ->
  ajournal_x (SK := SK) segs B prh_pst ARX STK_tx_put (tp_sp0 D) FPs ly3 S3 Hp3 W3 mem md [] ly3 S3 Hp3 W3 mem' md' 0 ->
  (forall a, inFP FPs a -> inFP (tp_FP D) a \/ in_tmp_block (ablocks B (tp_ly D) (tp_S D)) (ablocks B ly3 S3) a) ->
  ajournal_xR (SK := SK) segs B prh_pst ARX RW (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D)
    (tp_ly D) S0 (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D) [] ly3 S3 Hp3 W3 mem' md' k /\
  tp_KR B SK RW D ly3 S3 W3 mem' md'.
Proof.
intros D S0 ly3 S3 Hp3 W3 mem md mem' md' k FPs HPRE HJ HAB HK HJ0 HFP.
pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HFW & _). destruct HFPRE as (HPRE0 & _ & _ & _).
pose proof HPRE0 as (HAR0 & _). pose proof HFW as (Hd0 & _).
pose proof HJ as (HAR & _).
assert (HJ0R : ajournal_xR (SK := SK) segs B prh_pst ARX RW STK_tx_put (tp_sp0 D) FPs ly3 S3 Hp3 W3 mem md []
  ly3 S3 Hp3 W3 mem' md' 0)
  by exact (ajournal_xwR_mono (SK := SK) segs B prh_pst ARX (@wle segs) RW (wle_wle' segs YGcfRehidePost.RZ_cf)
    _ _ _ _ _ Hp3 _ _ _ _ _ _ _ _ _ _ _ _ HJ0).
split.
- pose proof (ajournal_x_subR (SK := SK) segs B prh_pst ARX LAWS (@pa_segs_low _ _ PA) RW
    (wle'_trans segs YGcfRehidePost.RZ_cf)
    (STK_tx_put + tp_dw D) (tp_sp0 D + tp_dw D) (tp_FP D) (tp_ly D) S0 (tp_Hp D) (tp_W D) (tp_mem D) (tp_md D)
    [] ly3 S3 Hp3 W3 mem md k STK_tx_put (tp_sp0 D) FPs [] ly3 S3 Hp3 W3 mem' md' 0
    HJ HJ0R ltac:(unfold tp_sp0; lia) ltac:(unfold tp_sp0; lia)) as X.
  rewrite Z.add_0_r in X. apply X.
  intros a Ha. destruct (HFP a Ha) as [H|H]; [left; exact H | right; left; rewrite HAB; exact H].
- unfold tp_KR. eapply (cj_kept_transR (SK := SK) segs B prh_pst ARX LAWS RW (wle'_trans segs YGcfRehidePost.RZ_cf)
    STK_tx_put (tp_sp0 D) STK_tx_put (tp_sp0 D) (tp_OR D) (tp_FP D) FPs (tp_FP D)).
  + exact HK.
  + exact (cj_kept_of_journalR (SK := SK) segs B prh_pst ARX RW STK_tx_put (tp_sp0 D) FPs ly3 S3 Hp3 W3 mem md
      ly3 S3 Hp3 W3 mem' md' 0 (tp_OR D) HJ0R).
  + exact HAR0.
  + exact HAR.
  + lia.
  + lia.
  + intros a Ha. left. exact Ha.
  + intros a Ha. destruct (HFP a Ha) as [H|H]; [left; exact H | right; left; exact H].
Qed.

(* where the buffer's bytes may be written: the entry's old buffer (FIT arm, in FP), or the block the grow made
   (GROW arm, a block not in the entry's list: prhtx_grow's permutation and the blocks' pairwise disjointness) *)
Lemma fit_buf : forall D ly3 S3 Hp3 (W3 : world segs) mem md b1 cap1,
  ARX ly3 S3 Hp3 W3 mem md -> tp_fitarm B D ly3 S3 b1 cap1 -> 0 < cap1 -> In (b1, cap1) (ablocks B ly3 S3) ->
  forall a, b1 <= a < b1 + cap1 ->
  inFP (tp_FP D) a \/ in_tmp_block (ablocks B (tp_ly D) (tp_S D)) (ablocks B ly3 S3) a.
Proof.
intros D ly3 S3 Hp3 W3 mem md b1 cap1 HAR HARM Hc Hin a Ha.
assert (Hreq : req_size cap1 = cap1) by (unfold req_size; destruct (Z.eqb_spec cap1 0); lia).
destruct HARM as [(Hn & Eb & Ec & Ely & ES) | (Hlt & Ec & Hgrow & _)].
- left. unfold tp_FP, prhtx_fp. apply inFP_cons. right.
  destruct (Z.eqb_spec (tp_cap0 D) 0) as [E0|E0]; [lia|].
  cbn [ablocks_fp map]. apply inFP_cons. left. cbn [fst snd].
  rewrite <- Eb, <- Ec, Hreq. lia.
- right. exists b1, cap1. split; [exact Hin|]. split; [|rewrite Hreq; lia].
  intros Hin0.
  destruct Hgrow as [(_ & Ec' & _) | (Hlt' & bl1 & bl2 & Hsplit & Hperm)]; [unfold tp_req, tp_need in *; lia|].
  pose proof (alx_blocks segs B ARX LAWS ly3 S3 Hp3 W3 mem md b1 cap1 HAR Hin) as (_ & _ & _ & _ & _ & Hpw).
  assert (Hin12 : In (b1, cap1) (bl1 ++ bl2)).
  { destruct Hsplit as [(_ & E) | (_ & E)]; rewrite E in Hin0; [exact Hin0|].
    apply in_app_or in Hin0 as [H|[H|H]]; [apply in_or_app; left; exact H | | apply in_or_app; right; exact H].
    injection H as _ Ecap. lia. }
  apply (fit_pairwise_perm _ zdisjoint fit_zdisjoint_sym _ _ (Permutation_map _ Hperm)) in Hpw.
  cbn [map pairwise] in Hpw. destruct Hpw as [Hx _].
  rewrite Forall_forall in Hx.
  assert (Hm : In (b1, req_size cap1) (map (fun b => (fst b, req_size (snd b))) (bl1 ++ bl2))).
  { change (b1, req_size cap1) with ((fun b : Z * Z => (fst b, req_size (snd b))) (b1, cap1)).
    apply in_map. exact Hin12. }
  specialize (Hx _ Hm). unfold zdisjoint in Hx. cbn [fst snd] in Hx. lia.
Qed.

(* the frame and awr side goals of a run, over the regions the run starts from *)
Ltac fit_rs_compute H := lazymatch type of H with frame_of ?Ex ?rs _ _ =>
  let rs' := eval vm_compute in rs in change rs with rs' in H end.
Ltac fit_awr_compute := lazymatch goal with |- awr_ok ?Ex ?rs ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7 =>
  let rs' := eval vm_compute in rs in change (awr_ok Ex rs' a1 a2 a3 a4 a5 a6 a7) end.
Ltac fit_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?Hh ?ms) => pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H
  | st_ok ?sg ?E ?ss (restrict ?Hh ?ms) => pose proof (st_ok_restrict_reg sg Hh E ss ms r HS) as H
  end;
  lazymatch type of H with _ = sv_denot _ (sr_get (ss_regs ?ssx) _) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in change (sr_get (ss_regs ssx) r) with e in H end;
  cbn [ms_regs mkst restrict] in H.
Ltac fit_atom_reg := cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.

Lemma tp_seg_FIT_ok : forall P, srr_inv_laws segs P -> srr_inv_call segs P -> tp_seg_FIT B SK CTX0 P.
Proof.
intros P PLAW PCALL Q D ly3 S3 Hp3 W3 regs3 mem3 md3 k b1 cap1 HAT HIMG KEND HP0.
pose proof HAT as (WS & HBUD & HCAR & HSH & Hf0 & R19 & R21 & R23 & R25 & R26 & HREC & HBLK & HTXT & HNEED & HSDJ &
  HKEPT & HARM & HSIDE & HPOS).
pose proof HCAR as (HPRE & HJ & HK & HKR & HSP & HSAV & HHP & HROD).
(* the cut journal is at the budget WS (the grow's wild trace, or none); the runs and __asan_memcpy's rule read an
   empty-budget journal: the cut's, rebased at the cut's depot (YCbqGwild.ajournal_xw_rebase); unbased at the end *)
pose proof HJ as HJw. unfold tp_JR in HJw.
pose proof (ajournal_xw_rebaseR (SK := SK) segs B prh_pst _ RW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJw) as HJr.
clear HJ. rename HJr into HJ.
pose proof HSH as (R22 & R8 & R9 & R18).
pose proof HPRE as (HFPRE & HUNIV & HRL & HPOS0 & HLIVE & H10 & H11 & H12 & HFW & HPLACE & HTRACE & HREC0 & HINV &
  HSRC & HSLEN & HKEPT0 & HDISJ & HNEEDB & HLED & HEVP & HBB & HREQ).
pose proof HFPRE as (HPRE0 & HROD0 & HSTKHI & HRAC).
pose proof HPRE0 as ([HAR0 HXS] & Hra & Hra4 & Hgp & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HFW as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HPLACE as (Hta & Ht1 & Ht2 & Hwrit & Hra28).
pose proof HREC as (Rb & Rl & Rc & Rf & Mb & Ml & Mc & Mf).
pose proof HBLK as (Hcap1 & Hblk & Hb4096 & Hbceil & Hbamr & Hbw & Hbra & Hbhull & Hbnl).
pose proof HSIDE as (HLED3 & HSRC3 & HRL3).
pose proof HINV as (Hltxt & _).
pose proof HJ as (HARJ & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & J1 & J2 & J3 & J4 & Jgone & Jpres & Jstk &
  J5 & JQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
pose proof HSRC3 as (Hsby & Hs4096 & Hsceil & Hsamr & Hsra & Hshull).
rewrite HSLEN in Hsceil, Hsamr, Hsra, Hshull.
unfold tp_need in HNEED, HNEEDB. unfold tp_sp0 in *.
assert (FTP : @STK_tx_put TP_PrhImg = 16496) by (vm_compute; reflexivity).
assert (HES : ESTACK = 4096) by reflexivity.
assert (ESP : tp_sp0 D = spZ (tp_regs D)) by reflexivity.
assert (EFR : TP_FRAME = 112) by reflexivity.
assert (Hn0 : 0 <= tp_n D) by (rewrite <- HSLEN; lia).
assert (Ht47 : tp_t D + 28 <= 2 ^ 47) by lia.
assert (Ht46 : 2 ^ 46 <= tp_t D) by lia.
assert (Ht32 : tp_t D <= 2 ^ 47 - 32)
  by (pose proof (Z.div_mod (tp_t D) 8 ltac:(lia)) as Hdm; rewrite Hta in Hdm; lia).
assert (Hrq1 : req_size cap1 = cap1) by (unfold req_size; destruct (Z.eqb_spec cap1 0); lia).
(* the record's 16 checked bytes: present (the journal's window) and addressable (the real stack's zero shadow) *)
assert (Hwr16 : forall a, tp_t D <= a < tp_t D + 16 -> writable_at segs (mrestrict (w_H W3) mem3) a)
  by (intros a Ha; apply (apresent_writable segs); apply Jpres; lia).
assert (Hra16 : range_addressable (aview segs (w_H W3) mem3) SHADOW_OFF (tp_t D) 16).
{ apply (fit_ra_stack ly3 S3 Hp3 W3 mem3 md3 (tp_t D) 16 HARJ); rewrite ?Elo, ?Ehi; lia. }
(* the buffer's bytes are inside the walk's write permission *)
assert (HBUF : forall a, b1 <= a < b1 + cap1 ->
  awr_byte (STK_tx_put + tp_dw D) (spZ (tp_regs D) + tp_dw D) (tp_FP D) (ablocks B (tp_ly D) (tp_S D))
    (ablocks B ly3 S3) ly3 [] a).
{ intros a Ha. destruct (fit_buf D ly3 S3 Hp3 W3 mem3 md3 b1 cap1 HARJ HARM Hcap1 Hblk a Ha) as [Hf | Ht'].
  - right. left. split; [exact Hf|]. exists b1, cap1. split; [exact Hblk | lia].
  - right. right. left. exact Ht'. }
assert (HFPS : forall a, inFP (ablocks_fp [(b1, cap1)]) a ->
  inFP (tp_FP D) a \/ in_tmp_block (ablocks B (tp_ly D) (tp_S D)) (ablocks B ly3 S3) a).
{ intros a Ha. cbn [ablocks_fp map] in Ha. apply inFP_cons in Ha as [Ha | (r & [] & _)].
  cbn [fst snd] in Ha. apply (fit_buf D ly3 S3 Hp3 W3 mem3 md3 b1 cap1 HARJ HARM Hcap1 Hblk a). lia. }
assert (HFP0 : forall a, inFP (@nil (Z * Z)) a ->
  inFP (tp_FP D) a \/ in_tmp_block (ablocks B (tp_ly D) (tp_S D)) (ablocks B ly3 S3) a)
  by (intros a (r & [] & _)).
(* an image byte is no buffer byte *)
assert (KIMG : forall a, in_img segs a -> ~ (b1 <= a < b1 + cap1))
  by (intros a Hi Hr; exact (blk_img_x segs B ARX LAWS ly3 S3 Hp3 W3 mem3 md3 b1 cap1 a HARJ Hblk ltac:(lia) Hi)).
(* ---- the symbolic state at the cut ---- *)
destruct (fit_entry W3 regs3 mem3 (tp_t D) (tp_n D) b1 (tp_len0 D) R8 R9 R22 R19 R26 R23 ltac:(lia)
  ltac:(exact Hta) ltac:(lia) ltac:(lia) ltac:(lia) Hwr16 Mb Ml Hra16) as [HS SHOK].
remember (fit_E regs3 b1 (tp_len0 D)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold fit_E; apply Eimg_env).
assert (EL : forall j, (j < A_TEXT)%nat -> ew E j = ew (Ereg regs3 (map (Z_to_bv 64) [b1; tp_len0 D])) j)
  by (intros j Hj; subst E; unfold fit_E; apply Eimg_low; exact Hj).
assert (ER : forall (r : bv 5) j, Z.of_nat j = bv_unsigned r -> ew E j = getr regs3 r).
{ intros r j Hj. pose proof (u5_range r) as Hr. rewrite EL by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs3 _ j r Hj). }
assert (X32 : ew E 32 = Z_to_bv 64 b1) by (rewrite EL by (unfold A_TEXT; lia); reflexivity).
assert (X33 : ew E 33 = Z_to_bv 64 (tp_len0 D)) by (rewrite EL by (unfold A_TEXT; lia); reflexivity).
assert (UB1 : U E (SOff 32 0) = b1) by (apply U_atom; [exact X32 | lia]).
assert (UL0 : U E (SOff 33 0) = tp_len0 D) by (apply U_atom; [exact X33 | lia]).
assert (UN : U E (SOff 9 0) = tp_n D) by (apply U_atom; [rewrite (ER 9%bv 9%nat eq_refl); exact R9 | lia]).
assert (Ut : bv_unsigned (ew E 8) = tp_t D)
  by (rewrite (ER 8%bv 8%nat eq_refl), R8; apply unsigned_lit_small; lia).
assert (UBX : U E (SOff 22 0) = SHADOW_OFF).
{ rewrite U_SOff, (ER 22%bv 22%nat eq_refl), R22, Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia).
  apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
clear HE.
pose (RUN := @paj_run_x_invR fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW
  RW (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RUNTO := @paj_run_to_x_invR fx rc SK B_prog_listing TP_PAListing PA B prh_pst ARX _ LAWS P PLAW
  RW (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (PI := PA) RW).
unfold tp_cfg, tp_pc. rewrite <- Z.add_assoc.
(* the FIT cut is after the GROW's realloc: the segment is over RW (SRr' segs RZ_cf is SRrG segs RW) *)
unfold SRr'.
assert (HPM : P mem3) by exact HP0.
(* ==== +256 .. +288: the load checks of t and t + 8 (covered by fit_SH), a0 = len0 + b1, a1 = b1 ==== *)
pose proof HJ as HJa.
paj_run_tok_x_inv RUN HS HJ SHOK HPM fit_Bspan.
{ fit_awr_compute. intros a Ha. apply fit_inw1 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ut in Ha. left. lia. }
lazymatch type of HS with context [restrict _ ?msx] => rename msx into ms1 end.
fit_rs_compute HFr.
assert (KV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  aview segs (w_H W3) (ms_mem ms1) a = aview segs (w_H W3) mem3 a).
{ eapply (fit_keep_frame E _ W3 mem3 (ms_mem ms1)); [exact HFr|].
  intros a Ha. apply fit_inw1 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ut in Ha. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdx) _ =>
  assert (K1 : tp_KR B SK RW D ly3 S3 W3 (ms_mem ms1) mdx) end.
{ eapply (fit_K_exec D ly3 S3 Hp3 W3 mem3 md3 _ _ k _ (@nil (Z * Z)) HPRE HJa HK);
  [exact HFr | intros a Ha | exact HFP0 | first [apply same_but_materialized_wvb_any | exact (fit_sbm _ _ _ _)]].
  left. unfold tp_OR, tp_FP, prhtx_fp. apply inFP_cons. left.
  apply fit_inw1 in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Ut in Ha. lia. }
clear HK HJa. rename K1 into HK. clear HF HG HFr.
(* +288 `bltu a0, a1`: b1 + len0 does not wrap (UBSan's trap at +488, NOT TAKEN) *)
psrr_branch_tok RUN BR HS SHOK fit_Bspan.
{ exfalso. rewrite branch_ltu_U, U_SAlu, UB1, UL0 in Hc. cbn [zalu_raw] in Hc.
  rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
(* ==== +292 .. +316: the UBSan NULL test (decided), the memcpy arguments ==== *)
clear Hc. pose proof HJ as HJa.
paj_run_tok_x_inv RUN HS HJ SHOK HPM fit_Bspan.
{ fit_awr_compute. intros a Ha. apply fit_inw1 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ut in Ha. left. lia. }
lazymatch type of HS with context [restrict _ ?msx] => rename msx into ms2 end.
fit_rs_compute HFr.
assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) mem3 a).
{ assert (KV2' : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
    aview segs (w_H W3) (ms_mem ms2) a = aview segs (w_H W3) (ms_mem ms1) a).
  { eapply (fit_keep_frame E _ W3 (ms_mem ms1) (ms_mem ms2)); [exact HFr|].
    intros x Hx. apply fit_inw1 in Hx. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Ut in Hx. lia. }
  intros a Ha Hn. rewrite (KV2' a Ha Hn). exact (KV1 a Ha Hn). }
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdx) _ =>
  assert (K2 : tp_KR B SK RW D ly3 S3 W3 (ms_mem ms2) mdx) end.
{ eapply (fit_K_exec D ly3 S3 Hp3 W3 (ms_mem ms1) _ _ _ k _ (@nil (Z * Z)) HPRE HJa HK);
  [exact HFr | intros a Ha | exact HFP0 | first [apply same_but_materialized_wvb_any | exact (fit_sbm _ _ _ _)]].
  left. unfold tp_OR, tp_FP, prhtx_fp. apply inFP_cons. left.
  apply fit_inw1 in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Ut in Ha. lia. }
clear HK HJa. rename K2 into HK. clear HF HG HFr.
(* ==== +316 `jal __asan_memcpy` (b1 + len0, s, n) ==== *)
pmkst HS.
fit_reg HS (10%bv : bv 5) Q10. fit_reg HS (11%bv : bv 5) Q11. fit_reg HS (12%bv : bv 5) Q12.
fit_reg HS (1%bv : bv 5) Q1. fit_reg HS (2%bv : bv 5) Q2. fit_reg HS (3%bv : bv 5) Q3. fit_reg HS (4%bv : bv 5) Q4.
assert (V10 : getr (ms_regs ms2) 10 = Z_to_bv 64 (b1 + tp_len0 D)).
{ rewrite Q10, denot_lit_U. f_equal. rewrite U_SAlu, UB1, UL0. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. }
assert (V11 : getr (ms_regs ms2) 11 = Z_to_bv 64 (tp_s D)).
{ rewrite Q11. fit_atom_reg. rewrite (ER 18%bv 18%nat eq_refl). exact R18. }
assert (V12 : getr (ms_regs ms2) 12 = Z_to_bv 64 (tp_n D)).
{ rewrite Q12. fit_atom_reg. rewrite (ER 9%bv 9%nat eq_refl). exact R9. }
assert (V2 : spZ (ms_regs ms2) = spZ regs3).
{ unfold spZ at 1. rewrite Q2. fit_atom_reg. rewrite (ER 2%bv 2%nat eq_refl). reflexivity. }
assert (V3 : getr (ms_regs ms2) 3 = getr regs3 3)
  by (rewrite Q3; fit_atom_reg; rewrite (ER 3%bv 3%nat eq_refl); reflexivity).
assert (V4 : getr (ms_regs ms2) 4 = getr regs3 4)
  by (rewrite Q4; fit_atom_reg; rewrite (ER 4%bv 4%nat eq_refl); reflexivity).
assert (V1 : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + 15428))
  by (rewrite Q1; change 240%nat with A_TEXT; apply codeptr_val; exact HEI).
assert (HJ0 : ajournal_x (SK := SK) segs B prh_pst ARX STK_tx_put (spZ (tp_regs D)) (ablocks_fp [(b1, cap1)])
  ly3 S3 Hp3 W3 (ms_mem ms2) _ [] ly3 S3 Hp3 W3 (ms_mem ms2) _ 0)
  by (eapply (fit_J0 D ly3 S3 Hp3 W3 _ _ k _ HPRE); exact HJ).
assert (Hsby2 : garr8 segs (mrestrict (w_H W3) (ms_mem ms2)) (tp_s D) (tp_src D)).
{ apply (fit_garr8_move W3 W3 mem3 (ms_mem ms2) (tp_s D) (tp_s D) (tp_src D) Hsby).
  intros j Hj. apply KV2; [lia | pose proof (HDISJ (tp_s D + Z.of_nat j) ltac:(lia)) as [Hx _]; lia]. }
(* the call keeps the world: its plain SRr rule, lifted into RW (YA0nH.SRr_SRrG), bound at RW *)
eapply (SRrG_bind segs RW (wle'_trans segs YGcfRehidePost.RZ_cf)).
{ apply (SRr_SRrG segs RW (wle_wle' segs YGcfRehidePost.RZ_cf)).
  eapply (aj_intrin_at_xm (SK := SK) segs B prh_pst ARX LAWS (@pa_segs_low _ _ PA) OCpy (SIGMA AS___asan_memcpy)
    AI W3 (ms_regs ms2) (ms_mem ms2) STK_tx_put (spZ (tp_regs D)) (ablocks_fp [(b1, cap1)]) ly3 S3 Hp3 W3
    (ms_mem ms2) _ [] ly3 S3 Hp3 _ 0 (b1 + tp_len0 D) (tp_s D) (tp_n D) (-112) _ HJ0).
  - exact V10.
  - exact V11.
  - exact V12.
  - lia.
  - lia.
  - lia.
  - rewrite ?V2, ?HSP. lia.
  - reflexivity.
  - lia.
  - rewrite FTP, HES. lia.
  - rewrite V3. rewrite (HKR 3%bv ltac:(cbn; tauto)). exact Hgp.
  - rewrite V4. rewrite (HKR 4%bv ltac:(cbn; tauto)). exact Htp0.
  - exact V1.
  - apply (ret_ok_codeptr_v (L := B_prog_listing) (PI := PA)); [lia | reflexivity].
  - intros a Ha. split.
    + right. left. split.
      * cbn [ablocks_fp map]. apply inFP_cons. left. cbn [fst snd]. lia.
      * exists b1, cap1. split; [exact Hblk | lia].
    + rewrite ?V2, ?HSP. lia.
  - unfold amem_range in *. lia.
  - apply (tpk_ra_keep (aview segs (w_H W3) mem3));
    [intros x Hx; apply KV2; [pose proof (tpk_shadow_lo x ltac:(lia)); lia |
       pose proof (tpk_shadow_lo x ltac:(lia)); lia]|].
    apply (range_addressable_sub (aview segs (w_H W3) mem3) SHADOW_OFF b1 cap1); [exact Hbra | lia | lia].
  - intros Hnp. apply (tpk_hull_keep (aview segs (w_H W3) mem3));
    [intros sx Hsx; apply KV2;
       [pose proof (tpk_hull_lo (b1 + tp_len0 D) (tp_n D) sx ltac:(lia) ltac:(lia) ltac:(lia) Hsx); lia |
        pose proof (tpk_hull_lo (b1 + tp_len0 D) (tp_n D) sx ltac:(lia) ltac:(lia) ltac:(lia) Hsx); lia]|].
    apply (fit_hull_sub _ b1 cap1); [exact Hbhull | lia | lia | lia].
  - cbv beta iota. split; [lia|]. split; [lia|]. split.
    { rewrite <- HSLEN. apply (fit_src_ok W3 (ms_regs ms2) (ms_mem ms2) (tp_s D) (tp_src D) Hsby2).
      intros a Ha. rewrite HSLEN in Ha. rewrite ?V2, ?HSP. lia. }
    split.
    { destruct (Z_le_gt_dec (b1 + tp_len0 D + tp_n D) (tp_s D)) as [h|h]; [left; lia|].
      destruct (Z_le_gt_dec (tp_s D + tp_n D) (b1 + tp_len0 D)) as [h'|h']; [right; lia|].
      exfalso. destruct (Z_le_gt_dec (tp_s D) (b1 + tp_len0 D)) as [hc|hc].
      - exact (HSDJ (b1 + tp_len0 D) ltac:(lia) ltac:(lia)).
      - exact (HSDJ (tp_s D) ltac:(lia) ltac:(lia)). }
    split; [unfold amem_range in *; lia|].
    split.
    { apply (tpk_ra_keep (aview segs (w_H W3) mem3));
      [intros x Hx; apply KV2;
         [pose proof (tpk_shadow_lo x ltac:(lia)); lia | pose proof (tpk_shadow_lo x ltac:(lia)); lia]|].
      exact Hsra. }
    intros Hnp. apply (tpk_hull_keep (aview segs (w_H W3) mem3));
    [intros sx Hsx; apply KV2;
       [pose proof (tpk_hull_lo (tp_s D) (tp_n D) sx ltac:(lia) ltac:(lia) ltac:(lia) Hsx); lia |
        pose proof (tpk_hull_lo (tp_s D) (tp_n D) sx ltac:(lia) ltac:(lia) ltac:(lia) Hsx); lia]|].
    exact (Hshull Hnp). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Hcopy & Hfr5 & Hpres5 & Hmn5).
cbv beta iota in Hcopy.
assert (HPM5 : P mem5) by exact (PCALL _ _ Hmn5 HPM).
destruct (fit_K_call D ly3 S3 Hp3 W3 (ms_mem ms2) _ mem5 _ k (ablocks_fp [(b1, cap1)]) HPRE HJ eq_refl HK HJ5 HFPS)
  as [HJn HKn].
clear HJ HK. rename HJn into HJ. rename HKn into HK.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & J5pres & _).
jafter_call_keep_pi HS 40%nat regs5 (mrestrict (w_H W3) mem5) HP5 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ apply Forall_cons; [|apply Forall_nil]. split;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Ut; intros a Ha.
  - apply (prh_mbyte_of_aview (w_H W3) (w_H W3)). apply Hfr5; [lia | lia | rewrite ?V2, ?HSP; lia].
  - intros _. apply (apresent_writable segs). apply J5pres. lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 40 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HSX.
assert (OLD5 : forall j, (j < 40)%nat -> ew E5 j = ew E j)
  by (intros j Hj; rewrite HE5, ew_havoc_old by exact Hj; reflexivity).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI | cbv; lia]).
clear HE5.
assert (Ut5 : bv_unsigned (ew E5 8) = tp_t D) by (rewrite OLD5 by lia; exact Ut).
assert (UB15 : U E5 (SOff 32 0) = b1) by (rewrite !U_SOff, OLD5 by lia; rewrite <- !U_SOff; exact UB1).
assert (UL05 : U E5 (SOff 33 0) = tp_len0 D) by (rewrite !U_SOff, OLD5 by lia; rewrite <- !U_SOff; exact UL0).
assert (UN5 : U E5 (SOff 9 0) = tp_n D) by (rewrite !U_SOff, OLD5 by lia; rewrite <- !U_SOff; exact UN).
assert (UBX5 : U E5 (SOff 22 0) = SHADOW_OFF) by (rewrite !U_SOff, OLD5 by lia; rewrite <- !U_SOff; exact UBX).
assert (SHOK5 : sh_ok segs fit_Bx fit_SH E5 (mrestrict (w_H W3) mem5)).
{ apply (fit_shok E5 W3 mem5 (tp_t D)); [exact UBX5 | | lia |].
  - rewrite U_SOff, Ut5, Z.add_0_r. apply zcanon_id. unfold M64. lia.
  - apply (fit_ra_stack ly3 S3 Hp3 W3 mem5 _ (tp_t D) 16 (proj1 HJ)); rewrite ?Elo, ?Ehi; lia. }
clear HS SHOK HPM. rename HSX into HS. rename SHOK5 into SHOK. rename HPM5 into HPM.
(* ==== +320 .. +356 ==== *)
pose proof HJ as HJa.
paj_run_tok_x_inv RUN HS HJ SHOK HPM fit_Bspan.
{ fit_awr_compute. intros a Ha. apply fit_inw1 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ut5 in Ha. left. lia. }
lazymatch type of HS with context [restrict _ ?msx] => rename msx into ms3 end.
fit_rs_compute HFr.
assert (KV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  aview segs (w_H W3) (ms_mem ms3) a = aview segs (w_H W3) mem5 a).
{ eapply (fit_keep_frame E5 _ W3 mem5 (ms_mem ms3)); [exact HFr|].
  intros a Ha. apply fit_inw1 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ut5 in Ha. lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdx) _ =>
  assert (K3 : tp_KR B SK RW D ly3 S3 W3 (ms_mem ms3) mdx) end.
{ eapply (fit_K_exec D ly3 S3 Hp3 W3 mem5 _ _ _ k _ (@nil (Z * Z)) HPRE HJa HK);
  [exact HFr | intros a Ha | exact HFP0 | first [apply same_but_materialized_wvb_any | exact (fit_sbm _ _ _ _)]].
  left. unfold tp_OR, tp_FP, prhtx_fp. apply inFP_cons. left.
  apply fit_inw1 in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Ut5 in Ha. lia. }
clear HK HJa. rename K3 into HK. clear HF HG HFr.
(* +356 `bltu a0, a1`: b1 + len0 + n does not wrap (NOT TAKEN) *)
psrr_branch_tok RUN BR HS SHOK fit_Bspan.
{ exfalso. rewrite branch_ltu_U, !U_SAlu, UB15, UL05, UN5 in Hc. cbn [zalu_raw] in Hc.
  rewrite (zcanon_id (tp_n D + b1)) in Hc by (unfold M64; lia).
  rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
(* ==== +360 .. +380: the two UBSan tests (decided); stop before the NUL store's 1-byte check ==== *)
clear Hc. pose proof HJ as HJa.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM fit_Bspan 15488.
{ fit_awr_compute. intros a Ha. apply fit_inw1 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Ut5 in Ha. left. lia. }
lazymatch type of HS with context [restrict _ ?msx] => rename msx into ms4 end.
fit_rs_compute HFr.
assert (KV4 : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) mem5 a).
{ assert (KV4' : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
    aview segs (w_H W3) (ms_mem ms4) a = aview segs (w_H W3) (ms_mem ms3) a).
  { eapply (fit_keep_frame E5 _ W3 (ms_mem ms3) (ms_mem ms4)); [exact HFr|].
    intros x Hx. apply fit_inw1 in Hx. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hx. rewrite Ut5 in Hx. lia. }
  intros a Ha Hn. rewrite (KV4' a Ha Hn). exact (KV3 a Ha Hn). }
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdx) _ =>
  assert (K4 : tp_KR B SK RW D ly3 S3 W3 (ms_mem ms4) mdx) end.
{ eapply (fit_K_exec D ly3 S3 Hp3 W3 (ms_mem ms3) _ _ _ k _ (@nil (Z * Z)) HPRE HJa HK);
  [exact HFr | intros a Ha | exact HFP0 | first [apply same_but_materialized_wvb_any | exact (fit_sbm _ _ _ _)]].
  left. unfold tp_OR, tp_FP, prhtx_fp. apply inFP_cons. left.
  apply fit_inw1 in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Ut5 in Ha. lia. }
clear HK HJa. clear HF HG HFr. rename K4 into HK.
(* ---- the NUL byte gets an atom and a region of its own ---- *)
pmkst HS.
fit_reg HS (10%bv : bv 5) Q10'.
assert (V10' : getr (ms_regs ms4) 10 = Z_to_bv 64 (b1 + tp_len0 D + tp_n D)).
{ rewrite Q10', denot_lit_U. f_equal. rewrite !U_SAlu, UB15, UL05, UN5. cbn [zalu_raw].
  rewrite (zcanon_id (tp_n D + b1)) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia. }
jafter_stretch_pi HS 56%nat (ms_regs ms4) (mrestrict (w_H W3) (ms_mem ms4)) ([10%bv] : list (bv 5)) 15488 HSY.
specialize (HSY (fun r _ => eq_refl)).
lazymatch type of HSY with ?T -> _ => assert (HRKY : T) end.
{ apply Forall_forall. intros r _. split; intros; [reflexivity | assumption]. }
specialize (HSY HRKY). clear HRKY. rewrite <- restrict_mkst_fx in HSY.
remember (havoc E5 56 (map (getr (ms_regs ms4)) [10%bv])) as E6 eqn:HE6 in HSY.
assert (OLD6 : forall j, (j < 56)%nat -> ew E6 j = ew E5 j)
  by (intros j Hj; rewrite HE6, ew_havoc_old by exact Hj; reflexivity).
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (X56 : ew E6 56 = Z_to_bv 64 (b1 + tp_len0 D + tp_n D)) by (rewrite HE6; cbn; exact V10').
clear HE6.
assert (Ut6 : bv_unsigned (ew E6 8) = tp_t D) by (rewrite OLD6 by lia; exact Ut5).
assert (UBX6 : U E6 (SOff 22 0) = SHADOW_OFF) by (rewrite !U_SOff, OLD6 by lia; rewrite <- !U_SOff; exact UBX5).
assert (U56 : U E6 (SOff 56 0) = b1 + tp_len0 D + tp_n D) by (apply U_atom; [exact X56 | lia]).
assert (AF56 : afact_ok E6 56 (mkAF 4096 (2 ^ 47 - 2 ^ 23) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite X56, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia. }
pose proof (st_ok_pi_add_fact _ _ _ _ _ HSY AF56) as HS6. clear HSY.
assert (HRO56 : region_ok segs E6 (mrestrict (w_H W3) (ms_mem ms4)) fit_nul).
{ unfold fit_nul, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite X56.
  rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  pose proof (alx_blocks segs B ARX LAWS ly3 S3 Hp3 W3 (ms_mem ms4) _ b1 cap1 (proj1 HJ) Hblk)
    as (_ & _ & _ & _ & Hpr4 & _).
  intros o Ho. apply (apresent_writable segs). apply (proj1 (Hpr4 (b1 + tp_len0 D + tp_n D + o) ltac:(lia))). }
assert (HDJ56 : all_disjoint E6 fit_nul [fit_rec]).
{ cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, fit_nul, fit_rec.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite X56, Ut6.
  rewrite unsigned_lit_small by lia. left. lia. }
pose proof (st_ok_pi_add_region _ _ _ fit_nul HS6 eq_refl HRO56 HDJ56) as HS7. clear HS6.
assert (SHOK7 : sh_ok segs fit_Bx fit_SH2 E6 (mrestrict (w_H W3) (ms_mem ms4))).
{ unfold sh_ok, fit_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_range segs (w_H W3) (ms_mem ms4) E6 fit_Bx 8%nat (tp_t D) 16 (tp_t D) 0 16);
    [ apply (fit_ra_stack ly3 S3 Hp3 W3 (ms_mem ms4) _ (tp_t D) 16 (proj1 HJ)); rewrite ?Elo, ?Ehi; lia
    | exact UBX6
    | rewrite U_SOff, Ut6, Z.add_0_r; apply zcanon_id; unfold M64; lia | lia | lia
    | intros x Hx; unfold SHADOW_OFF; lia].
  - apply (shent_ok_of_range segs (w_H W3) (ms_mem ms4) E6 fit_Bx 56%nat b1 cap1
      (b1 + tp_len0 D + tp_n D) 0 1);
    [ | exact UBX6 | exact U56 | lia | lia
    | intros x Hx; unfold amem_range in Hbamr; unfold SHADOW_OFF; lia ].
    apply (tpk_ra_keep (aview segs (w_H W3) mem5));
    [ intros x Hx; apply KV4;
      [pose proof (tpk_shadow_lo x ltac:(lia)); lia | pose proof (tpk_shadow_lo x ltac:(lia)); lia] |].
    apply (tpk_ra_keep (aview segs (w_H W3) (ms_mem ms2)));
    [ intros x Hx; apply Hfr5;
      [ pose proof (tpk_shadow_lo x ltac:(lia)); lia
      | pose proof (fit_sh_off b1 cap1 x (b1 + tp_len0 D) (b1 + tp_len0 D + tp_n D) Hbamr ltac:(lia)
          ltac:(lia) ltac:(lia)); lia
      | pose proof (tpk_shadow_lo x ltac:(lia)); rewrite ?V2, ?HSP; lia ] |].
    apply (tpk_ra_keep (aview segs (w_H W3) mem3));
    [ intros x Hx; apply KV2;
      [pose proof (tpk_shadow_lo x ltac:(lia)); lia | pose proof (tpk_shadow_lo x ltac:(lia)); lia]
    | exact Hbra ]. }
clear HS SHOK. rename HS7 into HS. rename SHOK7 into SHOK.
(* ==== +380 .. +400: the NUL store's 1-byte check (decided) and `sb zero, 0(a0)` ==== *)
pose proof HJ as HJa.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM fit_Bspan 15508.
{ fit_awr_compute. intros a Ha. apply fit_inw2 in Ha.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Ut6, X56, unsigned_lit_small in Ha by lia.
  destruct Ha as [Ha | Ha]; [apply HBUF; lia | left; lia]. }
lazymatch type of HS with context [restrict _ ?msx] => rename msx into msE end.
fit_rs_compute HFr.
assert (KV6 : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  ~ (b1 + tp_len0 D + tp_n D <= a < b1 + tp_len0 D + tp_n D + 1) ->
  aview segs (w_H W3) (ms_mem msE) a = aview segs (w_H W3) (ms_mem ms4) a).
{ intros a Ha Hn1 Hn2.
  eapply (fit_keep_frame E6 _ W3 (ms_mem ms4) (ms_mem msE)
    (fun x => (tp_t D <= x < tp_t D + 16) \/ (b1 + tp_len0 D + tp_n D <= x < b1 + tp_len0 D + tp_n D + 1)));
  [exact HFr | | exact Ha | tauto].
  intros x Hx. apply fit_inw2 in Hx.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hx.
  rewrite Ut6, X56, unsigned_lit_small in Hx by lia. destruct Hx as [Hx | Hx]; [right | left]; lia. }
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdx) _ =>
  assert (K6 : tp_KR B SK RW D ly3 S3 W3 (ms_mem msE) mdx) end.
{ eapply (fit_K_exec D ly3 S3 Hp3 W3 (ms_mem ms4) _ _ _ k _ (ablocks_fp [(b1, cap1)]) HPRE HJa HK);
  [exact HFr | intros a Ha | exact HFPS | first [apply same_but_materialized_wvb_any | exact (fit_sbm _ _ _ _)]].
  apply fit_inw2 in Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Ha.
  rewrite Ut6, X56, unsigned_lit_small in Ha by lia.
  destruct Ha as [Ha | Ha].
  - right. split; [cbn [ablocks_fp map]; apply inFP_cons; left; cbn [fst snd]; lia|].
    exists b1, cap1. split; [exact Hblk | lia].
  - left. unfold tp_OR, tp_FP, prhtx_fp. apply inFP_cons. left. lia. }
clear HK HJa. rename K6 into HK. clear HF HG HFr.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & JEpres & _).
(* ---- the keeps at the end state ---- *)
assert (KVE : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  ~ (b1 + tp_len0 D <= a < b1 + tp_len0 D + tp_n D) ->
  ~ (spZ (tp_regs D) - 112 - ESTACK <= a < spZ (tp_regs D) - 112) ->
  ~ (b1 + tp_len0 D + tp_n D <= a < b1 + tp_len0 D + tp_n D + 1) ->
  aview segs (w_H W3) (ms_mem msE) a = aview segs (w_H W3) mem3 a).
{ intros a Ha H1 H2 H3 H4. rewrite (KV6 a Ha H1 H4), (KV4 a Ha H1).
  rewrite (Hfr5 a Ha H2 ltac:(rewrite ?V2, ?HSP; lia)). exact (KV2 a Ha H1). }
assert (KVC : forall a, 0 <= a < 2 ^ 64 -> ~ (tp_t D <= a < tp_t D + 16) ->
  ~ (b1 + tp_len0 D + tp_n D <= a < b1 + tp_len0 D + tp_n D + 1) ->
  aview segs (w_H W3) (ms_mem msE) a = aview segs (w_H W3) mem5 a)
  by (intros a Ha H1 H4; rewrite (KV6 a Ha H1 H4); exact (KV4 a Ha H1)).
assert (KPST : forall a, Exists (in_zr a) prh_pst ->
  aview segs (w_H W3) (ms_mem msE) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. pose proof (pa_segs_low a (tpi_pst_img B HIMG a Ha)) as Hlo. unfold kLowMemEnd in Hlo.
  pose proof (KIMG a (tpi_pst_img B HIMG a Ha)) as Hni.
  apply KVE; [lia | lia | lia | lia | lia]. }
assert (KHEAD : forall a j, In (a, j) (tp_Lam D) -> forall i, 0 <= i < 8 ->
  aview segs (w_H W3) (ms_mem msE) (a - cf_head + i) = aview segs (w_H W3) mem3 (a - cf_head + i)).
{ intros a j Hin i Hi.
  destruct (prh_ledger_hblock B ly3 S3 Hp3 W3 mem3 (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D)
    a j (tp_most D) (tp_own D) HLED3 Hin) as (Hj0 & Hab & _ & Ha16 & _).
  pose proof (tpi_head_wide B HIMG) as HW8. unfold prh_head_wide in HW8.
  pose proof (alx_blocks segs B ARX LAWS ly3 S3 Hp3 W3 mem3 md3 (a - cf_head) (j + cf_head) HARJ Hab)
    as (Hal & H4096 & Hce & _).
  assert (Hrq : j + cf_head <= req_size (j + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (j + cf_head) 0); lia).
  assert (Hdj : zdisjoint (a - cf_head, req_size (j + cf_head)) (b1, req_size cap1)).
  { apply (sep_blocks_x segs B ARX LAWS ly3 S3 Hp3 W3 mem3 md3); [exact HARJ | exact Hab | exact Hblk|].
    intros Heq. injection Heq as Eb Ec. apply (Hbnl a j Hin). lia. }
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Hrq1 in Hdj.
  apply KVE; [lia | lia | lia | lia | lia]. }
assert (KROD : arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W3) (ms_mem msE))).
{ intros a Ha Ho He.
  assert (Hi : in_img segs a)
    by (destruct Ha as [(sg & Hs & _ & Hr) | Hr];
        [exists sg; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hi) as Hlo. unfold kLowMemEnd in Hlo. pose proof (KIMG a Hi) as Hni.
  rewrite KVE by (lia). exact (HROD a Ha Ho He). }
(* ---- the symbolic memory at the end: the record's two words and the NUL byte ---- *)
pmkst HS.
fit_reg HS (2%bv : bv 5) F2. fit_reg HS (3%bv : bv 5) F3. fit_reg HS (4%bv : bv 5) F4.
assert (G2 : spZ (ms_regs msE) = spZ regs3).
{ unfold spZ at 1. rewrite F2. fit_atom_reg. rewrite !ew_ewset_other by lia. rewrite OLD6, OLD5 by lia.
  rewrite (ER 2%bv 2%nat eq_refl). reflexivity. }
assert (G3 : getr (ms_regs msE) 3 = getr regs3 3).
{ rewrite F3. fit_atom_reg. rewrite !ew_ewset_other by lia. rewrite OLD6, OLD5 by lia.
  rewrite (ER 3%bv 3%nat eq_refl). reflexivity. }
assert (G4 : getr (ms_regs msE) 4 = getr regs3 4).
{ rewrite F4. fit_atom_reg. rewrite !ew_ewset_other by lia. rewrite OLD6, OLD5 by lia.
  rewrite (ER 4%bv 4%nat eq_refl). reflexivity. }
pose proof (st_ok_mem_ok segs _ _ _ HS) as (_ & HMO & _).
cbn [ms_mem restrict mkst abs_ss setpc ss_mem] in HMO.
pose proof (Forall_inv HMO) as HRN. pose proof (Forall_inv (Forall_inv_tail HMO)) as HRR.
unfold region_ok in HRN, HRR.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRN, HRR.
destruct HRN as (_ & _ & _ & HRNc). destruct HRR as (_ & _ & _ & HRRc).
pose proof (fit_val_mem_chunk1z _ _ _ (Forall_inv HRNc)) as VNUL.
pose proof (fit_val_mem_chunk8 _ _ _ 8 _ (Forall_inv HRRc)) as VLEN.
pose proof (fit_val_mem_chunk8 _ _ _ 0 _ (Forall_inv (Forall_inv_tail HRRc))) as VB1.
rewrite !ew_ewset_other in VNUL, VLEN, VB1 by lia.
rewrite X56, unsigned_lit_small in VNUL by lia. rewrite Ut6 in VLEN, VB1.
rewrite U_SAlu, !U_SOff, !ew_ewset_other, !OLD6, !OLD5 in VLEN by lia.
rewrite <- !U_SOff in VLEN. rewrite UN, UL0 in VLEN. cbn [zalu_raw] in VLEN.
rewrite zcanon_id in VLEN by (unfold M64; lia).
replace (tp_n D + tp_len0 D) with (tp_len0 D + tp_n D) in VLEN by lia.
rewrite !U_SOff, !ew_ewset_other, !OLD6, !OLD5 in VB1 by lia. rewrite <- !U_SOff in VB1. rewrite UB1 in VB1.
rewrite Z.add_0_r in VB1.
(* ---- the record at the end ---- *)
assert (HRECE : prhtx_rec W3 (ms_mem msE) (tp_t D) b1 (tp_len0 D + tp_n D) cap1 0).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|].
  split; [exact VB1|]. split; [exact VLEN|]. split.
  - apply (prh_val_mem_keep _ _ _ _ _ Mc). intros j Hj. apply prh_mbyte_of_aview.
    apply KVE; [lia | lia | lia | lia | lia].
  - apply (prh_val_mem_keep _ _ _ _ _ Mf). intros j Hj. apply prh_mbyte_of_aview.
    apply KVE; [lia | lia | lia | lia | lia]. }
(* ---- the buffer's bytes at the end ---- *)
assert (HBYE : bytes_at W3 (ms_mem msE) b1 ((tp_txt D ++ tp_src D) ++ [0])).
{ unfold bytes_at. apply garr8_app. split.
  - apply garr8_app. split.
    + apply (fit_garr8_move W3 W3 mem3 (ms_mem msE) b1 b1 (tp_txt D) HTXT).
      intros j Hj. apply KVE; [lia | lia | lia | lia | lia].
    + rewrite Hltxt.
      apply (fit_garr8_move W3 W3 (ms_mem ms2) (ms_mem msE) (tp_s D) (b1 + tp_len0 D) (tp_src D) Hsby2).
      intros j Hj. rewrite (KVC (b1 + tp_len0 D + Z.of_nat j) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact (Hcopy (Z.of_nat j) ltac:(lia)).
  - rewrite length_app, Nat2Z.inj_add, Hltxt, HSLEN.
    intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j.
    cbn [Z.of_nat nth]. split; [|lia]. rewrite Z.add_0_r.
    replace (b1 + (tp_len0 D + tp_n D)) with (b1 + tp_len0 D + tp_n D) by lia. exact VNUL. }
assert (HWRE : forall a, b1 <= a < b1 + cap1 -> writable_at segs (mrestrict (w_H W3) (ms_mem msE)) a).
{ pose proof (alx_blocks segs B ARX LAWS ly3 S3 Hp3 W3 (ms_mem msE) _ b1 cap1 (proj1 HJ) Hblk)
    as (_ & _ & _ & _ & HprE & _).
  intros a Ha. apply (apresent_writable segs). apply (proj1 (HprE a ltac:(lia))). }
assert (HRAE : range_addressable (aview segs (w_H W3) (ms_mem msE)) SHADOW_OFF b1 cap1).
{ apply (tpk_ra_keep (aview segs (w_H W3) mem3)); [|exact Hbra].
  intros x Hx. pose proof (tpk_shadow_lo x ltac:(lia)) as Hsx.
  pose proof (fit_sh_off b1 cap1 x b1 (b1 + cap1) Hbamr ltac:(lia) ltac:(lia) ltac:(lia)).
  apply KVE; [lia | lia | lia | lia | lia]. }
assert (HHUE : shadow_hull_vis (aview segs (w_H W3) (ms_mem msE)) b1 cap1).
{ apply (tpk_hull_keep (aview segs (w_H W3) mem3)); [|exact Hbhull].
  intros sx Hsx. pose proof (tpk_hull_lo b1 cap1 sx ltac:(lia) ltac:(lia) ltac:(lia) Hsx) as Hlo.
  pose proof (fit_hull_off b1 cap1 b1 cap1 sx b1 (b1 + cap1) Hbamr ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(lia) ltac:(lia) Hsx).
  apply KVE; [lia | lia | lia | lia | lia]. }
assert (HINVE : prhtx_inv B (tp_Lam D) ly3 S3 W3 (ms_mem msE) b1 (tp_len0 D + tp_n D) cap1
  (tp_txt D ++ tp_src D)).
{ split; [rewrite length_app, Nat2Z.inj_add, Hltxt, HSLEN; reflexivity|]. right.
  split; [lia|]. split; [lia|]. split; [exact Hblk|]. split; [exact HBYE|]. split; [lia|]. split; [lia|].
  split; [exact Hbamr|]. split; [exact HWRE|]. split; [exact HRAE|]. split; [exact HHUE | exact Hbnl]. }
assert (HPLE : prhtx_place ly3 S3 W3 (tp_regs D) (ms_mem msE) (tp_dw D) (tp_t D)).
{ split; [exact Hta|]. split; [exact Ht1|]. split; [exact Ht2|]. split.
  - intros a Ha. apply (apresent_writable segs). apply JEpres. lia.
  - apply (fit_ra_stack ly3 S3 Hp3 W3 (ms_mem msE) _ (tp_t D) 28 (proj1 HJ)); rewrite ?Elo, ?Ehi; lia. }
assert (HSRCE : bytes_at W3 (ms_mem msE) (tp_s D) (tp_src D)).
{ apply (tpk_bytes_at_rng W3 W3 mem3 (ms_mem msE)); [|exact Hsby].
  intros a Ha. rewrite HSLEN in Ha.
  apply KVE; [lia | pose proof (HDISJ a ltac:(lia)) as [Hx _]; lia |
    pose proof (HSDJ a ltac:(lia)); lia | lia | pose proof (HSDJ a ltac:(lia)); lia]. }
assert (HLEDE : prh_ledger B ly3 S3 Hp3 W3 (ms_mem msE) (tp_Lam D) (tp_peak D) (tp_cnt D) (tp_fail D) (tp_ran D)
  (tp_most D) (tp_own D)).
{ apply (prh_ledger_kept_aview B ly3 S3 Hp3 W3 mem3 ly3 S3 Hp3 W3 (ms_mem msE)); [exact HLED3 | exact KPST | | |].
  - intros a j i Hin Hi. exact (KHEAD a j Hin i Hi).
  - intros a j Hin Hab. exact Hab.
  - apply Permutation_refl. }
assert (HSAVE : tp_saved D W3 (ms_mem msE)).
{ assert (KSAV : forall a v, spZ (tp_regs D) - 104 <= a -> a + 8 <= spZ (tp_regs D) ->
    val_mem segs (mrestrict (w_H W3) mem3) a 8 v -> val_mem segs (mrestrict (w_H W3) (ms_mem msE)) a 8 v).
  { intros a v Ha1 Ha2 Hv. apply (prh_val_mem_keep _ _ _ _ _ Hv). intros j Hj. apply prh_mbyte_of_aview.
    apply KVE; [lia | lia | lia | lia | lia]. }
  pose proof HSAV as (S1' & S2' & S3' & S4' & S5' & S6' & S7' & S8' & S9' & S10' & S11' & S12' & S13').
  repeat split; apply KSAV; solve [lia | assumption]. }
(* ---- the END cut ---- *)
lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?mdx) _ =>
  assert (HATE : tp_at_END B SK CTX0 D ly3 S3 Hp3 W3 (ms_regs msE) (ms_mem msE) mdx k) end.
{ exists WS. split; [exact HBUD|]. split.
  - split; [exact HPRE|].
    split; [unfold tp_JR; eapply (ajournal_xw_unbase0R (SK := SK) segs B prh_pst _ RW);
      [exact HJ | exact (ajxR_wild HJw)]|].
    split; [exact HK|].
    split.
    { intros r Hr. cbn in Hr. destruct Hr as [<- | [<- | []]]; [rewrite G3 | rewrite G4];
      apply HKR; cbn; tauto. }
    split; [rewrite G2; exact HSP|]. split; [exact HSAVE|]. split; [exact HHP | exact KROD].
  - exists b1, cap1, 0, (tp_own D), (tp_src D).
    split.
    { split; [rewrite HSLEN; exact HRECE|]. split; [rewrite HSLEN; exact HINVE|].
      split; [exact HPLE|]. split; [exact HHP|]. split.
      - destruct HARM as [(Hn' & Eb & Ec & Ely & ES) | (Hlt & Ec & Hg & Hbb)];
        [left; split; [exact Eb | split; [exact Ec | rewrite Ely, ES; reflexivity]] | exact Hg].
      - destruct HARM as [(Hn' & Eb & Ec & Ely & ES) | (Hlt & Ec & Hg & Hbb)]; [rewrite ES; lia | lia]. }
    split.
    { left. split; [exact Hf0|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      unfold tp_cap1, TxModel.tx_cap1.
      pose proof HARM as HARM2. unfold tp_fitarm, tp_req, tp_need in HARM2.
      destruct HARM2 as [(Hn' & Eb & Ec & _) | (Hlt & Ec & _)];
      destruct (Z.leb_spec (tp_len0 D + tp_n D + 1) (tp_cap0 D)); lia. }
    split; [intros _; reflexivity|].
    split; [exact HSRCE|]. split; [exact HRL3|].
    split; [exact (proj1 HPOS) | split; [exact (proj2 HPOS) | exact HLEDE]]. }
pose proof (KEND ly3 S3 Hp3 W3 (ms_regs msE) (ms_mem msE) _ k HATE HPM) as HFIN.
unfold tp_cfg, tp_pc, TP_PC_END in HFIN. rewrite TP_OFF_val in HFIN.
replace (BASE + 15108 + 400) with (BASE + 15508) in HFIN by lia.
exact HFIN.
Qed.

End fit.
