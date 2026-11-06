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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO38.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1o YE09 YE1s YE1r YE1w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition VP_ENTRY {imgk : img} : Z := (0x420f4 + D_2c4).
Definition FP_REAL {imgk : img} : Z := (0x97ccc + D_10ec).
Definition VP_RET2 {imgk : img} : Z := (0x4558c + D_2c4).
Definition VP_RET1 {imgk : img} : Z := (0x44a1c + D_2c4).
Definition VP_WIN : Z := 2432.
Definition VPI_STK : Z := 9200.
Definition FMT {imgk : img} : Z := (0x14861 + D_20).
Lemma fp_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> sym_runN tfxsegs tbl_fp FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl_fp tbl_fp_ok YF8r.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|]. split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Lemma fp_phase_to {imgk : img} : forall (W : world tfxsegs) E stop ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfxsegs tbl_fp FUEL stop ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfxsegs tbl_fp tbl_fp_ok YF8r.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|]. split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Definition vpA_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [((0xa2150 + D_10f0), 8, [(0, 8%N, (0x13bce8 + D_10c0))]); ((0x13bd3c + D_10c0), 1, [(0, 1%N, 1)]); ((0xa3ee0 + D_10f0), 16, [(0, 8%N, (0x9addc + D_10ec)); (8, 8%N, (0x97ccc + D_10ec))])].
Lemma vpA_rodata_chk {imgk : img} : forall ly, rodata_chk ly vpA_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition SH_LO {imgk : img} : Z := (0x7fffa908 + D_8).  Definition SH_HI {imgk : img} : Z := (0x7fffa910 + D_8).
Definition shz {imgk : img} : YQ0b.region := YQ0b.mkRegion None SH_LO SH_HI SH_LO SH_LO [YQ0b.mkChunk SH_LO (CZero (SH_HI - SH_LO))].
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Definition stkA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- VP_WIN) 0 (- VP_WIN) 0 [].
Definition apr : YQ0b.region := YQ0b.mkRegion (Some 11%nat) 0 8 0 0 [YQ0b.mkChunk 0 (CVal 8 (SLit 0))].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (11%nat, mkAF (2^44) (2^47) 3)].
Definition regsA {imgk : img} : list sv := ltac:(img_eval_last (fun imgk : img => ((firstn 10 sr_atoms ++ [SLit FMT] ++ skipn 11 sr_atoms)))).
Definition memA {imgk : img} : smem := stkA :: apr :: shz :: img_ro_region :: map ro_region vpA_rodata.
Definition ssA {imgk : img} : sstate := mkSS VP_ENTRY regsA memA None (mkFacts factsA [] []).
Definition RUNTOR {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_fp FUEL FP_REAL s.
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_fp FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YQ09.add_cond s (mkAC c a b).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition eA1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR ssA)))).
Lemma r_A1 {imgk : img} : RUNTOR ssA = (eA1, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2264))) (SLit 15)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition eA2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)))))).
Lemma r_A2 {imgk : img} : RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)) = (eA2, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2312))) (SLit 15)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition eA {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR (AC eA2 BC_NE (RG eA2 13) (SLit 0)))))).
Lemma r_A3 {imgk : img} : RUNTOR (AC eA2 BC_NE (RG eA2 13) (SLit 0)) = (eA, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition SAVEDA {imgk : img} : list (Z * sv) :=
[(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-80, SOff 18 0); (-72, SOff 11 0); (-64, SLit FMT); (-56, SLit VP_RET1)].
Definition KEPTA : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? FP_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - VP_WIN) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SLit F_STDOUT) && reg_is ss 11 (SLit FMT) && reg_is ss 12 (SOff 11 0) &&
reg_is ss 1 (SLit VP_RET2) && reg_is ss 2 (SOff 2 (-96)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (fst p) (snd p)) SAVEDA.
Lemma shapeA_ok {imgk : img} : shapeA eA = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.
Lemma br_memset_align : forall E sp0 d, bv_unsigned (ew E 2) = sp0 -> sp0 mod 16 = 0 -> d mod 16 = 8 -> 0 <= d <= 4096 -> 2 ^ 44 <= sp0 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (- d))) (SLit 15))) (sv_denot E (SLit 0)) = false.
Proof.
intros E sp0 d H2 Hal Hd Hdr Hsp. rewrite branch_eq_U, !U_SAlu, !U_SLit, U_SOff, H2. cbn [zalu_raw].
rewrite (zcanon_small 40), (zcanon_small 15), (zcanon_small 0), (zcanon_small (sp0 + - d)) by img_lia.
assert (Hm : (sp0 + - d) mod 16 = 8).
{ replace (sp0 + - d) with (sp0 - d) by img_lia. rewrite Zminus_mod, Hal, Hd. img_refl. }
assert (Hand : Z.land (Z.lor 40 (sp0 + - d)) 15 = 8).
{ rewrite Z.land_lor_distr_l. img_change 15 with (Z.ones 4). rewrite !Z.land_ones by img_lia. img_change (2 ^ 4) with 16. rewrite Hm. img_refl. }
assert (Hlt : Z.lor 40 (sp0 + - d) < 2 ^ 64).
{ destruct (Z.eq_dec (Z.lor 40 (sp0 + - d)) 0) as [E0|E0]; [img_try (rewrite E0; img_lia)|].
img_apply Z.log2_lt_pow2; [img_try (pose proof (Z.lor_nonneg 40 (sp0 + - d)); img_lia)|]. rewrite Z.log2_lor by img_lia.
img_apply Z.max_lub_lt; [img_try ((img_case; cbv); img_refl) | img_try (img_apply Z.log2_lt_pow2; img_lia)]. }
rewrite (zcanon_small (Z.lor 40 (sp0 + - d))) by (img_try (pose proof (Z.lor_nonneg 40 (sp0 + - d)); img_lia)).
rewrite Hand. img_refl.
Qed.
Definition epi_chunks {imgk : img} : list YQ0b.chunk :=
[YQ0b.mkChunk 88 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 80 (CVal 8 (SOff 33 0)); YQ0b.mkChunk 72 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 16 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 24 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 32 (CVal 8 (SLit FMT));
YQ0b.mkChunk 40 (CVal 8 (SLit VP_RET1))].
Definition ss_epi {imgk : img} : sstate := mkSS VP_RET2 sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 96 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition shapeE (ss : sstate) : bool :=
reg_is ss 1 (SOff 32 0) && reg_is ss 8 (SOff 33 0) && reg_is ss 9 (SOff 34 0) && reg_is ss 18 (SOff 35 0) && reg_is ss 2 (SOff 2 96) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Lemma shapeE_ok {imgk : img} : shapeE epi_e = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition vpf_saved {imgk : img} (regs : bvmap 5 word) (m : word -> option byte) (sp0 : Z) : Prop :=
val_mem tfxsegs m (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\ val_mem tfxsegs m (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfxsegs m (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\ val_mem tfxsegs m (sp0 - 80) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfxsegs m (sp0 - 72) 8 (sp0 + 24) /\ val_mem tfxsegs m (sp0 - 64) 8 FMT /\ val_mem tfxsegs m (sp0 - 56) 8 VP_RET1.
Lemma vpf_saved_kept {imgk : img} : forall regs (H : word -> bool) (m m' : word -> option byte) sp0,
vpf_saved regs (mrestrict H m) sp0 -> (forall b, sp0 - 96 <= b < sp0 -> aview tfxsegs H m' b = aview tfxsegs H m b) ->
vpf_saved regs (mrestrict H m') sp0.
Proof.
intros regs H m m' sp0 (V1 & V2 & V3 & V4 & V5 & V6 & V7) Heq.
assert (T : forall a v, sp0 - 96 <= a -> a + 8 <= sp0 -> val_mem tfxsegs (mrestrict H m) a 8 v -> val_mem tfxsegs (mrestrict H m') a 8 v).
{ intros a v H1 H2 Hv. eapply val_mem_kept; [|img_try (img_exact Hv)]. intros k Hk. img_apply Heq. cbn in Hk. img_lia. }
repeat split; (img_apply T; [img_lia | img_lia | img_try (assumption)]).
Qed.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Theorem tfx_vprintf_icpt_A : forall ly S (W : world tfxsegs) regs mem md T,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + VPI_STK <= spZ regs ->
(forall a, spZ regs - VPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
spZ regs + 32 <= 2 ^ 47 ->
getr regs 10 = w64 FMT -> getr regs 11 = w64 (spZ regs + 24) ->
val_mem tfxsegs (mrestrict (w_H W) mem) (spZ regs + 24) 8 0 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview tfxsegs (w_H W) mem) FMT 4 ->
AI tfxsegs (w_H W) (w_A W) md ->
(forall regs1 mem1 md1,
ecall_pre tfxsegs B ly S W regs1 mem1 md1 ->
spZ regs1 = spZ regs - 96 -> raZ regs1 = VP_RET2 ->
getr regs1 10 = w64 F_STDOUT -> getr regs1 11 = w64 FMT -> getr regs1 12 = w64 (spZ regs + 24) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr regs1 r = getr regs r) ->
same_but_materialized md md1 ->
(forall z : word, ~ (spZ regs - VP_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - VP_WIN <= a < spZ regs) -> aview tfxsegs (w_H W) mem1 a = aview tfxsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
vpf_saved regs (mrestrict (w_H W) mem1) (spZ regs) ->
AI tfxsegs (w_H W) (w_A W) md1 ->
srealizes tfxsegs (cfg_at tfxsegs A_vfprintf regs1 mem1 md1) T) ->
srealizes tfxsegs (cfg_at tfxsegs VP_ENTRY regs mem md) T.
Proof.
intros ly S W regs mem md T HPRE Hstk Hpres Hsphi G10 G11 Harg Hro HZ HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold VPI_STK in *.
assert (HFMT : FMT = (84065 + D_20)) by img_refl. assert (HFO : F_STDOUT = (682048 + D_10f0)) by img_refl.
assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try ((subst sp0; cbv beta); img_lia)).
pose proof YF8r.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfxsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfxsegs H m' b = aview tfxsegs H m b) -> val_mem tfxsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf. img_apply (YF8r.val_mem_ext (mrestrict H m)); [|img_try (img_exact Hv)]. intros j Hj. img_apply mbyte_of_aview. img_apply Hf. img_lia. }
unfold cfg_at. img_change (w64 VP_ENTRY) with (Z_to_bv 64 VP_ENTRY).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (EE11 : ew EE 11 = Z_to_bv 64 (sp0 + 24)) by (img_try (rewrite (EEreg 11%nat 11%bv eq_refl); img_exact G11)).
assert (EE11u : bv_unsigned (ew EE 11) = sp0 + 24) by (img_try (rewrite EE11; img_apply unsigned_lit_small; img_lia)).
assert (HZ' : forall s, SH_LO <= s < SH_HI -> aview tfxsegs H mem s = Some 0).
{ intros s Hs. img_apply HZ. unfold SH_LO, SH_HI in Hs.
match goal with |- ?a <= s < ?b => let a' := img_ev constr:(a) in img_change a with a'; let b' := img_ev constr:(b) in img_change b with b' end. img_lia. }
assert (HS0 : st_ok tfxsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 VP_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
img_apply (st_ok_regs tfxsegs EE (mkSS VP_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (YE0v.Env_reg regs _ 10 10%bv eq_refl), G10; img_refl) ] |]).
destruct Hr. }
unfold memA, EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [| img_try (img_apply Forall_cons; [| img_apply Forall_cons; [| img_apply Forall_cons; [img_apply Hro | img_exact (rodata_ok B TB vpA_rodata ly S H mem EE (vpA_rodata_chk ly) (proj1 HAR))]]])].
+ unfold stkA, VP_WIN. img_apply (region_ok_stack tfxsegs EE _ 2 sp0 (- 2432)); [img_try (img_exact EE2) | img_lia | img_lia |].
intros a Ha. img_apply YE0v.apresent_writable. img_apply HpresE. (subst sp0; cbv beta). img_lia.
+ unfold apr, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]. rewrite EE11u.
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply (chunk_ok_val tfxsegs EE _ (sp0 + 24) 0 8 (SLit 0) 0); [img_refl | img_try (cbn; img_lia) | img_try (cbn; img_lia) | img_try (rewrite Z.add_0_r; img_exact Harg)].
+ unfold shz, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold SH_LO, SH_HI. split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|]. img_apply HZ'. unfold SH_LO, SH_HI. cbn in Hi. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkA, apr, shz, img_ro_region, vpA_rodata, icpt_rodata, ro_region, extent_of_region, VP_WIN, SH_LO, SH_HI, IMG_RO_LO, IMG_RO_HI.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite EE2, EE11u.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE11u.
img_change (2 ^ 4) with 16. img_change (2 ^ 3) with 8. repeat split; try ((subst sp0; cbv beta); img_lia); try img_exact Hal16.
replace (sp0 + 24) with ((3 + 2 * (sp0 / 16)) * 8) by (img_try (pose proof (Z.div_mod sp0 16 ltac:(img_lia)) as Dm; rewrite Hal16 in Dm; img_lia)). img_apply Z_mod_mult. }
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HS0 r_A1) HAI0).
intros Wa ca _ HAIa (-> & msa & mata & -> & HSa & HFa & HFra). cbn [cfg_model] in HAIa. rewrite ?wvb_wvb in HAIa |- *.
assert (MEQa : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msa z = mem z).
{ intros z Hz. img_apply (HFa z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- VP_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold VP_WIN in *. img_lia. }
clear HFa HFra.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG eA1 13) (SLit 0) HSa (br_memset_align EE sp0 2264 EE2 Hal16 eq_refl ltac:(img_lia) ltac:(img_lia))) as HSa'.
img_change (neg_bc BC_EQ) with BC_NE in HSa'. clear HSa.
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSa' r_A2) HAIa).
intros Wb cb _ HAIb (-> & msb & matb & -> & HSb & HFb & HFrb). cbn [cfg_model] in HAIb. rewrite ?wvb_wvb in HAIb |- *.
assert (MEQb : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msb z = mem z).
{ intros z Hz. rewrite (HFb z); [img_try (img_apply MEQa; img_exact Hz)|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- VP_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold VP_WIN in *. img_lia. }
clear HFb HFrb.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG eA2 13) (SLit 0) HSb (br_memset_align EE sp0 2312 EE2 Hal16 eq_refl ltac:(img_lia) ltac:(img_lia))) as HSb'.
img_change (neg_bc BC_EQ) with BC_NE in HSb'. clear HSb.
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSb' r_A3) HAIb).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [img_try (img_apply MEQb; img_exact Hz)|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- VP_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold VP_WIN in *. img_lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| img_try (rewrite <- Hi; img_exact HK')]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
assert (CK : forall off v z, In (off, v) SAVEDA -> sv_denot EE v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> val_mem tfxsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 z).
{ intros off v z Hj Hv Hz. rewrite forallb_forall in HSV. specialize (HSV (off, v) Hj). cbn [fst snd] in HSV.
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. (subst c; cbv beta).
pose proof (st_ok_mem_ok tfxsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
img_change 8%nat with (N.to_nat 8). img_apply (val_of_chunk_ok tfxsegs EE _ _ off 8 v _ Hck Hv); cbn; img_lia. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 F_STDOUT) by (img_try (rewrite (RD 10%bv (SLit F_STDOUT) R10); img_refl)).
assert (Q11 : getr regs1 11 = w64 FMT) by (img_try (rewrite (RD 11%bv (SLit FMT) R11); img_refl)).
assert (Q12 : getr regs1 12 = w64 (sp0 + 24)) by (img_try (rewrite (RD 12%bv (SOff 11 0) R12); cbn [sv_denot]; rewrite EE11u, Z.add_0_r; img_refl)).
assert (Q1 : getr regs1 1 = w64 VP_RET2) by (img_try (rewrite (RD 1%bv (SLit VP_RET2) R1); img_refl)).
assert (Q2 : getr regs1 2 = w64 (sp0 - 96)) by (img_try (rewrite (RD 2%bv (SOff 2 (-96)) R2); cbn [sv_denot]; rewrite EE2; img_refl)).
assert (Q3 : getr regs1 3 = getr regs 3) by (img_try (img_exact (RK 3%bv 3%nat eq_refl ltac:(cbn; img_lia)))).
assert (Q4 : getr regs1 4 = getr regs 4) by (img_try (img_exact (RK 4%bv 4%nat eq_refl ltac:(cbn; img_lia)))).
assert (R1sp : spZ regs1 = sp0 - 96) by (img_try (unfold spZ; rewrite Q2; unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (R1ra : raZ regs1 = VP_RET2) by (img_try (unfold raZ; rewrite Q1; unfold w64; img_apply unsigned_lit_small; unfold VP_RET2; img_lia)).
pose proof (st_ok_restrict_mkst tfxsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (img_try ((subst md1; cbv beta); img_apply with_vm_backing_same)).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2432 <= a < sp0) -> aview tfxsegs H (ms_mem ms1) a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PRS1 : forall a, sp0 - 2432 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. img_apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold VP_WIN. img_lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (YE0v.apresent_mod _ (ms_mem ms1) a). rewrite (YE0v.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [img_try (img_apply (apresent_same H mem (ms_mem ms1) a'); [img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hp])|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PRS1; img_lia)|].
img_apply (apresent_same H mem (ms_mem ms1) a'); [img_try (img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hp)]. }
assert (HAR1 : AR tfxsegs B ly S W (ms_mem ms1) md1).
{ img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. img_apply AV1; [img_try (img_exact Hr)|]. intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ (ms_mem ms1) a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [img_try (rewrite AV1 by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AV1 by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. img_apply PRS1. img_lia.
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_exact (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(img_try (unfold sp0 in *; img_lia)) ltac:(img_lia)). }
assert (HPRE1 : ecall_pre tfxsegs B ly S W regs1 (ms_mem ms1) md1).
{ split; [img_try (img_exact HAR1)|]. split; [img_try (rewrite Q1; img_apply (ret_ok_lit VP_RET2); [unfold VP_RET2; img_lia | img_refl])|].
split; [img_try (rewrite R1sp; replace (sp0 - 96) with (sp0 + (-6) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16)|].
split; [img_try (rewrite R1sp; unfold ESTACK; unfold sp0 in *; img_lia)|]. split; [img_try (rewrite R1sp; unfold sp0 in *; img_lia)|].
split; [img_try (intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; img_apply PM1; img_apply Hpres; unfold sp0 in *; img_lia)|].
split; [img_try (rewrite Q3; img_exact Hgp) | img_try (rewrite Q4; img_exact Htp)]. }
img_change (mkCfg (mkst regs1 (Z_to_bv 64 FP_REAL) (ms_mem ms1) (seg_rom tfxsegs)) md1) with (cfg_at tfxsegs A_vfprintf regs1 (ms_mem ms1) md1).
img_apply (HK regs1 (ms_mem ms1) md1 HPRE1 R1sp R1ra Q10 Q11 Q12 Q3 Q4 RK MF1 ltac:(img_try (unfold VP_WIN; img_exact MEQ1)) AV1 PM1).
-
assert (U : forall (r : bv 5), sv_denot EE (SOff (Z.to_nat (bv_unsigned r)) 0) = Z_to_bv 64 (bv_unsigned (getr regs r))).
{ intros r. cbn [sv_denot]. rewrite (EEreg (Z.to_nat (bv_unsigned r)) r) by (img_try (pose proof (bv_unsigned_in_range 5 r); img_lia)). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
pose proof (fun (r : bv 5) => u64_range (getr regs r)) as UR.
split; [| img_try (split; [| split; [| split; [| split; [| split]]]])].
+ replace (sp0 - 8) with (sp0 + -8) by img_lia. img_apply (CK (-8) (SOff 1 0)); [img_try (cbn; tauto) | img_try (img_exact (U 1%bv)) | img_try (img_apply UR)].
+ replace (sp0 - 16) with (sp0 + -16) by img_lia. img_apply (CK (-16) (SOff 8 0)); [img_try (cbn; tauto) | img_try (img_exact (U 8%bv)) | img_try (img_apply UR)].
+ replace (sp0 - 24) with (sp0 + -24) by img_lia. img_apply (CK (-24) (SOff 9 0)); [img_try (cbn; tauto) | img_try (img_exact (U 9%bv)) | img_try (img_apply UR)].
+ replace (sp0 - 80) with (sp0 + -80) by img_lia. img_apply (CK (-80) (SOff 18 0)); [img_try (cbn; tauto) | img_try (img_exact (U 18%bv)) | img_try (img_apply UR)].
+ replace (sp0 - 72) with (sp0 + -72) by img_lia. img_apply (CK (-72) (SOff 11 0)); [img_try (cbn; tauto) | img_try (cbn [sv_denot]; rewrite EE11u, Z.add_0_r; img_refl) | img_lia].
+ replace (sp0 - 64) with (sp0 + -64) by img_lia. img_apply (CK (-64) (SLit FMT)); [img_try (cbn; tauto) | img_refl | img_try (rewrite HFMT; img_lia)].
+ replace (sp0 - 56) with (sp0 + -56) by img_lia. img_apply (CK (-56) (SLit VP_RET1)); [img_try (cbn; tauto) | img_refl | img_try (unfold VP_RET1; img_lia)].
- img_exact HAI1.
Qed.
Theorem tfx_vprintf_icpt_E : forall (W : world tfxsegs) (regs regs2 : bvmap 5 word) mem2 md2 (T : TSet),
2 ^ 44 <= spZ regs -> spZ regs + 32 <= 2 ^ 47 -> spZ regs mod 16 = 0 -> YK0s.ret_ok (getr regs 1) ->
getr regs2 2 = w64 (spZ regs - 96) ->
vpf_saved regs (mrestrict (w_H W) mem2) (spZ regs) ->
AI tfxsegs (w_H W) (w_A W) md2 ->
(forall regs3 mem3 md3,
(forall z, mem3 z = mem2 z) ->
getr regs3 2 = getr regs 2 -> getr regs3 1 = getr regs 1 -> getr regs3 8 = getr regs 8 -> getr regs3 9 = getr regs 9 -> getr regs3 18 = getr regs 18 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] ->
getr regs3 r = getr regs2 r) ->
same_but_materialized md2 md3 -> AI tfxsegs (w_H W) (w_A W) md3 ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs3 mem3 md3) T) ->
srealizes tfxsegs (cfg_at tfxsegs VP_RET2 regs2 mem2 md2) T.
Proof.
intros W regs regs2 mem2 md2 T Hsp44 Hsphi Hal16 Hret R4sp (V1 & V2 & V3 & V4 & V5 & V6 & V7) HAI2 HK.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
pose proof YF8r.Hwx_tfa as Hwx. assert (HFMT : FMT = (84065 + D_20)) by img_refl.
unfold cfg_at. img_change (w64 VP_RET2) with (Z_to_bv 64 VP_RET2).
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)]).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 96).
{ (subst E4; cbv beta). rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R4sp. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (HSe : st_ok tfxsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 VP_RET2) mem2 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)]) with E4.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 96) by (img_try (symmetry; img_exact E4_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) off w z, nth_error [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)] j = Some w ->
bv_unsigned w = z -> val_mem tfxsegs (mrestrict H mem2) (sp0 - 96 + off) 8 z ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem2) (sp0 - 96) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off w z Hnth Hz Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 96) off 8 _ z).
- cbn [sv_denot]. (subst E4; cbv beta). rewrite (ew_Ereg_extra regs2 _ j), (nth_error_nth _ _ _ Hnth), Z.add_0_r, <- Hz, Z_to_bv_bv_unsigned. img_refl.
- (subst z; cbv beta). pose proof (u64_range w). img_zside.
- img_zside.
- img_exact Hv. }
assert (CKL : forall off z, 0 <= z < 2 ^ 64 -> val_mem tfxsegs (mrestrict H mem2) (sp0 - 96 + off) 8 z ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem2) (sp0 - 96) (YQ0b.mkChunk off (CVal 8 (SLit z)))).
{ intros off z Hz Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 96) off 8 _ z); [img_refl | img_try (img_zside) | img_try (img_zside) | img_try (img_exact Hv)]. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK4 0%nat 88 (getr regs 1) _ eq_refl eq_refl). replace (sp0 - 96 + 88) with (sp0 - 8) by img_lia. img_exact V1.
+ img_apply (CK4 1%nat 80 (getr regs 8) _ eq_refl eq_refl). replace (sp0 - 96 + 80) with (sp0 - 16) by img_lia. img_exact V2.
+ img_apply (CK4 2%nat 72 (getr regs 9) _ eq_refl eq_refl). replace (sp0 - 96 + 72) with (sp0 - 24) by img_lia. img_exact V3.
+ img_apply (CK4 3%nat 16 (getr regs 18) _ eq_refl eq_refl). replace (sp0 - 96 + 16) with (sp0 - 80) by img_lia. img_exact V4.
+ img_apply (CK4 4%nat 24 (Z_to_bv 64 (sp0 + 24)) (sp0 + 24) eq_refl ltac:(img_try (img_apply unsigned_lit_small; img_lia))). replace (sp0 - 96 + 24) with (sp0 - 72) by img_lia. img_exact V5.
+ img_apply (CKL 32 FMT ltac:(img_try (rewrite HFMT; img_lia))). replace (sp0 - 96 + 32) with (sp0 - 64) by img_lia. img_exact V6.
+ img_apply (CKL 40 VP_RET1 ltac:(img_try (unfold VP_RET1; img_lia))). replace (sp0 - 96 + 40) with (sp0 - 56) by img_lia. img_exact V7.
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
img_change (2 ^ 4) with 16. repeat split; try img_lia.
replace (sp0 - 96) with (sp0 + (-6) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
eapply (SRr_srealizes tfxsegs W _ _ T (fp_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI2).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem2 z) by (img_try (intros z; img_apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md2) mat' md2)) T); [ | img_try (img_exact HAI5) | ].
{ eapply (SRr_ret_at tfxsegs tbl_fp tbl_fp_ok Hwx W E4); [img_try (img_exact HS5) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
pose proof shapeE_ok as HshE. unfold shapeE in HshE.
apply andb_prop in HshE as [HshE HKE]. apply andb_prop in HshE as [HshE P2]. apply andb_prop in HshE as [HshE P18].
apply andb_prop in HshE as [HshE P9]. apply andb_prop in HshE as [P1 P8].
assert (RD : forall (r : bv 5) v, reg_is epi_e (bv_unsigned r) v = true -> getr (ms_regs ms5) r = sv_denot E4 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H E4 epi_e ms5 r HS5). }
assert (X : forall j w, nth_error [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)] j = Some w -> ew E4 (32 + j) = w)
by (img_try (intros jj w Hnth; (subst E4; cbv beta); rewrite (ew_Ereg_extra regs2 _ jj); img_exact (nth_error_nth _ _ _ Hnth))).
pose proof (X 0%nat _ eq_refl) as X0. pose proof (X 1%nat _ eq_refl) as X1. pose proof (X 2%nat _ eq_refl) as X2. pose proof (X 3%nat _ eq_refl) as X3.
cbn [Nat.add] in X0, X1, X2, X3.
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (img_try (intros ii rr Hnth; (subst E4; cbv beta); img_exact (ew_Ereg_nat regs2 _ ii rr Hnth))).
assert (P1' : getr (ms_regs ms5) 1 = getr regs 1) by (img_try (rewrite (RD 1%bv (SOff 32 0) P1); cbn [sv_denot]; rewrite X0, Z.add_0_r, Z_to_bv_bv_unsigned; img_refl)).
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite P1'; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hret)).
img_apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat6 md2) MEQ5).
- rewrite (RD 2%bv (SOff 2 96) P2). cbn [sv_denot]. rewrite E4_2. unfold sp0, spZ. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 2)) at 2. f_equal. img_lia.
- img_exact P1'.
- rewrite (RD 8%bv (SOff 33 0) P8). cbn [sv_denot]. rewrite X1, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite (RD 9%bv (SOff 34 0) P9). cbn [sv_denot]. rewrite X2, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite (RD 18%bv (SOff 35 0) P18). cbn [sv_denot]. rewrite X3, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- intros r i Hi Hin. rewrite forallb_forall in HKE. rewrite Hi in Hin. specialize (HKE _ Hin). cbn beta in HKE. rewrite <- Hi, Nat2Z.id in HKE.
rewrite (RD r (SOff i 0)); [| img_try (rewrite <- Hi; img_exact HKE)]. cbn [sv_denot]. rewrite (Y i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- rewrite <- (wvb_collapse (m_vm_lazy md2) mat6 mat5 md2). eapply same_but_materialized_trans; [img_try (img_apply with_vm_backing_same) | img_try (img_apply with_vm_backing_same)].
- img_exact HAI6.
Qed.
End g.
End f.
