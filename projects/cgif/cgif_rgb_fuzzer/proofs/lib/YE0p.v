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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1o YE09 YE1s YE1n YE1r YE1t YE16 YF3k YE1f YE1h.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section g. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition FP_ENTRY {imgk : img} : Z := (0x42100 + D_2c4).
Definition FP_REAL {imgk : img} : Z := (0x97ccc + D_10ec).
Definition FP_RET {imgk : img} : Z := (0x459a8 + D_2c4).
Definition FP_ALIGN {imgk : img} : Z := (0x6448c + D_2c4).
Definition FP_WIN : Z := 2432.
Definition FPI_STK : Z := 9216.
Definition FMT {imgk : img} : Z := (0x1d7cd + D_m9).
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
Definition fpA_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [((0xa2150 + D_10f0), 8, [(0, 8%N, (0x13bce8 + D_10c0))]); ((0x13bd3c + D_10c0), 1, [(0, 1%N, 1)]); ((0xa3ee8 + D_10f0), 8, [(0, 8%N, (0x97ccc + D_10ec))])].
Lemma fpA_rodata_chk {imgk : img} : forall ly, rodata_chk ly fpA_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition SH_LO : Z := 0x7fffbaf8.  Definition SH_HI : Z := 0x7fffbb00.
Definition shz : YQ0b.region := YQ0b.mkRegion None SH_LO SH_HI SH_LO SH_LO [YQ0b.mkChunk SH_LO (CZero (SH_HI - SH_LO))].
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Definition stkA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- FP_WIN) 0 (- FP_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 1 (2^47) 0)].
Definition regsA {imgk : img} : list sv := ltac:(img_eval_last (fun imgk : img => ((firstn 11 sr_atoms ++ [SLit FMT] ++ skipn 12 sr_atoms)))).
Definition memA {imgk : img} : smem := stkA :: shz :: img_ro_region :: map ro_region fpA_rodata.
Definition ssA {imgk : img} : sstate := mkSS FP_ENTRY regsA memA None (mkFacts factsA [] []).
Definition RUNTOR {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_fp FUEL FP_REAL s.
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_fp FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YQ09.add_cond s (mkAC c a b).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk {imgk : img} (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition eA1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR ssA)))).
Lemma r_A1 {imgk : img} : RUNTOR ssA = (eA1, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2328))) (SLit 15)) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition FP_LW {imgk : img} : Z := (0x44f08 + D_2c4).
Definition FP_SLCALL {imgk : img} : Z := (0x44f80 + D_2c4).
Definition FP_CHKEND {imgk : img} : Z := (0x44ee0 + D_2c4).
Definition OSP : Z := -2352.
Definition CLOBP : list (bv 5) := (CLOB ++ [23%bv])%list.
Definition RUNTOS {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_fp FUEL A_ISL s.
Definition eA2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)))))).
Lemma r_A2 {imgk : img} : RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)) = (eA2, RS_stopped (SR_load (Some 2%nat) (-2324))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition rA2 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => ((hd stkA (ss_mem eA2))))).
Definition restA2 {imgk : img} : list YQ0b.region := ltac:(img_eval_last (fun imgk : img => ((tl (ss_mem eA2))))).
Lemma memA2_eq {imgk : img} : ss_mem eA2 = rA2 :: restA2. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition eA2' {imgk : img} : sstate := set_regs_pc eA2 [((11%bv : bv 5), SLit 0)] (ss_pc eA2 + 4).
Definition eA3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOS eA2')))).
Lemma r_A3 {imgk : img} : RUNTOS eA2' = (eA3, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition rA3 {imgk : img} : YQ0b.region := ltac:(img_eval_last (fun imgk : img => ((hd stkA (ss_mem eA3))))).
Definition restA3 {imgk : img} : list YQ0b.region := ltac:(img_eval_last (fun imgk : img => ((tl (ss_mem eA3))))).
Lemma memA3_eq {imgk : img} : ss_mem eA3 = rA3 :: restA3. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition rest_okb (l : list YQ0b.region) : bool :=
forallb (fun r => obase_eqb (YQ0b.r_base r) None && (0 <=? YQ0b.r_lo r) && (YQ0b.r_hi r <=? 2 ^ 43) && (YQ0b.r_whi r <=? YQ0b.r_wlo r)) l.
Lemma rest_okb_sound : forall l, rest_okb l = true ->
forall r, In r l -> YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43 /\ YQ0b.r_whi r <= YQ0b.r_wlo r.
Proof.
intros l Hl r Hr. unfold rest_okb in Hl. rewrite forallb_forall in Hl. specialize (Hl r Hr). cbn beta in Hl.
apply andb_prop in Hl as [Hl H4]. apply andb_prop in Hl as [Hl H3]. apply andb_prop in Hl as [H1 H2].
apply obase_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. repeat split; assumption.
Qed.
Lemma restA3_ok {imgk : img} : rest_okb restA3 = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition fp_after {imgk : img} (k : nat) (ss : sstate) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS FP_CHKEND (sr_sets (ss_regs ss) (junk_upd k CLOBP))
(YQ0b.mkRegion (YQ0b.r_base r0) (YQ0b.r_lo r0) (YQ0b.r_hi r0) (YQ0b.r_wlo r0) (YQ0b.r_whi r0)
(List.filter (fun c => OSP <=? YQ0b.c_off c) (YQ0b.r_chunks r0)) :: rest)
None (ss_facts ss)
| [] => ss
end.
Definition eA3r {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fp_after 32 eA3))).
Lemma eA3r_eq {imgk : img} : fp_after 32 eA3 = eA3r. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition eA {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR eA3r)))).
Lemma r_A4 {imgk : img} : RUNTOR eA3r = (eA, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition shapeS {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? A_ISL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_lo r =? - FP_WIN) && (YQ0b.r_hi r =? 0) && (YQ0b.r_wlo r =? - FP_WIN) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 1 (SLit FP_SLCALL) && reg_is ss 2 (SOff 2 OSP) && reg_is ss 10 (SOff 12 0) && reg_is ss 22 (SOff 12 0).
Lemma shapeS_ok {imgk : img} : shapeS eA3 = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition chunk1_is (off : Z) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 1 && sv_eqb e (SLit 0) | _ => false end.
Definition W_LW {imgk : img} : Z := ltac:(img_eval_last (fun imgk : img => (match clookup tbl_fp FP_LW with Some w => w | None => 0 end))).
Lemma lw_fetch {imgk : img} : clookup tbl_fp FP_LW = Some W_LW /\ decode_any (Z_to_bv 32 W_LW) = Some (Load SZ4 true 11%bv 24%bv (4068%bv : bv 12), 4).
Proof. split; [img_try ((try img_inst; img_case; vm_compute); img_refl) | img_try ((img_case; vm_refl_bv))]. Qed.
Lemma lw_bytes_ok {imgk : img} : forallb (fun k => existsb (chunk1_is (-2324 + k)) (YQ0b.r_chunks rA2)) [0; 1; 2; 3] = true
/\ ss_pc eA2 = FP_LW /\ reg_is eA2 24 (SOff 2 (-2296)) = true /\ YQ0b.r_base rA2 = Some 2%nat.
Proof. img_case; vm_compute. all: repeat split; img_refl. Qed.
Lemma not_clobp_cases : forall r : bv 5, reg_in r CLOBP = false -> r = 0%bv \/ (acallee_saved (bv_unsigned r) /\ bv_unsigned r <> 23).
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin. unfold acallee_saved.
repeat (destruct Hin as [<-|Hin];
[first [ left; img_refl
| vm_compute in Hr; discriminate
| right;
match goal with |- context [bv_unsigned ?x] =>
let v := img_ev (bv_unsigned x) in img_change (bv_unsigned x) with v end;
img_lia ] |]).
destruct Hin.
Qed.
Lemma fp_lw_zero {imgk : img} : forall (W : world tfxsegs) E ss ms md (rd rs : bv 5) (imm : bv 12) (w : Z) (h : Z) (K : nat),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_fp (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd rs imm, 4) -> bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h + bv_signed imm -> h + bv_signed imm + 4 <= 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
(forall k, 0 <= k < 4 -> mbyte tfxsegs (mrestrict (w_H W) (ms_mem ms)) (h + bv_signed imm + k) = Some (Z_to_bv 8 0)) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfxsegs E (set_regs_pc ss [(rd, SLit 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\ ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs imm w h K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh4 Hh64 Hb. pose proof YF8r.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_fp_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|img_refl]. apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (img_try (rewrite (st_ok_restrict_reg tfxsegs (w_H W) E ss ms rs HS); img_exact Hrs)).
assert (Hrdn : rdn tfxsegs (mrestrict (w_H W) (ms_mem ms)) (v_addi (getr (ms_regs ms) rs) (bv_signed imm)) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
{ rewrite R, v_addi_lit. img_apply (proj2 (rdn_mbytes tfxsegs _ 4 _ _)). split; [img_refl|].
intros i Hi. rewrite (Hb (Z.of_nat i)) by img_lia. do 4 (destruct i as [|i]; [img_refl|]). img_lia. }
rewrite Hshape. eapply (SRr_step tfxsegs Hwx W); [img_refl | |].
- rewrite restrict_mkst_fx. img_apply (step_lw tfxsegs _ _ _ _ _ rd rs imm _ (Z_to_bv 64 0) Hfetch Hec Hdec Hrdn). img_case; vm_compute. all: img_refl.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
img_apply SRr_ret. split; [img_refl|]. eexists _, _. split; [img_refl|]. split; [|img_refl].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (img_try (img_apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; img_change (bv_modulus 64) with (2 ^ 64); rewrite Zplus_mod_idemp_l; img_refl)).
img_apply (st_ok_set_regs tfxsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SLit 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. img_refl.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [img_refl|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|img_try (constructor)]. cbn [fst snd]. split; [img_try (img_exact Hrd)|].
rewrite getr_same by (img_try (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate)). img_apply bv_eq. img_case; vm_compute. all: img_refl.
Qed.
Section q. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Lemma pc_scheck : forall (W : world tfxsegs) E ss ms md ly S (sp0 : Z) r0 rest k (x L : Z) (str : list byte),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_pc ss = A_ISL -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 12 = Z_to_bv 64 x ->
ss_mem ss = r0 :: rest -> YQ0b.r_base r0 = Some 2%nat -> YQ0b.r_lo r0 = - FP_WIN -> YQ0b.r_hi r0 = 0 ->
YQ0b.r_wlo r0 = - FP_WIN -> YQ0b.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit FP_SLCALL -> sr_get (ss_regs ss) 2 = SOff 2 OSP -> sr_get (ss_regs ss) 10 = SOff 12 0 -> sr_get (ss_regs ss) 22 = SOff 12 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (fp_after k ss)) = true ->
no_cdata (ss_mem (fp_after k ss)) = true ->
mem_atoms_lt k (ss_mem (fp_after k ss)) = true ->
forallb (chunk_inside r0) (YQ0b.r_chunks r0) = true ->
(forall r, In r rest -> YQ0b.r_base r = None /\ 0 <= YQ0b.r_lo r /\ YQ0b.r_hi r <= 2 ^ 43 /\ YQ0b.r_whi r <= YQ0b.r_wlo r) ->
AR tfxsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + FPI_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - FPI_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
vf_str W (ms_mem ms) x str -> L = Z.of_nat (length str) -> L + 1 < 2 ^ 32 -> 0 < x -> x + L + 1 <= 2 ^ 47 ->
amem_range x (L + 1) ->
range_addressable (aview tfxsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) (ms_mem ms)) x (L + 1) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 md2,
c' = mkCfg ms2 md2 /\
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms2)) CLOBP)) (fp_after k ss) (restrict (w_H W) ms2) /\
AR tfxsegs B ly S W (ms_mem ms2) md2 /\ same_but_materialized md md2 /\
(forall z : word, ~ (sp0 + OSP - 72 <= bv_unsigned z < sp0 + OSP) -> ms_mem ms2 z = ms_mem ms z) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k x L str HS Hpc Hrv Usp E12 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 S10 S22
Hat Hwf2 Hnc2 Hma2 Hci0 Hrest HAR Hsp44 Hsp16 Hstk Htop Hpres HSTR HL HL32 Hx0 Hxhi Hamx Hra_x Hhull_x.
pose proof YF8r.Hwx_tfa as Hwx. unfold FPI_STK in *. unfold OSP in *.
assert (HFPW : FP_WIN = 2432) by img_refl. assert (HISL : A_ISL = (411096 + D_2c4)) by img_refl. assert (HSLC : FP_SLCALL = (282496 + D_2c4)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hamr : x + L + 1 <= 2 ^ 47 - 1) by (img_try (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamx; img_lia)).
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *. set (H := w_H W) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 FP_SLCALL) by (img_try (rewrite (st_ok_restrict_reg tfxsegs H E _ _ 1 HS), S1; img_refl)).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 - 2352)) by (img_try (rewrite (st_ok_restrict_reg tfxsegs H E _ _ 2 HS), S2; cbn [sv_denot]; rewrite Usp; f_equal; img_lia)).
assert (R10 : getr regsT 10 = w64 x) by (img_try (rewrite (st_ok_restrict_reg tfxsegs H E _ _ 10 HS), S10; cbn [sv_denot]; rewrite E12, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (R22 : getr regsT 22 = w64 x) by (img_try (rewrite (st_ok_restrict_reg tfxsegs H E _ _ 22 HS), S22; cbn [sv_denot]; rewrite E12, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
destruct HSTR as (Hsb & Hs0 & Hnz).
assert (LEN : Z.of_nat (length str) = L) by img_lia.
assert (Hnul : ~ In NUL str).
{ intros Hin. apply In_nth with (d := NUL) in Hin as (j & Hj & Hnj). pose proof (proj1 (Forall_forall _ _) Hnz _ (nth_In str NUL Hj)) as Hb. img_apply Hb. rewrite Hnj. img_refl. }
assert (Hrd : forall j, (j <= length str)%nat -> rdn tfxsegs (mrestrict H memT) (Z_to_bv 64 (bv_unsigned (w64 x) + Z.of_nat j)) 1 = Some [nth j (str ++ [NUL]) NUL]).
{ intros j Hj. unfold w64. rewrite unsigned_lit_small by img_lia.
img_apply (proj2 (rdn_mbytes tfxsegs _ 1 _ _)). split; [img_refl|]. intros i Hi. replace i with 0%nat by img_lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
destruct (Nat.lt_ge_cases j (length str)) as [Hlt|Hge].
- rewrite app_nth1 by img_lia. rewrite (YF8r.aview_byte H memT _ (bv_unsigned (nth j str 0%bv))); [img_try (rewrite Z_to_bv_bv_unsigned; rewrite (nth_indep _ 0%bv NUL) by img_lia; img_refl)|]. img_exact (Hsb j Hlt).
- assert (Hj' : j = length str) by img_lia. (subst j; cbv beta). rewrite app_nth2 by img_lia. rewrite Nat.sub_diag. cbn [nth].
rewrite (YF8r.aview_byte H memT _ 0); [img_refl|]. img_exact Hs0. }
destruct (tfx_istrlen str (w64 x) (mrestrict H memT) (seg_rom tfxsegs) regsT R10 Hnul Hrd ltac:(img_try (unfold w64; rewrite unsigned_lit_small by img_lia; img_lia))) as (regs2 & Hms & A10 & KEEP).
rewrite R1 in Hms. replace (v_jalr (Z_to_bv 64 FP_SLCALL) 0) with (Z_to_bv 64 FP_SLCALL : word) in Hms by (img_try (img_apply bv_eq; (try img_inst; img_case; vm_compute); img_refl)).
rewrite Hshape. unfold memT in Hms |- *.
eapply (SRr_msteps tfxsegs Hwx W); [img_try (rewrite restrict_mkst_fx; img_exact Hms)|].
intros model' Hsbm _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H (ms_mem ms) (mrestrict H (ms_mem ms))).
assert (M2 : forall z, mem2 z = ms_mem ms z) by (img_try (intros z; (subst mem2; cbv beta); img_apply YE1h.munrestrict_mrestrict_same)).
assert (AV2 : forall a, aview tfxsegs H mem2 a = aview tfxsegs H (ms_mem ms) a) by (img_try (intros a; img_apply aview_same; img_apply M2)).
assert (K2 : forall (rr : bv 5), rr <> 10%bv -> rr <> 11%bv -> rr <> 12%bv -> getr regs2 rr = getr regsT rr) by (img_try (intros rr; img_apply KEEP)).
assert (R2sp : spZ regs2 = sp0 - 2352) by (img_try (unfold spZ; rewrite (K2 2%bv) by (intros H'; discriminate H'); rewrite R2; img_apply unsigned_lit_small; img_lia)).
assert (HAR2 : AR tfxsegs B ly S W mem2 model').
{ img_apply (al_frame _ _ LAWS ly S W (ms_mem ms) md mem2 _ HAR); [img_try (intros a _ _; img_apply AV2) | img_try (intros a Hv; rewrite AV2; img_exact Hv) | | | | img_try (img_exact (YE0v.hs_kept_eq _ _ _ M2))]; img_apply (same_but_materialized_frame md _ Hsbm). }
eapply SRr_bind.
{ img_apply (pfs_check_srr B LAWS TB ly S W regs2 mem2 model' x (L + 1) HAR2).
- rewrite R2sp. replace (sp0 - 2352) with (sp0 + (-147) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hsp16.
- rewrite R2sp. unfold YE1f.RC_SCR. img_lia.
- rewrite R2sp. img_lia.
- intros a Ha. rewrite R2sp in Ha. unfold YE1f.RC_SCR in Ha. img_apply (apresent_same H (ms_mem ms) mem2 a (M2 _)). img_apply Hpres. img_lia.
- rewrite A10, LEN. unfold w64. f_equal; img_lia.
- rewrite (K2 22%bv) by (img_try (intros H'; discriminate H')). img_exact R22.
- img_exact Hx0.
- img_lia.
- img_lia.
- img_lia.
- img_exact Hamx.
- eapply range_addressable_agree; [|img_try (img_exact Hra_x)]. intros z Hz. img_apply AV2.
- intros s' Hs. rewrite AV2. img_exact (Hhull_x s' Hs). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & _ & Hfr3 & Hpm3 & Hptw3).
rewrite R2sp in Hfr3, Hptw3. unfold YE1f.RC_SCR in Hfr3, Hptw3.
img_apply SRr_ret. split; [img_refl|]. exists (mkst regs3 (w64 YE1f.RC_END) mem3 (seg_rom tfxsegs)), md3.
split; [img_refl|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks] in *.
(subst b0 lo0 hi0 wlo0 whi0; cbv beta).
unfold fp_after in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|img_try (split; [img_exact HAR3 | split; [|split]])].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst]. img_change (w64 YE1f.RC_END) with (Z_to_bv 64 FP_CHKEND).
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfxsegs k E ss regsT regs3 (Z_to_bv 64 A_ISL) FP_CHKEND
(mrestrict H (ms_mem ms)) (mrestrict H mem3) rs [] CLOBP HS Hat) as SPL end.
cbn [map app fst] in SPL. img_apply SPL; clear SPL.
+ img_case; vm_compute. all: img_refl.
+ img_case; vm_compute. all: img_refl.
+ img_refl.
+ img_exact Hma2.
+ intros r Hr. destruct (not_clobp_cases r Hr) as [-> | [Hcs Hne]]; [img_try (rewrite !getr_zero; img_refl)|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (K3 (bv_unsigned r) Hcs Hne). rewrite Z_to_bv_bv_unsigned.
img_apply K2; intros ->; clear -Hcs Hne; unfold acallee_saved in Hcs;
match type of Hne with bv_unsigned ?x <> _ => let v := img_ev (bv_unsigned x) in img_change (bv_unsigned x) with v in * end; img_lia.
+ constructor.
+ split; [img_try (img_exact Hwf2)|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val] in *. rewrite Usp in *.
split; [img_try (img_exact Hlo)|]. split; [img_try (img_exact Hhi)|]. split.
{ intros off Ho. img_apply YE0v.apresent_writable. img_apply Hpm3. img_apply (apresent_same H (ms_mem ms) mem2 _ (M2 _)). img_apply Hpres. img_lia. }
img_apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk1]. apply Z.leb_le in Hk1. unfold OSP in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YQ0b.r_lo YQ0b.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [img_try (img_exact Hb1)|].
rewrite <- Hb2. img_apply mbyte_of_aview. rewrite Hfr3; [img_try (img_apply AV2) | img_lia | img_lia].
-- img_apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
destruct (Hrest r Hr) as (Hrb & Hrl & Hrh & Hrw).
eapply (region_ok_transport tfxsegs E E); [img_try (img_exact Hokr) | img_refl | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YQ0b.c_val c); [img_refl | img_try (img_exact I) | img_try (img_exact I) | img_try (discriminate)].
++ intros a Ha. img_apply mbyte_of_aview. rewrite Hrb in Ha. cbn [base_val] in Ha. rewrite Hfr3; [img_try (img_apply AV2) | img_lia | img_lia].
++ intros a Ha _. exfalso. img_lia.
++ apply regions_wf_In with (r := r) in HwfT; [|img_try (right; img_exact Hr)]. apply region_wf_facts in HwfT as (_ & _ & Hci). img_exact Hci.
* eapply pairwise_disjoint_extents; [|img_try (img_exact HpdT)]. img_refl.
- eapply same_but_materialized_trans; [img_try (img_exact Hsbm) | img_try (img_exact Hsbm3)].
- intros z Hz. cbn [ms_mem mkst]. rewrite Hptw3 by img_exact Hz. img_apply M2.
- intros a Hp. cbn [ms_mem mkst]. img_apply Hpm3. img_apply (apresent_same H (ms_mem ms) mem2 a (M2 _)). img_exact Hp.
Qed.
End q.
Definition epi_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 56 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 48 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 40 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition ss_epi {imgk : img} : sstate := mkSS FP_RET sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 112 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition SAVEDA : list (Z * Z) := [(1, -56); (8, -64); (9, -72); (18, -80); (12, -48)].
Definition KEPTA : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? FP_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - FP_WIN) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SLit FMT) && reg_is ss 12 (SOff 2 (-48)) &&
reg_is ss 1 (SLit FP_RET) && reg_is ss 2 (SOff 2 (-112)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok {imgk : img} : shapeA eA = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma chunk_is_sound {imgk : img} : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.
Lemma br_memset_align : forall E sp0, bv_unsigned (ew E 2) = sp0 -> sp0 mod 16 = 0 -> 2 ^ 44 <= sp0 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2328))) (SLit 15))) (sv_denot E (SLit 0)) = false.
Proof.
intros E sp0 H2 Hal Hsp. rewrite branch_eq_U, !U_SAlu, !U_SLit, U_SOff, H2. cbn [zalu_raw].
rewrite (zcanon_small 40), (zcanon_small 15), (zcanon_small 0), (zcanon_small (sp0 + -2328)) by img_lia.
assert (Hm : (sp0 + -2328) mod 16 = 8).
{ replace (sp0 + -2328) with (sp0 - 146 * 16 + 8) by img_lia. rewrite <- Z.add_mod_idemp_l by img_lia.
replace ((sp0 - 146 * 16) mod 16) with 0; [img_refl|]. rewrite <- Zminus_mod_idemp_l. rewrite Hal. img_refl. }
assert (Hand : Z.land (Z.lor 40 (sp0 + -2328)) 15 = 8).
{ rewrite Z.land_lor_distr_l. img_change 15 with (Z.ones 4). rewrite !Z.land_ones by img_lia. img_change (2 ^ 4) with 16. rewrite Hm. img_refl. }
assert (Hlt : Z.lor 40 (sp0 + -2328) < 2 ^ 64).
{ destruct (Z.eq_dec (Z.lor 40 (sp0 + -2328)) 0) as [E0|E0]; [img_try (rewrite E0; img_lia)|].
img_apply Z.log2_lt_pow2; [img_try (pose proof (Z.lor_nonneg 40 (sp0 + -2328)); img_lia)|]. rewrite Z.log2_lor by img_lia.
img_apply Z.max_lub_lt; [img_try ((img_case; cbv); img_refl) | img_try (img_apply Z.log2_lt_pow2; img_lia)]. }
rewrite (zcanon_small (Z.lor 40 (sp0 + -2328))) by (img_try (pose proof (Z.lor_nonneg 40 (sp0 + -2328)); img_lia)).
rewrite Hand. img_refl.
Qed.
Section t. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Hypothesis TL : TfxSyms B.
Lemma ocpy_of_icpt : aintrin_realizes tfxsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. rewrite (ts_code B TB). img_exact (memcpy_icpt_realizes B LAWS TB). Qed.
Lemma astrnlen_of_icpt : astrnlen_realizesM B (pc_wrap_strnlen (as_code B)).
Proof. rewrite (ts_code B TB). img_exact (strnlen_icpt_contractM B LAWS TB TL). Qed.
Theorem tfx_fprintf_icpt_open : forall ly S (W : world tfxsegs) regs mem md ch s (str : list byte) L cval T,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + FPI_STK <= spZ regs ->
(forall a, spZ regs - FPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_open -> getr regs 12 = w64 s ->
L = Z.of_nat (length str) -> L <= 33554415 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - FPI_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfxsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfxsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview tfxsegs (w_H W) mem) FMT_open 21 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfxsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfxsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 18) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FPI_STK <= a < spZ regs) -> ~ vf_file a -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfxsegs (w_H W) (w_A W) md' ->
srealizes tfxsegs (cfg_at tfxsegs (raZ regs) regs' mem' md') T) ->
srealizes tfxsegs (cfg_at tfxsegs FP_ENTRY regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_open1 ++ str ++ map (Z_to_bv 8) lit_open2)) T).
Proof.
intros ly S W regs mem md ch s str L cval T HPRE Hstk Hpres G10 G11 G12 HL HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s
HFP HFown Hgot Hcan Hcv Hro HZ Hch HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold FPI_STK in *.
assert (HFS : FILE_SZ = 232) by img_refl. assert (HFF : F_STDERR = (681808 + D_10f0)) by img_refl.
assert (HGC : A_GOT_canary = (0xa2e10 + D_10f0)) by img_refl. assert (HCA : A_canary = (0x5fd190 + D_10c0)) by img_refl.
assert (HVFS : VF_STK = 9104) by img_refl. assert (KHI : kHighMemEnd = 2 ^ 47) by img_refl.
assert (HFMT : FMT_open = FMT) by img_refl. assert (HFMTV : FMT = (120781 + D_m9)) by img_refl.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try ((subst sp0; cbv beta); img_lia)).
pose proof YF8r.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfxsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfxsegs H m' b = aview tfxsegs H m b) -> val_mem tfxsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf. img_apply (YF8r.val_mem_ext (mrestrict H m)); [|img_try (img_exact Hv)]. intros j Hj. img_apply mbyte_of_aview. img_apply Hf. img_lia. }
assert (FT : forall flds (m m' : word -> option byte),
Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) flds ->
file_is flds (mrestrict H m) ->
(forall b, F_STDERR <= b < F_STDERR + FILE_SZ -> aview tfxsegs H m' b = aview tfxsegs H m b) -> file_is flds (mrestrict H m')).
{ intros flds m m' Hwf Hf Hb. unfold file_is in *. img_apply Forall_forall. intros [[o nn] v] Hin.
pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. pose proof (proj1 (Forall_forall _ _) Hwf _ Hin) as Ho. cbn beta iota in Hv, Ho |- *.
img_apply (VT m); [img_try (img_exact Hv)|]. intros b Hbb. img_apply Hb. pose proof (N_nat_Z nn). img_lia. }
assert (WF1 : Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) stderr_fields) by (img_try (unfold stderr_fields, FILE_SZ; repeat constructor; cbn; img_lia)).
unfold cfg_at. img_change (w64 FP_ENTRY) with (Z_to_bv 64 FP_ENTRY).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (EE10 : ew EE 10 = Z_to_bv 64 F_STDERR) by (img_try (rewrite (EEreg 10%nat 10%bv eq_refl); img_exact G10)).
assert (EE12 : ew EE 12 = Z_to_bv 64 s) by (img_try (rewrite (EEreg 12%nat 12%bv eq_refl); img_exact G12)).
assert (HZ' : forall sa, SH_LO <= sa < SH_HI -> aview tfxsegs H mem sa = Some 0).
{ intros sa Hsa. img_apply HZ. unfold SH_LO, SH_HI in Hsa.
match goal with |- ?a <= sa < ?b => let a' := img_ev constr:(a) in img_change a with a'; let b' := img_ev constr:(b) in img_change b with b' end. img_lia. }
assert (HS0 : st_ok tfxsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 FP_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
img_apply (st_ok_regs tfxsegs EE (mkSS FP_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (YE0v.Env_reg regs _ 11 11%bv eq_refl), G11; img_refl) ] |]).
destruct Hr. }
unfold memA, EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [| img_try (img_apply Forall_cons; [| img_apply Forall_cons; [img_apply Hro | img_exact (rodata_ok B TB fpA_rodata ly S H mem EE (fpA_rodata_chk ly) (proj1 HAR))]])].
+ unfold stkA, FP_WIN. img_apply (region_ok_stack tfxsegs EE _ 2 sp0 (- 2432)); [img_try (img_exact EE2) | img_lia | img_lia |].
intros a Ha. img_apply YE0v.apresent_writable. img_apply HpresE. (subst sp0; cbv beta). img_lia.
+ unfold shz, region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
unfold SH_LO, SH_HI. split; [img_lia|]. split; [img_try (unfold kHighMemBeg in *; img_lia)|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
img_apply chunk_ok_zero. intros i Hi. rewrite (YF8r.aview_byte H mem _ 0); [img_refl|]. img_apply HZ'. unfold SH_LO, SH_HI. cbn in Hi. img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkA, shz, img_ro_region, fpA_rodata, icpt_rodata, ro_region, extent_of_region, FP_WIN, SH_LO, SH_HI, IMG_RO_LO, IMG_RO_HI.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE12, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; first [img_exact Hal16 | img_apply Z.mod_1_r | (subst sp0; cbv beta); img_lia | img_lia]. }
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HS0 r_A1) HAI0).
intros Wa ca _ HAIa (-> & msa & mata & -> & HSa & HFa & HFra). cbn [cfg_model] in HAIa. rewrite ?wvb_wvb in HAIa |- *.
assert (MEQa : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msa z = mem z).
{ intros z Hz. img_apply (HFa z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold FP_WIN in *. img_lia. }
clear HFa HFra.
pose proof (st_ok_add_cond_neg tfxsegs EE _ _ BC_EQ (RG eA1 13) (SLit 0) HSa (br_memset_align EE sp0 EE2 Hal16 ltac:(img_lia))) as HSa'.
img_change (neg_bc BC_EQ) with BC_NE in HSa'. clear HSa.
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSa' r_A2) HAIa).
intros Wb cb _ HAIb (-> & msb & matb & -> & HSb & HFb & HFrb). cbn [cfg_model] in HAIb. rewrite ?wvb_wvb in HAIb |- *.
assert (MEQb : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msb z = mem z).
{ intros z Hz. rewrite (HFb z); [img_try (img_apply MEQa; img_exact Hz)|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold FP_WIN in *. img_lia. }
clear HFb HFrb.
pose proof lw_bytes_ok as (LWB & LWpc & LWs8 & LWbase).
assert (Hb4 : forall kk, 0 <= kk < 4 -> mbyte tfxsegs (mrestrict H (ms_mem msb)) (sp0 - 2296 + (-28) + kk) = Some (Z_to_bv 8 0)).
{ intros kk Hkk. pose proof (st_ok_mem_ok tfxsegs EE eA2 _ HSb) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite memA2_eq in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
rewrite forallb_forall in LWB.
assert (Hin4 : forall j, In j [0; 1; 2; 3] -> exists c, In c (YQ0b.r_chunks rA2) /\ c = YQ0b.mkChunk (-2324 + j) (CVal 1 (SLit 0))).
{ intros j Hj. specialize (LWB j Hj). apply existsb_exists in LWB as (c & Hc1 & Hc2). exists c. split; [img_try (img_exact Hc1)|].
unfold chunk1_is in Hc2. destruct c as [o cv]. cbn [YQ0b.c_off YQ0b.c_val] in Hc2. apply andb_prop in Hc2 as [Ho Hv]. apply Z.eqb_eq in Ho.
destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He]. apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl. }
assert (Hkk' : In kk [0; 1; 2; 3]) by (img_try (cbn; img_lia)).
destruct (Hin4 kk Hkk') as (c & Hc & ->).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite LWbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
pose proof (val_of_chunk_ok tfxsegs EE _ _ (-2324 + kk) 1 (SLit 0) 0 Hck eq_refl ltac:(img_try (cbn; img_lia)) ltac:(img_try (cbn; img_lia))) as Hv.
pose proof (Hv 0%nat ltac:(img_lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
replace (sp0 - 2296 + -28 + kk) with (sp0 + (-2324 + kk)) by img_lia. etransitivity; [img_try (img_exact Hv0) | img_refl]. }
assert (Hat2 : ss_atoms_lt 32 eA2 = true) by (img_try ((try img_inst; img_case; vm_compute); img_refl)).
pose proof lw_fetch as [LWlk LWdec]. rewrite <- LWpc in LWlk.
assert (LWrs : sv_denot EE (sr_get (ss_regs eA2) 24%bv) = Z_to_bv 64 (sp0 - 2296)).
{ unfold reg_is, RG in LWs8. apply sv_eqb_eq in LWs8. replace (Z_to_bv 5 24) with (24%bv : bv 5) in LWs8 by (img_try (img_apply bv_eq; img_refl)).
rewrite LWs8. cbn [sv_denot]. rewrite EE2. img_refl. }
pose proof (fp_lw_zero W EE eA2 msb (with_vm_backing (m_vm_lazy md) matb md) 11%bv 24%bv (4068%bv : bv 12) W_LW (sp0 - 2296) 32
HSb eq_refl Hat2 LWlk LWdec eq_refl LWrs
ltac:(img_try (img_change (bv_signed (4068%bv : bv 12)) with (-28); img_lia))
ltac:(img_try (img_change (bv_signed (4068%bv : bv 12)) with (-28); img_lia))
ltac:(img_lia)
ltac:(img_try (img_change (bv_signed (4068%bv : bv 12)) with (-28); img_exact Hb4))) as STEP.
eapply (SRr_srealizes tfxsegs W _ _ _ STEP HAIb). clear STEP.
intros Wc cc _ HAIc (-> & msc & matc & -> & HSc & HMc). cbn [cfg_model] in HAIc. rewrite ?wvb_wvb in HAIc |- *.
rewrite LWpc in HSc. img_change (set_regs_pc eA2 [(11%bv, SLit 0)] (FP_LW + 4)) with eA2' in HSc.
assert (MEQc : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msc z = mem z) by (img_try (intros z Hz; rewrite HMc; img_apply MEQb; img_exact Hz)).
clear HMc.
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W EE A_ISL _ _ _ _ _ HSc r_A3) HAIc).
intros Wd cd _ HAId (-> & msd & matd & -> & HSd & HFd & HFrd). cbn [cfg_model] in HAId. rewrite ?wvb_wvb in HAId |- *.
assert (MEQd : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msd z = mem z).
{ intros z Hz. rewrite (HFd z); [img_try (img_apply MEQc; img_exact Hz)|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold FP_WIN in *. img_lia. }
clear HFd HFrd.
assert (AVd : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2432 <= a < sp0) -> aview tfxsegs H (ms_mem msd) a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQd. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
pose proof shapeS_ok as SSH. unfold shapeS in SSH. rewrite memA3_eq in SSH.
apply andb_prop in SSH as [SSH S22]. apply andb_prop in SSH as [SSH S10]. apply andb_prop in SSH as [SSH S2]. apply andb_prop in SSH as [SSH S1]. apply andb_prop in SSH as [Spc Smemd].
pose proof memA3_eq as Hmemd.
apply andb_prop in Smemd as [Smemd Swhi]. apply andb_prop in Smemd as [Smemd Swlo]. apply andb_prop in Smemd as [Smemd Shi]. apply andb_prop in Smemd as [Sbase Slo].
apply obase_eqb_eq in Sbase. apply Z.eqb_eq in Slo. apply Z.eqb_eq in Shi. apply Z.eqb_eq in Swlo. apply Z.eqb_eq in Swhi. apply Z.eqb_eq in Spc.
unfold reg_is, RG in S1, S2, S10, S22. apply sv_eqb_eq in S1. apply sv_eqb_eq in S2. apply sv_eqb_eq in S10. apply sv_eqb_eq in S22.
replace (Z_to_bv 5 1) with (1%bv : bv 5) in S1 by (img_try (img_apply bv_eq; img_refl)). replace (Z_to_bv 5 2) with (2%bv : bv 5) in S2 by (img_try (img_apply bv_eq; img_refl)).
replace (Z_to_bv 5 10) with (10%bv : bv 5) in S10 by (img_try (img_apply bv_eq; img_refl)). replace (Z_to_bv 5 22) with (22%bv : bv 5) in S22 by (img_try (img_apply bv_eq; img_refl)).
assert (PRSd : forall a, sp0 - 2432 <= a < sp0 -> apresent H (ms_mem msd) a).
{ intros a Ha. img_apply (st_ok_window_apresent H EE eA3 msd 0 rA3 a HSd ltac:(img_try (rewrite Hmemd; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Sbase, Swlo, Swhi. cbn [base_val]. rewrite EE2. unfold FP_WIN. img_lia. }
assert (PMd : forall a, apresent H mem a -> apresent H (ms_mem msd) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (YE0v.apresent_mod _ (ms_mem msd) a). rewrite (YE0v.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [img_try (img_apply (apresent_same H mem (ms_mem msd) a'); [img_apply MEQd; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hp])|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PRSd; img_lia)|].
img_apply (apresent_same H mem (ms_mem msd) a'); [img_try (img_apply MEQd; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hp)]. }
assert (HARd : AR tfxsegs B ly S W (ms_mem msd) (with_vm_backing (m_vm_lazy md) matd md)).
{ img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem msd) _ HAR).
+ intros a Hr Hown. img_apply AVd; [img_try (img_exact Hr)|]. intros Hs'. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ (ms_mem msd) a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [img_try (rewrite AVd by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AVd by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. img_apply PRSd. img_lia.
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md matd)).
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md matd)).
+ img_apply (same_but_materialized_frame md _ (with_vm_backing_same md matd)).
+ img_exact (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQd HpresE ltac:(img_try (unfold sp0 in *; img_lia)) ltac:(img_lia)). }
eapply (SRr_srealizes tfxsegs W (mkCfg msd (with_vm_backing (m_vm_lazy md) matd md)) _ _); [ | img_try (img_exact HAId) | ].
{ img_apply (pc_scheck B LAWS TB W EE eA3 msd (with_vm_backing (m_vm_lazy md) matd md) ly S sp0 rA3 restA3 32 s L str HSd Spc eq_refl EE2 EE12 Hmemd Sbase Slo Shi Swlo Swhi S1 S2 S10 S22).
- img_case; vm_compute. all: img_refl.
- rewrite eA3r_eq. img_case; vm_compute. all: img_refl.
- rewrite eA3r_eq. img_case; vm_compute. all: img_refl.
- rewrite eA3r_eq. img_case; vm_compute. all: img_refl.
- img_case; vm_compute. all: img_refl.
- img_exact (rest_okb_sound restA3 restA3_ok).
- img_exact HARd.
- img_lia.
- img_exact Hal16.
- unfold FPI_STK. img_lia.
- img_lia.
- intros a Ha. unfold FPI_STK in Ha. img_apply PMd. img_apply Hpres. img_lia.
- img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. img_apply AVd; [img_lia | img_try (unfold sp0 in *; img_lia)].
- img_exact HL.
- img_lia.
- img_lia.
- img_lia.
- img_exact Hams.
- eapply range_addressable_agree; [|img_try (img_exact Hra_s)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. img_apply AVd; unfold sp0 in *; img_lia.
- intros s' Hs'. rewrite AVd; [img_try (img_exact (Hhull_s s' Hs')) | |];
pose proof (shadow_addr_bounds s ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (s + (L + 1) - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr s) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr s) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (s + (L + 1) - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (s + (L + 1) - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia. }
intros We ce _ HAIe (-> & mse & mde & -> & HSe0 & HARe & Hsbme & Hfre & Hpme). cbn [cfg_model] in HAIe. unfold OSP in Hfre.
rewrite eA3r_eq in HSe0.
assert (MEQe : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem mse z = mem z) by (img_try (intros z Hz; rewrite Hfre by img_lia; img_apply MEQd; img_exact Hz)).
set (E1 := havoc EE 32 (map (getr (ms_regs mse)) CLOBP)) in HSe0.
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs r).
{ intros i r Hi. (subst E1; cbv beta). rewrite ew_havoc_old by (img_try (pose proof (u5_range r); img_lia)). img_apply EEreg. img_exact Hi. }
assert (E1_2 : bv_unsigned (ew E1 2) = sp0) by (img_try (rewrite (E1reg 2%nat 2%bv eq_refl); img_refl)).
assert (E1_10 : ew E1 10 = Z_to_bv 64 F_STDERR) by (img_try (rewrite (E1reg 10%nat 10%bv eq_refl); img_exact G10)).
assert (E1_12 : ew E1 12 = Z_to_bv 64 s) by (img_try (rewrite (E1reg 12%nat 12%bv eq_refl); img_exact G12)).
eapply (SRr_srealizes tfxsegs W _ _ _ (fp_phase_to W E1 FP_REAL _ _ _ _ _ HSe0 r_A4) HAIe).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [img_try (img_apply MEQe; img_exact Hz)|]. intros Hin.
unshelve epose proof (in_wrange_single_b E1 _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ E1_2 Hin) as X0; [img_try ((try img_inst; img_case; vm_compute); img_refl)|]. unfold FP_WIN in *. img_lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E1 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H E1 eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| img_try (rewrite <- Hi; img_exact HK')]. cbn [sv_denot]. rewrite (E1reg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfxsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (img_try (do 5 (destruct j as [|j]; [img_try (cbn in Hj; injection Hj as <- <-; img_lia)|]); destruct j; discriminate)).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. (subst c; cbv beta).
pose proof (st_ok_mem_ok tfxsegs E1 eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E1_2 in Hck.
img_apply (val_of_chunk_ok tfxsegs E1 _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (E1reg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [img_refl|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. img_change (bv_modulus 5) with 32. rewrite Z.mod_small by img_lia. img_lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). img_zside.
- img_zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 F_STDERR) by (img_try (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite E1_10, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q11 : getr regs1 11 = w64 FMT_open) by (img_try (rewrite (RD 11%bv (SLit FMT) R11); img_refl)).
assert (Q12 : getr regs1 12 = w64 (sp0 - 48)) by (img_try (rewrite (RD 12%bv (SOff 2 (-48)) R12); cbn [sv_denot]; rewrite E1_2; img_refl)).
assert (Q1 : getr regs1 1 = w64 FP_RET) by (img_try (rewrite (RD 1%bv (SLit FP_RET) R1); img_refl)).
assert (Q2 : getr regs1 2 = w64 (sp0 - 112)) by (img_try (rewrite (RD 2%bv (SOff 2 (-112)) R2); cbn [sv_denot]; rewrite E1_2; img_refl)).
assert (Q3 : getr regs1 3 = getr regs 3) by (img_try (img_exact (RK 3%bv 3%nat eq_refl ltac:(cbn; img_lia)))).
assert (Q4 : getr regs1 4 = getr regs 4) by (img_try (img_exact (RK 4%bv 4%nat eq_refl ltac:(cbn; img_lia)))).
assert (R1sp : spZ regs1 = sp0 - 112) by (img_try (unfold spZ; rewrite Q2; unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (R1ra : raZ regs1 = FP_RET) by (img_try (unfold raZ; rewrite Q1; unfold w64; img_apply unsigned_lit_small; unfold FP_RET; img_lia)).
pose proof (st_ok_restrict_mkst tfxsegs H E1 _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy mde) mat1 mde) in *.
assert (MF1 : same_but_materialized md md1).
{ (subst md1; cbv beta). eapply same_but_materialized_trans; [img_try (img_apply (with_vm_backing_same md matd))|].
eapply same_but_materialized_trans; [img_try (img_exact Hsbme) | img_try (img_apply with_vm_backing_same)]. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2432 <= a < sp0) -> aview tfxsegs H (ms_mem ms1) a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PRS1 : forall a, sp0 - 2432 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. img_apply (st_ok_window_apresent H E1 eA ms1 0 r0 a HS1 ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E1_2. unfold FP_WIN. img_lia. }
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
{ split; [img_try (img_exact HAR1)|]. split; [img_try (rewrite Q1; img_apply (ret_ok_lit FP_RET); [unfold FP_RET; img_lia | img_refl])|].
split; [img_try (rewrite R1sp; replace (sp0 - 112) with (sp0 + (-7) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16)|].
split; [img_try (rewrite R1sp; unfold ESTACK; unfold sp0 in *; img_lia)|]. split; [img_try (rewrite R1sp; unfold sp0 in *; img_lia)|].
split; [img_try (intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; img_apply PM1; img_apply Hpres; unfold sp0 in *; img_lia)|].
split; [img_try (rewrite Q3; img_exact Hgp) | img_try (rewrite Q4; img_exact Htp)]. }
img_change (mkCfg (mkst regs1 (Z_to_bv 64 FP_REAL) (ms_mem ms1) (seg_rom tfxsegs)) md1) with (cfg_at tfxsegs A_vfprintf regs1 (ms_mem ms1) md1).
img_apply (tfx_vfprintf_open B TL LAWS ocpy_of_icpt astrnlen_of_icpt ly S W regs1 (ms_mem ms1) md1 ch (sp0 - 48) s str L cval T HPRE1).
- rewrite R1sp. img_lia.
- rewrite R1sp, HVFS. unfold sp0 in *. img_lia.
- intros a Ha. unfold vf_band in Ha. rewrite R1sp, HVFS in Ha. img_apply PM1. img_apply Hpres. unfold sp0 in *. img_lia.
- img_exact Q10.
- img_exact Q11.
- img_exact Q12.
- rewrite R1sp. img_lia.
- img_lia.
- pose proof (Z.div_mod sp0 16 ltac:(img_lia)) as Hdm. rewrite Hal16, Z.add_0_r in Hdm.
replace (sp0 - 48) with ((2 * (sp0 / 16) - 6) * 8) by img_lia. img_apply Z_mod_mult.
- replace (sp0 - 48) with (sp0 + -48) by img_lia. replace s with (bv_unsigned (getr regs 12)) by (img_try (rewrite G12; unfold w64; rewrite unsigned_lit_small by img_lia; img_refl)).
img_exact (CK 4%nat 12%Z (-48)%Z eq_refl).
- img_exact HL.
- img_exact HLhi.
- img_exact Hs1.
- img_exact Hshi.
- rewrite R1sp, HVFS. unfold sp0 in *. img_lia.
- img_exact Hsfile.
- img_exact Hams.
- (img_apply (vf_tail_xfer W mem _ sp0); [img_try (img_exact Hstail) | img_try (intros a Hr Hb Hf; img_apply AV1; [img_exact Hr | unfold vf_band, VF_STK, ESTACK in Hb; unfold sp0 in *; img_lia]) | img_lia]) || (intros a Ha; rewrite AV1; [img_try (img_exact (Hstail a Ha)) | img_try (pose proof (Z.mod_pos_bound (s + L) 8 ltac:(img_lia)); img_lia) | img_try (pose proof (Z.mod_pos_bound (s + L) 8 ltac:(img_lia)); unfold sp0 in *; img_lia)]).
- intros a Hin. pose proof mc_bounds as [MB1 MB2]. rewrite AV1; [img_try (img_exact (Hromv a Hin)) | img_lia | img_lia].
- img_apply (vf_str_xfer W mem); [img_try (img_exact HSTR)|]. intros a Ha. img_apply AV1; [img_lia | img_try (unfold sp0 in *; img_lia)].
- eapply range_addressable_agree; [|img_try (img_exact Hra_s)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. img_apply AV1; unfold sp0 in *; img_lia.
- intros s' Hs'. rewrite AV1; [img_try (img_exact (Hhull_s s' Hs')) | |];
pose proof (shadow_addr_bounds s ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (s + (L + 1) - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr s) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr s) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (s + (L + 1) - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (s + (L + 1) - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia.
- img_apply (FT stderr_fields mem); [img_try (img_exact WF1) | img_try (img_exact HFP) | img_try (intros b Hb; img_apply AV1; img_lia)].
- img_exact HFown.
- img_apply (VT mem); [img_try (img_exact Hgot) | img_try (intros b Hb; img_apply AV1; img_lia)].
- img_apply (VT mem); [img_try (img_exact Hcan) | img_try (intros b Hb; img_apply AV1; img_lia)].
- img_exact Hcv.
- img_apply (ro_img_kept _ mem (ms_mem ms1)); [img_try (intros x Hx; img_apply MEQ1; unfold IMG_RO_LO, IMG_RO_HI in Hx; img_lia) | img_try (img_exact Hro)].
- intros a Ha. exists 0. split; [|img_try (left; img_refl)]. img_change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). rewrite AV1.
+ img_apply HZ. pose proof (Z.div_mod (shadow_addr a) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(img_lia)).
assert (shadow_addr FMT_open / 8 <= shadow_addr a / 8) by (img_try (img_apply Z.div_le_mono; [img_lia|]; unfold shadow_addr; img_apply Z.add_le_mono_l; img_apply Z.div_le_mono; img_lia)).
assert (shadow_addr a / 8 <= shadow_addr (FMT_open + 21 - 1) / 8) by (img_try (img_apply Z.div_le_mono; [img_lia|]; unfold shadow_addr; img_apply Z.add_le_mono_l; img_apply Z.div_le_mono; img_lia)).
img_lia.
+ pose proof (shadow_addr_bounds a ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. img_lia.
+ pose proof (shadow_addr_bounds a ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. unfold sp0 in *. img_lia.
- intros sa Hsa. rewrite AV1; [img_try (rewrite (HZ sa); [discriminate|]) | |].
+ pose proof (Z.div_le_mono (shadow_addr (FMT_open + 20 - 1)) (shadow_addr (FMT_open + 21 - 1)) 8 ltac:(img_lia) ltac:(img_try (unfold shadow_addr; img_apply Z.add_le_mono_l; img_apply Z.div_le_mono; img_lia))). img_lia.
+ match type of Hsa with ?a <= sa < ?b => let a' := img_ev constr:(a) in let b' := img_ev constr:(b) in img_change (a <= sa < b) with (a' <= sa < b') in Hsa end. img_lia.
+ match type of Hsa with ?a <= sa < ?b => let a' := img_ev constr:(a) in let b' := img_ev constr:(b) in img_change (a <= sa < b) with (a' <= sa < b') in Hsa end. unfold sp0 in *. img_lia.
- eapply fdchan_sbm; [img_try (img_exact Hch) | img_try (img_exact MF1)].
- img_exact HAI1.
-
intros regs2 mem2 md2 HAR2 AP2 Hsbm2 A10_2 HFW2 Hfr2 Hpm2 HAI2.
rewrite R1ra. unfold vf_band in Hfr2. rewrite R1sp, HVFS in Hfr2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr) by (img_try (intros rr z -> Hcs; img_exact (AP2 z Hcs))).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - 9104 <= a < sp0 - 112) -> ~ vf_file a -> aview tfxsegs H mem2 a = aview tfxsegs H (ms_mem ms1) a)
by (img_try (intros a Hr Ha Hf; img_exact (Hfr2 a Hr Ha Hf))).
unfold cfg_at. img_change (w64 FP_RET) with (Z_to_bv 64 FP_RET).
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
assert (R4sp : getr regs2 2 = w64 (sp0 - 112)) by (img_try (rewrite (K2 2%bv 2 ltac:(img_apply bv_eq; img_refl)) by (unfold acallee_saved; img_lia); img_exact Q2)).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 112).
{ (subst E4; cbv beta). rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R4sp. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (WS : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> -80 <= off -> val_mem tfxsegs (mrestrict H mem2) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj Hoff80. assert (Hoff : off <= -48) by (img_try (do 5 (destruct j as [|j]; [img_try (cbn in Hj; injection Hj as <- <-; img_lia)|]); destruct j; discriminate)).
img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK j rz off Hj)) | img_try (intros b Hb; img_apply AV2; [unfold sp0 in *; img_lia | unfold sp0 in *; img_lia | unfold vf_file; img_lia])]. }
pose proof (WS 0%nat 1%Z (-56)%Z eq_refl ltac:(img_lia)) as W0. replace (sp0 + -56) with (sp0 - 56) in W0 by img_lia.
pose proof (WS 1%nat 8%Z (-64)%Z eq_refl ltac:(img_lia)) as W1. replace (sp0 + -64) with (sp0 - 64) in W1 by img_lia.
pose proof (WS 2%nat 9%Z (-72)%Z eq_refl ltac:(img_lia)) as W2. replace (sp0 + -72) with (sp0 - 72) in W2 by img_lia.
pose proof (WS 3%nat 18%Z (-80)%Z eq_refl ltac:(img_lia)) as W3. replace (sp0 + -80) with (sp0 - 80) in W3 by img_lia.
assert (HSe : st_ok tfxsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 FP_RET) mem2 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18]) with E4.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 112) by (img_try (symmetry; img_exact E4_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18] (Z_to_bv 64 0) = getr regs r ->
off = 56 - 8 * Z.of_nat j -> Z.of_nat j < 4 ->
val_mem tfxsegs (mrestrict H mem2) (sp0 - 56 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem2) (sp0 - 112) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 112) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. (subst E4; cbv beta). rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs r)). img_zside.
- img_zside.
- (subst off; cbv beta). replace (sp0 - 112 + (56 - 8 * Z.of_nat j)) with (sp0 - 56 - 8 * Z.of_nat j) by img_lia. img_exact Hv. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK4 0%nat 1%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 56 - 8 * Z.of_nat 0) with (sp0 - 56) by img_lia; img_exact W0)].
+ img_apply (CK4 1%nat 8%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 56 - 8 * Z.of_nat 1) with (sp0 - 64) by img_lia; img_exact W1)].
+ img_apply (CK4 2%nat 9%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 56 - 8 * Z.of_nat 2) with (sp0 - 72) by img_lia; img_exact W2)].
+ img_apply (CK4 3%nat 18%bv); [img_refl | img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 56 - 8 * Z.of_nat 3) with (sp0 - 80) by img_lia; img_exact W3)].
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
img_change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try img_lia.
all: replace (spZ regs - 112) with (spZ regs + (-7) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
eapply (SRr_srealizes tfxsegs W _ _ T (fp_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI2).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem2 z) by (img_try (intros z; img_apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
eapply (SRr_srealizes tfxsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfxsegs))
(with_vm_backing (m_vm_lazy md2) mat' md2)) T); [ | img_try (img_exact HAI5) | ].
{ eapply (SRr_ret_at tfxsegs tbl_fp tbl_fp_ok Hwx W E4); [img_try (img_exact HS5) | img_refl | img_try ((try img_inst; img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb. split; [img_refl|]. exists mat'. img_refl. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (10%bv : bv 5) P10. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19.
rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21. rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23.
rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25. rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (img_try (intros jj rr Hnth; (subst E4; cbv beta); rewrite (ew_Ereg_extra regs2 _ jj); img_exact Hnth)).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (img_try (intros ii rr Hnth; (subst E4; cbv beta); img_exact (ew_Ereg_nat regs2 _ ii rr Hnth))).
assert (X32 : ew E4 32 = getr regs 1) by (img_try ((subst E4; cbv beta); img_exact (ew_Ereg_extra regs2 _ 0))). rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra')).
assert (SBM56 : same_but_materialized (with_vm_backing (m_vm_lazy md2) mat5 md2) (with_vm_backing (m_vm_lazy md2) mat6 md2))
by (img_try (rewrite <- (wvb_collapse (m_vm_lazy md2) mat6 mat5 md2); img_apply with_vm_backing_same)).
pose proof (same_but_materialized_frame _ _ SBM56) as MF.
assert (AV5 : forall a, aview tfxsegs H (ms_mem ms5) a = aview tfxsegs H mem2 a) by (img_try (intros a; img_apply aview_same; img_apply MEQ5)).
assert (GG : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr).
{ intros z rr Hrr H1. (subst rr; cbv beta). img_exact (K2 _ z eq_refl H1). }
img_apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat6 md2)).
+ img_apply (al_frame _ _ LAWS ly S W mem2 (with_vm_backing (m_vm_lazy md2) mat5 md2) (ms_mem ms5) _).
* img_apply (al_frame _ _ LAWS ly S W mem2 md2 mem2 _ HAR2); [img_try (intros; img_refl) | img_try (intros a Hv; img_exact Hv) | | | | img_try (img_exact (YE0v.hs_kept_refl _ _))]; img_apply (same_but_materialized_frame md2 _ (with_vm_backing_same md2 mat5)).
* intros a Hr Hown. img_apply AV5.
* intros a Hv. rewrite AV5. img_exact Hv.
* img_apply MF. * img_apply MF. * img_apply MF.
* img_exact (YE0v.hs_kept_eq _ _ _ MEQ5).
+ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P2. img_apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by img_lia. img_lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P3, (Y 3%nat 3%bv eq_refl), (GG 3 3%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P4, (Y 4%nat 4%bv eq_refl), (GG 4 4%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P8. img_exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P9. img_exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by img_lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P18. img_exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P19, (Y 19%nat 19%bv eq_refl), (GG 19 19%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 19%bv 19%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P20, (Y 20%nat 20%bv eq_refl), (GG 20 20%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 20%bv 20%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P21, (Y 21%nat 21%bv eq_refl), (GG 21 21%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 21%bv 21%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P22, (Y 22%nat 22%bv eq_refl), (GG 22 22%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 22%bv 22%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P23, (Y 23%nat 23%bv eq_refl), (GG 23 23%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 23%bv 23%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P24, (Y 24%nat 24%bv eq_refl), (GG 24 24%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 24%bv 24%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P25, (Y 25%nat 25%bv eq_refl), (GG 25 25%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 25%bv 25%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P26, (Y 26%nat 26%bv eq_refl), (GG 26 26%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 26%bv 26%nat eq_refl ltac:(img_try (cbn; img_lia))).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite P27, (Y 27%nat 27%bv eq_refl), (GG 27 27%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact (RK 27%bv 27%nat eq_refl ltac:(img_try (cbn; img_lia))).
+ eapply same_but_materialized_trans; [img_try (img_exact MF1)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm2)|]. img_apply with_vm_backing_same.
+ rewrite P10, (Y 10%nat 10%bv eq_refl). img_exact A10_2.
+ unfold stderr_after_vfprintf in *. revert HFW2. generalize stderr_fields_after_vf. intros flds Hf.
unfold file_is in *. img_apply Forall_forall. intros [[o nn] v] Hin. pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. cbn beta iota in Hv |- *.
img_apply (YF8r.val_mem_ext (mrestrict H mem2)); [|img_try (img_exact Hv)]. intros j Hj. img_apply mbyte_of_aview. img_apply AV5.
+ intros a Hr Hs Hf. rewrite AV5. rewrite AV2; [| img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia) | img_try (img_exact Hf)]. img_apply AV1; [img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia)].
+ intros a Hr Hf Hp. img_apply (apresent_same H mem2 (ms_mem ms5) a (MEQ5 _)). img_apply Hpm2; [img_try (img_exact Hr) | img_try (img_exact Hf)|]. img_apply PM1. img_exact Hp.
+ img_exact HAI6.
Qed.
End t.
End g.
