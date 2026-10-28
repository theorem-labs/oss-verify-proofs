(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN32.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3f AE2p AE3i AE39 AE3h AE3j AE31 AE38 AE7c AE7d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition FP_ENTRY : Z := 0x4192c.
Definition FP_REAL : Z := 0x93ad0.
Definition FP_RET : Z := 0x451d4.
Definition FP_ALIGN : Z := 0x63970.
Definition FP_WIN : Z := 2432.
Definition FPI_STK : Z := 9216.
Definition FMT : Z := 0x1d727.
Lemma fp_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_fp FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_fp tbl_fp_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma fp_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_fp FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fp tbl_fp_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition fpA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x9df88, 8, [(0, 8%N, 0x137b28)]); (0x137b7c, 1, [(0, 1%N, 1)]); (0x9fd10, 8, [(0, 8%N, 0x93ad0)])].
Lemma fpA_rodata_chk : forall ly, rodata_chk ly fpA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition SH_LO : Z := 0x7fffbae0.  Definition SH_HI : Z := 0x7fffbae8.
Definition shz : YP09.region := YP09.mkRegion None SH_LO SH_HI SH_LO SH_LO [YP09.mkChunk SH_LO (CZero (SH_HI - SH_LO))].
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FP_WIN) 0 (- FP_WIN) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 1 (2^47) 0)].
Definition regsA : list sv := Eval vm_compute in (firstn 11 sr_atoms ++ [SLit FMT] ++ skipn 12 sr_atoms).
Definition memA : smem := stkA :: shz :: img_ro_region :: map ro_region fpA_rodata.
Definition ssA : sstate := mkSS FP_ENTRY regsA memA None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_fp FUEL FP_REAL s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_fp FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Definition eA1 : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A1 : RUNTOR ssA = (eA1, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2328))) (SLit 15)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition FP_LW : Z := 0x44734.
Definition FP_SLCALL : Z := 0x447ac.
Definition FP_CHKEND : Z := 0x4470c.
Definition OSP : Z := -2352.
Definition CLOBP : list (bv 5) := (CLOB ++ [23%bv])%list.
Definition RUNTOS (s : sstate) := sym_run_toN tfibsegs tbl_fp FUEL A_ISL s.
Definition eA2 : sstate := Eval vm_compute in fst (RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0))).
Lemma r_A2 : RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)) = (eA2, RS_stopped (SR_load (Some 2%nat) (-2324))). Proof. vm_compute. reflexivity. Qed.
Definition rA2 : YP09.region := Eval vm_compute in (hd stkA (ss_mem eA2)).
Definition restA2 : list YP09.region := Eval vm_compute in (tl (ss_mem eA2)).
Lemma memA2_eq : ss_mem eA2 = rA2 :: restA2. Proof. vm_compute. reflexivity. Qed.
Definition eA2' : sstate := set_regs_pc eA2 [((11%bv : bv 5), SLit 0)] (ss_pc eA2 + 4).
Definition eA3 : sstate := Eval vm_compute in fst (RUNTOS eA2').
Lemma r_A3 : RUNTOS eA2' = (eA3, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition rA3 : YP09.region := Eval vm_compute in (hd stkA (ss_mem eA3)).
Definition restA3 : list YP09.region := Eval vm_compute in (tl (ss_mem eA3)).
Lemma memA3_eq : ss_mem eA3 = rA3 :: restA3. Proof. vm_compute. reflexivity. Qed.
Definition rest_okb (l : list YP09.region) : bool :=
forallb (fun r => obase_eqb (YP09.r_base r) None && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 2 ^ 43) && (YP09.r_whi r <=? YP09.r_wlo r)) l.
Lemma rest_okb_sound : forall l, rest_okb l = true ->
forall r, In r l -> YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43 /\ YP09.r_whi r <= YP09.r_wlo r.
Proof.
intros l Hl r Hr. unfold rest_okb in Hl. rewrite forallb_forall in Hl. specialize (Hl r Hr). cbn beta in Hl.
apply andb_prop in Hl as [Hl H4]. apply andb_prop in Hl as [Hl H3]. apply andb_prop in Hl as [H1 H2].
apply obase_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. repeat split; assumption.
Qed.
Lemma restA3_ok : rest_okb restA3 = true. Proof. vm_compute. reflexivity. Qed.
Definition fp_after (k : nat) (ss : sstate) : sstate :=
match ss_mem ss with
| r0 :: rest =>
mkSS FP_CHKEND (sr_sets (ss_regs ss) (junk_upd k CLOBP))
(YP09.mkRegion (YP09.r_base r0) (YP09.r_lo r0) (YP09.r_hi r0) (YP09.r_wlo r0) (YP09.r_whi r0)
(List.filter (fun c => OSP <=? YP09.c_off c) (YP09.r_chunks r0)) :: rest)
None (ss_facts ss)
| [] => ss
end.
Definition eA3r : sstate := Eval vm_compute in fp_after 32 eA3.
Lemma eA3r_eq : fp_after 32 eA3 = eA3r. Proof. vm_compute. reflexivity. Qed.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR eA3r).
Lemma r_A4 : RUNTOR eA3r = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition shapeS (ss : sstate) : bool :=
(ss_pc ss =? A_ISL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_lo r =? - FP_WIN) && (YP09.r_hi r =? 0) && (YP09.r_wlo r =? - FP_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 1 (SLit FP_SLCALL) && reg_is ss 2 (SOff 2 OSP) && reg_is ss 10 (SOff 12 0) && reg_is ss 22 (SOff 12 0).
Lemma shapeS_ok : shapeS eA3 = true. Proof. vm_compute. reflexivity. Qed.
Definition chunk1_is (off : Z) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 1 && sv_eqb e (SLit 0) | _ => false end.
Definition W_LW : Z := Eval vm_compute in match clookup tbl_fp FP_LW with Some w => w | None => 0 end.
Lemma lw_fetch : clookup tbl_fp FP_LW = Some W_LW /\ decode_any (Z_to_bv 32 W_LW) = Some (Load SZ4 true 11%bv 24%bv (4068%bv : bv 12), 4).
Proof. split; [vm_compute; reflexivity | vm_refl_bv]. Qed.
Lemma lw_bytes_ok : forallb (fun k => existsb (chunk1_is (-2324 + k)) (YP09.r_chunks rA2)) [0; 1; 2; 3] = true
/\ ss_pc eA2 = FP_LW /\ reg_is eA2 24 (SOff 2 (-2296)) = true /\ YP09.r_base rA2 = Some 2%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma not_clobp_cases : forall r : bv 5, reg_in r CLOBP = false -> r = 0%bv \/ (acallee_saved (bv_unsigned r) /\ bv_unsigned r <> 23).
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin. unfold acallee_saved.
repeat (destruct Hin as [<-|Hin];
[first [ left; reflexivity
| vm_compute in Hr; discriminate
| right;
match goal with |- context [bv_unsigned ?x] =>
let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end;
lia ] |]).
destruct Hin.
Qed.
Lemma fp_lw_zero : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (imm : bv 12) (w : Z) (h : Z) (K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_fp (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ4 true rd rs imm, 4) -> bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h + bv_signed imm -> h + bv_signed imm + 4 <= 2 ^ 64 -> 0 <= h < 2 ^ 64 ->
(forall k, 0 <= k < 4 -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (h + bv_signed imm + k) = Some (Z_to_bv 8 0)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SLit 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\ ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs imm w h K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh4 Hh64 Hb. pose proof AF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_fp_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity]. apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
assert (Hrdn : rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (v_addi (getr (ms_regs ms) rs) (bv_signed imm)) 4 = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
{ rewrite R, v_addi_lit. apply (proj2 (rdn_mbytes tfibsegs _ 4 _ _)). split; [reflexivity|].
intros i Hi. rewrite (Hb (Z.of_nat i)) by lia. do 4 (destruct i as [|i]; [reflexivity|]). lia. }
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_lw tfibsegs _ _ _ _ _ rd rs imm _ (Z_to_bv 64 0) Hfetch Hec Hdec Hrdn). vm_compute. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SLit 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). apply bv_eq. vm_compute. reflexivity.
Qed.
Section q.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Lemma pc_scheck : forall (W : world tfibsegs) E ss ms md ly S (sp0 : Z) r0 rest k (x L : Z) (str : list byte),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_pc ss = A_ISL -> ss_resv ss = None ->
bv_unsigned (ew E 2) = sp0 -> ew E 12 = Z_to_bv 64 x ->
ss_mem ss = r0 :: rest -> YP09.r_base r0 = Some 2%nat -> YP09.r_lo r0 = - FP_WIN -> YP09.r_hi r0 = 0 ->
YP09.r_wlo r0 = - FP_WIN -> YP09.r_whi r0 = 0 ->
sr_get (ss_regs ss) 1 = SLit FP_SLCALL -> sr_get (ss_regs ss) 2 = SOff 2 OSP -> sr_get (ss_regs ss) 10 = SOff 12 0 -> sr_get (ss_regs ss) 22 = SOff 12 0 ->
ss_atoms_lt k ss = true ->
regions_wf (ss_mem (fp_after k ss)) = true ->
no_cdata (ss_mem (fp_after k ss)) = true ->
mem_atoms_lt k (ss_mem (fp_after k ss)) = true ->
forallb (chunk_inside r0) (YP09.r_chunks r0) = true ->
(forall r, In r rest -> YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 2 ^ 43 /\ YP09.r_whi r <= YP09.r_wlo r) ->
AR tfibsegs B ly S W (ms_mem ms) md ->
2 ^ 44 <= sp0 -> sp0 mod 16 = 0 -> ly_stk_lo ly + FPI_STK <= sp0 -> sp0 <= ly_stk_hi ly ->
(forall a, sp0 - FPI_STK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) ->
vf_str W (ms_mem ms) x str -> L = Z.of_nat (length str) -> L + 1 < 2 ^ 32 -> 0 < x -> x + L + 1 <= 2 ^ 47 ->
amem_range x (L + 1) ->
range_addressable (aview tfibsegs (w_H W) (ms_mem ms)) SHADOW_OFF x (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms)) x (L + 1) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms2 md2,
c' = mkCfg ms2 md2 /\
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms2)) CLOBP)) (fp_after k ss) (restrict (w_H W) ms2) /\
AR tfibsegs B ly S W (ms_mem ms2) md2 /\ same_but_materialized md md2 /\
(forall z : word, ~ (sp0 + OSP - 72 <= bv_unsigned z < sp0 + OSP) -> ms_mem ms2 z = ms_mem ms z) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms2) a)).
Proof.
intros W E ss ms md ly S sp0 r0 rest k x L str HS Hpc Hrv Usp E12 Hmem0 Hb0 Hlo0 Hhi0 Hwlo0 Hwhi0 S1 S2 S10 S22
Hat Hwf2 Hnc2 Hma2 Hci0 Hrest HAR Hsp44 Hsp16 Hstk Htop Hpres HSTR HL HL32 Hx0 Hxhi Hamx Hra_x Hhull_x.
pose proof AF0x.Hwx_tfa as Hwx. unfold FPI_STK in *. unfold OSP in *.
assert (HFPW : FP_WIN = 2432) by reflexivity. assert (HISL : A_ISL = 408252) by reflexivity. assert (HSLC : FP_SLCALL = 280492) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hamr : x + L + 1 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamx; lia).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *. set (H := w_H W) in *.
assert (R1 : getr regsT 1 = Z_to_bv 64 FP_SLCALL) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 1 HS), S1; reflexivity).
assert (R2 : getr regsT 2 = Z_to_bv 64 (sp0 - 2352)) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 2 HS), S2; cbn [sv_denot]; rewrite Usp; f_equal; lia).
assert (R10 : getr regsT 10 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 10 HS), S10; cbn [sv_denot]; rewrite E12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (R22 : getr regsT 22 = w64 x) by (rewrite (st_ok_restrict_reg tfibsegs H E _ _ 22 HS), S22; cbn [sv_denot]; rewrite E12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
pose proof HS as HSc. destruct HSc as (_ & _ & _ & _ & _ & _ & _ & HmemT & HG). cbn [restrict ms_mem] in HmemT. fold memT in HmemT.
destruct HSTR as (Hsb & Hs0 & Hnz).
assert (LEN : Z.of_nat (length str) = L) by lia.
assert (Hnul : ~ In NUL str).
{ intros Hin. apply In_nth with (d := NUL) in Hin as (j & Hj & Hnj). pose proof (proj1 (Forall_forall _ _) Hnz _ (nth_In str NUL Hj)) as Hb. apply Hb. rewrite Hnj. reflexivity. }
assert (Hrd : forall j, (j <= length str)%nat -> rdn tfibsegs (mrestrict H memT) (Z_to_bv 64 (bv_unsigned (w64 x) + Z.of_nat j)) 1 = Some [nth j (str ++ [NUL]) NUL]).
{ intros j Hj. unfold w64. rewrite unsigned_lit_small by lia.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
destruct (Nat.lt_ge_cases j (length str)) as [Hlt|Hge].
- rewrite app_nth1 by lia. rewrite (AF0x.aview_byte H memT _ (bv_unsigned (nth j str 0%bv))); [rewrite Z_to_bv_bv_unsigned; rewrite (nth_indep _ 0%bv NUL) by lia; reflexivity|]. exact (Hsb j Hlt).
- assert (Hj' : j = length str) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
rewrite (AF0x.aview_byte H memT _ 0); [reflexivity|]. exact Hs0. }
destruct (tfib_istrlen str (w64 x) (mrestrict H memT) (seg_rom tfibsegs) regsT R10 Hnul Hrd ltac:(unfold w64; rewrite unsigned_lit_small by lia; lia)) as (regs2 & Hms & A10 & KEEP).
rewrite R1 in Hms. replace (v_jalr (Z_to_bv 64 FP_SLCALL) 0) with (Z_to_bv 64 FP_SLCALL : word) in Hms by (apply bv_eq; vm_compute; reflexivity).
rewrite Hshape. unfold memT in Hms |- *.
eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact Hms|].
intros model' Hsbm _. cbn [unrestrict ms_regs ms_pc ms_mem ms_rom]. fold H.
set (mem2 := munrestrict H (ms_mem ms) (mrestrict H (ms_mem ms))).
assert (M2 : forall z, mem2 z = ms_mem ms z) by (intros z; subst mem2; apply AE7d.munrestrict_mrestrict_same).
assert (AV2 : forall a, aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms) a) by (intros a; apply aview_same; apply M2).
assert (K2 : forall (rr : bv 5), rr <> 10%bv -> rr <> 11%bv -> rr <> 12%bv -> getr regs2 rr = getr regsT rr) by (intros rr; apply KEEP).
assert (R2sp : spZ regs2 = sp0 - 2352) by (unfold spZ; rewrite (K2 2%bv) by (intros H'; discriminate H'); rewrite R2; apply unsigned_lit_small; lia).
assert (HAR2 : AR tfibsegs B ly S W mem2 model').
{ apply (al_frame _ _ LAWS ly S W (ms_mem ms) md mem2 _ HAR); [intros a _ _; apply AV2 | intros a Hv; rewrite AV2; exact Hv | | | | exact (AE2y.hs_kept_eq _ _ _ M2)]; apply (same_but_materialized_frame md _ Hsbm). }
eapply SRr_bind.
{ apply (pfs_check_srr B LAWS TB ly S W regs2 mem2 model' x (L + 1) HAR2).
- rewrite R2sp. replace (sp0 - 2352) with (sp0 + (-147) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16.
- rewrite R2sp. unfold AE7c.RC_SCR. lia.
- rewrite R2sp. lia.
- intros a Ha. rewrite R2sp in Ha. unfold AE7c.RC_SCR in Ha. apply (apresent_same H (ms_mem ms) mem2 a (M2 _)). apply Hpres. lia.
- rewrite A10, LEN. unfold w64. f_equal; lia.
- rewrite (K2 22%bv) by (intros H'; discriminate H'). exact R22.
- exact Hx0.
- lia.
- lia.
- lia.
- exact Hamx.
- eapply range_addressable_agree; [|exact Hra_x]. intros z Hz. apply AV2.
- intros s' Hs. rewrite AV2. exact (Hhull_x s' Hs). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & _ & Hfr3 & Hpm3 & Hptw3).
rewrite R2sp in Hfr3, Hptw3. unfold AE7c.RC_SCR in Hfr3, Hptw3.
apply SRr_ret. split; [reflexivity|]. exists (mkst regs3 (w64 AE7c.RC_END) mem3 (seg_rom tfibsegs)), md3.
split; [reflexivity|].
destruct HmemT as (HwfT & HokT & HpdT). rewrite Hmem0 in HwfT, HokT, HpdT.
pose proof (Forall_inv HokT) as Hok0. pose proof (Forall_inv_tail HokT) as HokR.
destruct r0 as [b0 lo0 hi0 wlo0 whi0 cs0]. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks] in *.
subst b0 lo0 hi0 wlo0 whi0.
unfold fp_after in Hwf2, Hnc2, Hma2 |- *. rewrite Hmem0 in Hwf2, Hnc2, Hma2 |- *.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ss_mem] in Hwf2, Hnc2, Hma2 |- *.
split; [|split; [exact HAR3 | split; [|split]]].
- rewrite restrict_mkst_fx. cbn [ms_regs mkst]. change (w64 AE7c.RC_END) with (Z_to_bv 64 FP_CHKEND).
rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
lazymatch goal with |- st_ok _ _ (mkSS _ _ ?rs _ _) _ =>
pose proof (st_ok_splice_havoc tfibsegs k E ss regsT regs3 (Z_to_bv 64 A_ISL) FP_CHKEND
(mrestrict H (ms_mem ms)) (mrestrict H mem3) rs [] CLOBP HS Hat) as SPL end.
cbn [map app fst] in SPL. apply SPL; clear SPL.
+ vm_compute. reflexivity.
+ vm_compute. reflexivity.
+ reflexivity.
+ exact Hma2.
+ intros r Hr. destruct (not_clobp_cases r Hr) as [-> | [Hcs Hne]]; [rewrite !getr_zero; reflexivity|].
rewrite <- (Z_to_bv_bv_unsigned 5 r). rewrite (K3 (bv_unsigned r) Hcs Hne). rewrite Z_to_bv_bv_unsigned.
apply K2; intros ->; clear -Hcs Hne; unfold acallee_saved in Hcs;
match type of Hne with bv_unsigned ?x <> _ => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v in * end; lia.
+ constructor.
+ split; [exact Hwf2|]. split.
* constructor.
-- destruct Hok0 as (Hlo & Hhi & Hw & Hcs). unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in *. rewrite Usp in *.
split; [exact Hlo|]. split; [exact Hhi|]. split.
{ intros off Ho. apply AE2y.apresent_writable. apply Hpm3. apply (apresent_same H (ms_mem ms) mem2 _ (M2 _)). apply Hpres. lia. }
apply Forall_forall. intros c Hc. apply filter_In in Hc as [Hc Hk1]. apply Z.leb_le in Hk1. unfold OSP in Hk1.
pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as Hck.
pose proof (chunk_inside_facts _ c (proj1 (forallb_forall _ _) Hci0 c Hc)) as (Ci1 & Ci2 & Ci3).
cbn [YP09.r_lo YP09.r_hi] in Ci1, Ci2.
intros i Hi. destruct (Hck i Hi) as (bb & Hb1 & Hb2). exists bb. split; [exact Hb1|].
rewrite <- Hb2. apply mbyte_of_aview. rewrite Hfr3; [apply AV2 | lia | lia].
-- apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) HokR r Hr) as Hokr.
destruct (Hrest r Hr) as (Hrb & Hrl & Hrh & Hrw).
eapply (region_ok_transport tfibsegs E E); [exact Hokr | reflexivity | | | | ].
++ intros c Hc. unfold no_cdata in Hnc2. cbn [forallb] in Hnc2. apply andb_prop in Hnc2 as [_ HncR].
pose proof (proj1 (forallb_forall _ _) HncR r Hr) as Hncr. pose proof (proj1 (forallb_forall _ _) Hncr c Hc) as Hncc.
cbn beta in Hncc. destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate].
++ intros a Ha. apply mbyte_of_aview. rewrite Hrb in Ha. cbn [base_val] in Ha. rewrite Hfr3; [apply AV2 | lia | lia].
++ intros a Ha _. exfalso. lia.
++ apply regions_wf_In with (r := r) in HwfT; [|right; exact Hr]. apply region_wf_facts in HwfT as (_ & _ & Hci). exact Hci.
* eapply pairwise_disjoint_extents; [|exact HpdT]. reflexivity.
- eapply same_but_materialized_trans; [exact Hsbm | exact Hsbm3].
- intros z Hz. cbn [ms_mem mkst]. rewrite Hptw3 by exact Hz. apply M2.
- intros a Hp. cbn [ms_mem mkst]. apply Hpm3. apply (apresent_same H (ms_mem ms) mem2 a (M2 _)). exact Hp.
Qed.
End q.
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 56 (CVal 8 (SOff 32 0));
YP09.mkChunk 48 (CVal 8 (SOff 33 0));
YP09.mkChunk 40 (CVal 8 (SOff 34 0));
YP09.mkChunk 32 (CVal 8 (SOff 35 0))].
Definition ss_epi : sstate := mkSS FP_RET sr_atoms [YP09.mkRegion (Some 2%nat) 0 112 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition SAVEDA : list (Z * Z) := [(1, -56); (8, -64); (9, -72); (18, -80); (12, -48)].
Definition KEPTA : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FP_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - FP_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SLit FMT) && reg_is ss 12 (SOff 2 (-48)) &&
reg_is ss 1 (SLit FP_RET) && reg_is ss 2 (SOff 2 (-112)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma br_memset_align : forall E sp0, bv_unsigned (ew E 2) = sp0 -> sp0 mod 16 = 0 -> 2 ^ 44 <= sp0 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2328))) (SLit 15))) (sv_denot E (SLit 0)) = false.
Proof.
intros E sp0 H2 Hal Hsp. rewrite branch_eq_U, !U_SAlu, !U_SLit, U_SOff, H2. cbn [zalu_raw].
rewrite (zcanon_small 40), (zcanon_small 15), (zcanon_small 0), (zcanon_small (sp0 + -2328)) by lia.
assert (Hm : (sp0 + -2328) mod 16 = 8).
{ replace (sp0 + -2328) with (sp0 - 146 * 16 + 8) by lia. rewrite <- Z.add_mod_idemp_l by lia.
replace ((sp0 - 146 * 16) mod 16) with 0; [reflexivity|]. rewrite <- Zminus_mod_idemp_l. rewrite Hal. reflexivity. }
assert (Hand : Z.land (Z.lor 40 (sp0 + -2328)) 15 = 8).
{ rewrite Z.land_lor_distr_l. change 15 with (Z.ones 4). rewrite !Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Hm. reflexivity. }
assert (Hlt : Z.lor 40 (sp0 + -2328) < 2 ^ 64).
{ destruct (Z.eq_dec (Z.lor 40 (sp0 + -2328)) 0) as [E0|E0]; [rewrite E0; lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg 40 (sp0 + -2328)); lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; [cbv; reflexivity | apply Z.log2_lt_pow2; lia]. }
rewrite (zcanon_small (Z.lor 40 (sp0 + -2328))) by (pose proof (Z.lor_nonneg 40 (sp0 + -2328)); lia).
rewrite Hand. reflexivity.
Qed.
Section t.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis TL : TfibSyms B.
Lemma ocpy_of_icpt : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof. rewrite (ts_code B TB). exact (memcpy_icpt_realizes B LAWS TB). Qed.
Lemma astrnlen_of_icpt : astrnlen_realizesM B (pc_wrap_strnlen (as_code B)).
Proof. rewrite (ts_code B TB). exact (strnlen_icpt_contractM B LAWS TB TL). Qed.
Theorem tfib_fprintf_icpt_open : forall ly S (W : world tfibsegs) regs mem md ch s (str : list byte) L cval T,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + FPI_STK <= spZ regs ->
(forall a, spZ regs - FPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 F_STDERR -> getr regs 11 = w64 FMT_open -> getr regs 12 = w64 s ->
L = Z.of_nat (length str) -> L <= 33554415 ->
1 <= s -> s + L + 1 <= 2 ^ 47 ->
(s + L + 1 <= spZ regs - FPI_STK \/ spZ regs <= s) ->
(s + L + 1 <= F_STDERR \/ F_STDERR + FILE_SZ <= s) -> amem_range s (L + 1) ->
vf_tail W mem s L -> mconsts_view W mem ->
vf_str W mem s str ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s (L + 1) ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) s (L + 1) ->
stderr_pristine (mrestrict (w_H W) mem) -> (forall a, vf_file a -> ~ aowned B ly S a) ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_GOT_canary 8 A_canary ->
val_mem tfibsegs (mrestrict (w_H W) mem) A_canary 8 cval -> 0 <= cval < 2 ^ 64 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview tfibsegs (w_H W) mem) FMT_open 21 ->
fdchan (Z_to_bv 64 2) ch md -> AI tfibsegs (w_H W) (w_A W) md ->
(forall regs' mem' md',
AR tfibsegs B ly S W mem' md' -> aregs_preserved regs regs' -> same_but_materialized md md' ->
getr regs' 10 = w64 (L + 18) ->
stderr_after_vfprintf (mrestrict (w_H W) mem') ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FPI_STK <= a < spZ regs) -> ~ vf_file a -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ vf_file a -> apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
AI tfibsegs (w_H W) (w_A W) md' ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs' mem' md') T) ->
srealizes tfibsegs (cfg_at tfibsegs FP_ENTRY regs mem md)
(t_emit (map (WriteEv ch) (map (Z_to_bv 8) lit_open1 ++ str ++ map (Z_to_bv 8) lit_open2)) T).
Proof.
intros ly S W regs mem md ch s str L cval T HPRE Hstk Hpres G10 G11 G12 HL HLhi Hs1 Hshi Hsband Hsfile Hams Hstail Hromv HSTR Hra_s Hhull_s
HFP HFown Hgot Hcan Hcv Hro HZ Hch HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold FPI_STK in *.
assert (HFS : FILE_SZ = 232) by reflexivity. assert (HFF : F_STDERR = 664952) by reflexivity.
assert (HGC : A_GOT_canary = 0x9ec38) by reflexivity. assert (HCA : A_canary = 0x5f8fd0) by reflexivity.
assert (HVFS : VF_STK = 9104) by reflexivity. assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
assert (HFMT : FMT_open = FMT) by reflexivity. assert (HFMTV : FMT = 120615) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfibsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf. lia. }
assert (FT : forall flds (m m' : word -> option byte),
Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) flds ->
file_is flds (mrestrict H m) ->
(forall b, F_STDERR <= b < F_STDERR + FILE_SZ -> aview tfibsegs H m' b = aview tfibsegs H m b) -> file_is flds (mrestrict H m')).
{ intros flds m m' Hwf Hf Hb. unfold file_is in *. apply Forall_forall. intros [[o nn] v] Hin.
pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. pose proof (proj1 (Forall_forall _ _) Hwf _ Hin) as Ho. cbn beta iota in Hv, Ho |- *.
apply (VT m); [exact Hv|]. intros b Hbb. apply Hb. pose proof (N_nat_Z nn). lia. }
assert (WF1 : Forall (fun f : Z * N * Z => match f with (o, nn, _) => 0 <= o /\ o + Z.of_N nn <= FILE_SZ end) stderr_fields) by (unfold stderr_fields, FILE_SZ; repeat constructor; cbn; lia).
unfold cfg_at. change (w64 FP_ENTRY) with (Z_to_bv 64 FP_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 F_STDERR) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE12 : ew EE 12 = Z_to_bv 64 s) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (HZ' : forall sa, SH_LO <= sa < SH_HI -> aview tfibsegs H mem sa = Some 0).
{ intros sa Hsa. apply HZ. unfold SH_LO, SH_HI in Hsa.
match goal with |- ?a <= sa < ?b => let a' := eval vm_compute in a in change a with a'; let b' := eval vm_compute in b in change b with b' end. lia. }
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 FP_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
apply (st_ok_regs tfibsegs EE (mkSS FP_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 11 11%bv eq_refl), G11; reflexivity) ] |]).
destruct Hr. }
unfold memA, EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [apply Hro | exact (rodata_ok B TB fpA_rodata ly S H mem EE (fpA_rodata_chk ly) (proj1 HAR))]]].
+ unfold stkA, FP_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2432)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia.
+ unfold shz, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold SH_LO, SH_HI. split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|]. apply HZ'. unfold SH_LO, SH_HI. cbn in Hi. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, shz, img_ro_region, fpA_rodata, icpt_rodata, ro_region, extent_of_region, FP_WIN, SH_LO, SH_HI, IMG_RO_LO, IMG_RO_HI.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE12, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. repeat split; first [exact Hal16 | apply Z.mod_1_r | subst sp0; lia | lia]. }
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HS0 r_A1) HAI0).
intros Wa ca _ HAIa (-> & msa & mata & -> & HSa & HFa & HFra). cbn [cfg_model] in HAIa. rewrite ?wvb_wvb in HAIa |- *.
assert (MEQa : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msa z = mem z).
{ intros z Hz. apply (HFa z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold FP_WIN in *. lia. }
clear HFa HFra.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG eA1 13) (SLit 0) HSa (br_memset_align EE sp0 EE2 Hal16 ltac:(lia))) as HSa'.
change (neg_bc BC_EQ) with BC_NE in HSa'. clear HSa.
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSa' r_A2) HAIa).
intros Wb cb _ HAIb (-> & msb & matb & -> & HSb & HFb & HFrb). cbn [cfg_model] in HAIb. rewrite ?wvb_wvb in HAIb |- *.
assert (MEQb : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msb z = mem z).
{ intros z Hz. rewrite (HFb z); [apply MEQa; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold FP_WIN in *. lia. }
clear HFb HFrb.
pose proof lw_bytes_ok as (LWB & LWpc & LWs8 & LWbase).
assert (Hb4 : forall kk, 0 <= kk < 4 -> mbyte tfibsegs (mrestrict H (ms_mem msb)) (sp0 - 2296 + (-28) + kk) = Some (Z_to_bv 8 0)).
{ intros kk Hkk. pose proof (st_ok_mem_ok tfibsegs EE eA2 _ HSb) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite memA2_eq in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
rewrite forallb_forall in LWB.
assert (Hin4 : forall j, In j [0; 1; 2; 3] -> exists c, In c (YP09.r_chunks rA2) /\ c = YP09.mkChunk (-2324 + j) (CVal 1 (SLit 0))).
{ intros j Hj. specialize (LWB j Hj). apply existsb_exists in LWB as (c & Hc1 & Hc2). exists c. split; [exact Hc1|].
unfold chunk1_is in Hc2. destruct c as [o cv]. cbn [YP09.c_off YP09.c_val] in Hc2. apply andb_prop in Hc2 as [Ho Hv]. apply Z.eqb_eq in Ho.
destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He]. apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity. }
assert (Hkk' : In kk [0; 1; 2; 3]) by (cbn; lia).
destruct (Hin4 kk Hkk') as (c & Hc & ->).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite LWbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
pose proof (val_of_chunk_ok tfibsegs EE _ _ (-2324 + kk) 1 (SLit 0) 0 Hck eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
pose proof (Hv 0%nat ltac:(lia)) as Hv0. cbn [Z.of_nat] in Hv0. rewrite Z.add_0_r in Hv0.
replace (sp0 - 2296 + -28 + kk) with (sp0 + (-2324 + kk)) by lia. etransitivity; [exact Hv0 | reflexivity]. }
assert (Hat2 : ss_atoms_lt 32 eA2 = true) by (vm_compute; reflexivity).
pose proof lw_fetch as [LWlk LWdec]. rewrite <- LWpc in LWlk.
assert (LWrs : sv_denot EE (sr_get (ss_regs eA2) 24%bv) = Z_to_bv 64 (sp0 - 2296)).
{ unfold reg_is, RG in LWs8. apply sv_eqb_eq in LWs8. replace (Z_to_bv 5 24) with (24%bv : bv 5) in LWs8 by (apply bv_eq; reflexivity).
rewrite LWs8. cbn [sv_denot]. rewrite EE2. reflexivity. }
pose proof (fp_lw_zero W EE eA2 msb (with_vm_backing (m_vm_lazy md) matb md) 11%bv 24%bv (4068%bv : bv 12) W_LW (sp0 - 2296) 32
HSb eq_refl Hat2 LWlk LWdec eq_refl LWrs
ltac:(change (bv_signed (4068%bv : bv 12)) with (-28); lia)
ltac:(change (bv_signed (4068%bv : bv 12)) with (-28); lia)
ltac:(lia)
ltac:(change (bv_signed (4068%bv : bv 12)) with (-28); exact Hb4)) as STEP.
eapply (SRr_srealizes tfibsegs W _ _ _ STEP HAIb). clear STEP.
intros Wc cc _ HAIc (-> & msc & matc & -> & HSc & HMc). cbn [cfg_model] in HAIc. rewrite ?wvb_wvb in HAIc |- *.
rewrite LWpc in HSc. change (set_regs_pc eA2 [(11%bv, SLit 0)] (FP_LW + 4)) with eA2' in HSc.
assert (MEQc : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msc z = mem z) by (intros z Hz; rewrite HMc; apply MEQb; exact Hz).
clear HMc.
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE A_ISL _ _ _ _ _ HSc r_A3) HAIc).
intros Wd cd _ HAId (-> & msd & matd & -> & HSd & HFd & HFrd). cbn [cfg_model] in HAId. rewrite ?wvb_wvb in HAId |- *.
assert (MEQd : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msd z = mem z).
{ intros z Hz. rewrite (HFd z); [apply MEQc; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold FP_WIN in *. lia. }
clear HFd HFrd.
assert (AVd : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2432 <= a < sp0) -> aview tfibsegs H (ms_mem msd) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQd. rewrite unsigned_lit_small by lia. exact Ha. }
pose proof shapeS_ok as SSH. unfold shapeS in SSH. rewrite memA3_eq in SSH.
apply andb_prop in SSH as [SSH S22]. apply andb_prop in SSH as [SSH S10]. apply andb_prop in SSH as [SSH S2]. apply andb_prop in SSH as [SSH S1]. apply andb_prop in SSH as [Spc Smemd].
pose proof memA3_eq as Hmemd.
apply andb_prop in Smemd as [Smemd Swhi]. apply andb_prop in Smemd as [Smemd Swlo]. apply andb_prop in Smemd as [Smemd Shi]. apply andb_prop in Smemd as [Sbase Slo].
apply obase_eqb_eq in Sbase. apply Z.eqb_eq in Slo. apply Z.eqb_eq in Shi. apply Z.eqb_eq in Swlo. apply Z.eqb_eq in Swhi. apply Z.eqb_eq in Spc.
unfold reg_is, RG in S1, S2, S10, S22. apply sv_eqb_eq in S1. apply sv_eqb_eq in S2. apply sv_eqb_eq in S10. apply sv_eqb_eq in S22.
replace (Z_to_bv 5 1) with (1%bv : bv 5) in S1 by (apply bv_eq; reflexivity). replace (Z_to_bv 5 2) with (2%bv : bv 5) in S2 by (apply bv_eq; reflexivity).
replace (Z_to_bv 5 10) with (10%bv : bv 5) in S10 by (apply bv_eq; reflexivity). replace (Z_to_bv 5 22) with (22%bv : bv 5) in S22 by (apply bv_eq; reflexivity).
assert (PRSd : forall a, sp0 - 2432 <= a < sp0 -> apresent H (ms_mem msd) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA3 msd 0 rA3 a HSd ltac:(rewrite Hmemd; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Sbase, Swlo, Swhi. cbn [base_val]. rewrite EE2. unfold FP_WIN. lia. }
assert (PMd : forall a, apresent H mem a -> apresent H (ms_mem msd) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem msd) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [apply (apresent_same H mem (ms_mem msd) a'); [apply MEQd; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRSd; lia|].
apply (apresent_same H mem (ms_mem msd) a'); [apply MEQd; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
assert (HARd : AR tfibsegs B ly S W (ms_mem msd) (with_vm_backing (m_vm_lazy md) matd md)).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem msd) _ HAR).
+ intros a Hr Hown. apply AVd; [exact Hr|]. intros Hs'. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem msd) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [rewrite AVd by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AVd by lia; exact Hv].
apply aview_some_of_apresent. apply PRSd. lia.
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md matd)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md matd)).
+ apply (same_but_materialized_frame md _ (with_vm_backing_same md matd)).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQd HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
eapply (SRr_srealizes tfibsegs W (mkCfg msd (with_vm_backing (m_vm_lazy md) matd md)) _ _); [ | exact HAId | ].
{ apply (pc_scheck B LAWS TB W EE eA3 msd (with_vm_backing (m_vm_lazy md) matd md) ly S sp0 rA3 restA3 32 s L str HSd Spc eq_refl EE2 EE12 Hmemd Sbase Slo Shi Swlo Swhi S1 S2 S10 S22).
- vm_compute. reflexivity.
- rewrite eA3r_eq. vm_compute. reflexivity.
- rewrite eA3r_eq. vm_compute. reflexivity.
- rewrite eA3r_eq. vm_compute. reflexivity.
- vm_compute. reflexivity.
- exact (rest_okb_sound restA3 restA3_ok).
- exact HARd.
- lia.
- exact Hal16.
- unfold FPI_STK. lia.
- lia.
- intros a Ha. unfold FPI_STK in Ha. apply PMd. apply Hpres. lia.
- apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply AVd; [lia | unfold sp0 in *; lia].
- exact HL.
- lia.
- lia.
- lia.
- exact Hams.
- eapply range_addressable_agree; [|exact Hra_s]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. apply AVd; unfold sp0 in *; lia.
- intros s' Hs'. rewrite AVd; [exact (Hhull_s s' Hs') | |];
pose proof (shadow_addr_bounds s ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (s + (L + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr s) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr s) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (s + (L + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (s + (L + 1) - 1)) 8 ltac:(lia)); unfold sp0 in *; lia. }
intros We ce _ HAIe (-> & mse & mde & -> & HSe0 & HARe & Hsbme & Hfre & Hpme). cbn [cfg_model] in HAIe. unfold OSP in Hfre.
rewrite eA3r_eq in HSe0.
assert (MEQe : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem mse z = mem z) by (intros z Hz; rewrite Hfre by lia; apply MEQd; exact Hz).
set (E1 := havoc EE 32 (map (getr (ms_regs mse)) CLOBP)) in HSe0.
assert (E1reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E1 i = getr regs r).
{ intros i r Hi. subst E1. rewrite ew_havoc_old by (pose proof (u5_range r); lia). apply EEreg. exact Hi. }
assert (E1_2 : bv_unsigned (ew E1 2) = sp0) by (rewrite (E1reg 2%nat 2%bv eq_refl); reflexivity).
assert (E1_10 : ew E1 10 = Z_to_bv 64 F_STDERR) by (rewrite (E1reg 10%nat 10%bv eq_refl); exact G10).
assert (E1_12 : ew E1 12 = Z_to_bv 64 s) by (rewrite (E1reg 12%nat 12%bv eq_refl); exact G12).
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W E1 FP_REAL _ _ _ _ _ HSe0 r_A4) HAIe).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQe; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b E1 _ (bv_unsigned z) 2 (- FP_WIN) 0 sp0 _ E1_2 Hin) as X0; [vm_compute; reflexivity|]. unfold FP_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot E1 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E1 eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (E1reg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs E1 eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite E1_2 in Hck.
apply (val_of_chunk_ok tfibsegs E1 _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (E1reg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 F_STDERR) by (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite E1_10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q11 : getr regs1 11 = w64 FMT_open) by (rewrite (RD 11%bv (SLit FMT) R11); reflexivity).
assert (Q12 : getr regs1 12 = w64 (sp0 - 48)) by (rewrite (RD 12%bv (SOff 2 (-48)) R12); cbn [sv_denot]; rewrite E1_2; reflexivity).
assert (Q1 : getr regs1 1 = w64 FP_RET) by (rewrite (RD 1%bv (SLit FP_RET) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 112)) by (rewrite (RD 2%bv (SOff 2 (-112)) R2); cbn [sv_denot]; rewrite E1_2; reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 112) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (R1ra : raZ regs1 = FP_RET) by (unfold raZ; rewrite Q1; unfold w64; apply unsigned_lit_small; unfold FP_RET; lia).
pose proof (st_ok_restrict_mkst tfibsegs H E1 _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy mde) mat1 mde) in *.
assert (MF1 : same_but_materialized md md1).
{ subst md1. eapply same_but_materialized_trans; [apply (with_vm_backing_same md matd)|].
eapply same_but_materialized_trans; [exact Hsbme | apply with_vm_backing_same]. }
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2432 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2432 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H E1 eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E1_2. unfold FP_WIN. lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same H mem (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hp]. }
assert (HAR1 : AR tfibsegs B ly S W (ms_mem ms1) md1).
{ apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. apply AV1; [exact Hr|]. intros Hs. exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(unfold sp0 in *; lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms1) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2432)) as [L1|L1]; [rewrite AV1 by lia; exact Hv|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| rewrite AV1 by lia; exact Hv].
apply aview_some_of_apresent. apply PRS1. lia.
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ apply (same_but_materialized_frame md _ MF1).
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(unfold sp0 in *; lia) ltac:(lia)). }
assert (HPRE1 : ecall_pre tfibsegs B ly S W regs1 (ms_mem ms1) md1).
{ split; [exact HAR1|]. split; [rewrite Q1; apply (ret_ok_lit FP_RET); [unfold FP_RET; lia | reflexivity]|].
split; [rewrite R1sp; replace (sp0 - 112) with (sp0 + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite R1sp; unfold ESTACK; unfold sp0 in *; lia|]. split; [rewrite R1sp; unfold sp0 in *; lia|].
split; [intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; apply PM1; apply Hpres; unfold sp0 in *; lia|].
split; [rewrite Q3; exact Hgp | rewrite Q4; exact Htp]. }
change (mkCfg (mkst regs1 (Z_to_bv 64 FP_REAL) (ms_mem ms1) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs A_vfprintf regs1 (ms_mem ms1) md1).
apply (tfib_vfprintf_open B TL LAWS ocpy_of_icpt astrnlen_of_icpt ly S W regs1 (ms_mem ms1) md1 ch (sp0 - 48) s str L cval T HPRE1).
- rewrite R1sp. lia.
- rewrite R1sp, HVFS. unfold sp0 in *. lia.
- intros a Ha. unfold vf_band in Ha. rewrite R1sp, HVFS in Ha. apply PM1. apply Hpres. unfold sp0 in *. lia.
- exact Q10.
- exact Q11.
- exact Q12.
- rewrite R1sp. lia.
- lia.
- pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hdm. rewrite Hal16, Z.add_0_r in Hdm.
replace (sp0 - 48) with ((2 * (sp0 / 16) - 6) * 8) by lia. apply Z_mod_mult.
- replace (sp0 - 48) with (sp0 + -48) by lia. replace s with (bv_unsigned (getr regs 12)) by (rewrite G12; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
exact (CK 4%nat 12%Z (-48)%Z eq_refl).
- exact HL.
- exact HLhi.
- exact Hs1.
- exact Hshi.
- rewrite R1sp, HVFS. unfold sp0 in *. lia.
- exact Hsfile.
- exact Hams.
- (apply (vf_tail_xfer W mem _ sp0); [exact Hstail | intros a Hr Hb Hf; apply AV1; [exact Hr | unfold vf_band, VF_STK, ESTACK in Hb; unfold sp0 in *; lia] | lia]) || (intros a Ha; rewrite AV1; [exact (Hstail a Ha) | pose proof (Z.mod_pos_bound (s + L) 8 ltac:(lia)); lia | pose proof (Z.mod_pos_bound (s + L) 8 ltac:(lia)); unfold sp0 in *; lia]).
- intros a Hin. pose proof mc_bounds as [MB1 MB2]. rewrite AV1; [exact (Hromv a Hin) | lia | lia].
- apply (vf_str_xfer W mem); [exact HSTR|]. intros a Ha. apply AV1; [lia | unfold sp0 in *; lia].
- eapply range_addressable_agree; [|exact Hra_s]. intros z Hz. change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. apply AV1; unfold sp0 in *; lia.
- intros s' Hs'. rewrite AV1; [exact (Hhull_s s' Hs') | |];
pose proof (shadow_addr_bounds s ltac:(unfold kHighMemEnd; lia)) as [B1 B2]; pose proof (shadow_addr_bounds (s + (L + 1) - 1) ltac:(unfold kHighMemEnd; lia)) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr s) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr s) 8 ltac:(lia));
pose proof (Z.div_mod (shadow_addr (s + (L + 1) - 1)) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (shadow_addr (s + (L + 1) - 1)) 8 ltac:(lia)); unfold sp0 in *; lia.
- apply (FT stderr_fields mem); [exact WF1 | exact HFP | intros b Hb; apply AV1; lia].
- exact HFown.
- apply (VT mem); [exact Hgot | intros b Hb; apply AV1; lia].
- apply (VT mem); [exact Hcan | intros b Hb; apply AV1; lia].
- exact Hcv.
- apply (ro_img_kept _ mem (ms_mem ms1)); [intros x Hx; apply MEQ1; unfold IMG_RO_LO, IMG_RO_HI in Hx; lia | exact Hro].
- intros a Ha. exists 0. split; [|left; reflexivity]. change (shadow_of_addr SHADOW_OFF a) with (shadow_addr a). rewrite AV1.
+ apply HZ. pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)).
assert (shadow_addr FMT_open / 8 <= shadow_addr a / 8) by (apply Z.div_le_mono; [lia|]; unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (shadow_addr a / 8 <= shadow_addr (FMT_open + 21 - 1) / 8) by (apply Z.div_le_mono; [lia|]; unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
lia.
+ pose proof (shadow_addr_bounds a ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. lia.
+ pose proof (shadow_addr_bounds a ltac:(unfold kHighMemEnd; lia)) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. unfold sp0 in *. lia.
- intros sa Hsa. rewrite AV1; [rewrite (HZ sa); [discriminate|] | |].
+ pose proof (Z.div_le_mono (shadow_addr (FMT_open + 20 - 1)) (shadow_addr (FMT_open + 21 - 1)) 8 ltac:(lia) ltac:(unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia)). lia.
+ match type of Hsa with ?a <= sa < ?b => let a' := eval vm_compute in a in let b' := eval vm_compute in b in change (a <= sa < b) with (a' <= sa < b') in Hsa end. lia.
+ match type of Hsa with ?a <= sa < ?b => let a' := eval vm_compute in a in let b' := eval vm_compute in b in change (a <= sa < b) with (a' <= sa < b') in Hsa end. unfold sp0 in *. lia.
- eapply fdchan_sbm; [exact Hch | exact MF1].
- exact HAI1.
-
intros regs2 mem2 md2 HAR2 AP2 Hsbm2 A10_2 HFW2 Hfr2 Hpm2 HAI2.
rewrite R1ra. unfold vf_band in Hfr2. rewrite R1sp, HVFS in Hfr2.
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr) by (intros rr z -> Hcs; exact (AP2 z Hcs)).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - 9104 <= a < sp0 - 112) -> ~ vf_file a -> aview tfibsegs H mem2 a = aview tfibsegs H (ms_mem ms1) a)
by (intros a Hr Ha Hf; exact (Hfr2 a Hr Ha Hf)).
unfold cfg_at. change (w64 FP_RET) with (Z_to_bv 64 FP_RET).
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18]).
assert (R4sp : getr regs2 2 = w64 (sp0 - 112)) by (rewrite (K2 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q2).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 112).
{ subst E4. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R4sp. unfold w64. apply unsigned_lit_small. lia. }
assert (WS : forall j rz off, nth_error SAVEDA j = Some (rz, off) -> -80 <= off -> val_mem tfibsegs (mrestrict H mem2) (sp0 + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj Hoff80. assert (Hoff : off <= -48) by (do 5 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
apply (VT (ms_mem ms1)); [exact (CK j rz off Hj) | intros b Hb; apply AV2; [unfold sp0 in *; lia | unfold sp0 in *; lia | unfold vf_file; lia]]. }
pose proof (WS 0%nat 1%Z (-56)%Z eq_refl ltac:(lia)) as W0. replace (sp0 + -56) with (sp0 - 56) in W0 by lia.
pose proof (WS 1%nat 8%Z (-64)%Z eq_refl ltac:(lia)) as W1. replace (sp0 + -64) with (sp0 - 64) in W1 by lia.
pose proof (WS 2%nat 9%Z (-72)%Z eq_refl ltac:(lia)) as W2. replace (sp0 + -72) with (sp0 - 72) in W2 by lia.
pose proof (WS 3%nat 18%Z (-80)%Z eq_refl ltac:(lia)) as W3. replace (sp0 + -80) with (sp0 - 80) in W3 by lia.
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 FP_RET) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 112) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) (r : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18] (Z_to_bv 64 0) = getr regs r ->
off = 56 - 8 * Z.of_nat j -> Z.of_nat j < 4 ->
val_mem tfibsegs (mrestrict H mem2) (sp0 - 56 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem2) (sp0 - 112) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j r off Hnth Hoff Hj8 Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 112) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (sp0 - 112 + (56 - 8 * Z.of_nat j)) with (sp0 - 56 - 8 * Z.of_nat j) by lia. exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK4 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 0) with (sp0 - 56) by lia; exact W0].
+ apply (CK4 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 1) with (sp0 - 64) by lia; exact W1].
+ apply (CK4 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 2) with (sp0 - 72) by lia; exact W2].
+ apply (CK4 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia | replace (sp0 - 56 - 8 * Z.of_nat 3) with (sp0 - 80) by lia; exact W3].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try lia.
all: replace (spZ regs - 112) with (spZ regs + (-7) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_srealizes tfibsegs W _ _ T (fp_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI2).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem2 z) by (intros z; apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md2) mat' md2)) T); [ | exact HAI5 | ].
{ eapply (SRr_ret_at tfibsegs tbl_fp tbl_fp_ok Hwx W E4); [exact HS5 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (10%bv : bv 5) P10. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19.
rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21. rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23.
rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25. rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs2 _ jj); exact Hnth).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs2 _ 0)). rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (rewrite P1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra').
assert (SBM56 : same_but_materialized (with_vm_backing (m_vm_lazy md2) mat5 md2) (with_vm_backing (m_vm_lazy md2) mat6 md2))
by (rewrite <- (wvb_collapse (m_vm_lazy md2) mat6 mat5 md2); apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ SBM56) as MF.
assert (AV5 : forall a, aview tfibsegs H (ms_mem ms5) a = aview tfibsegs H mem2 a) by (intros a; apply aview_same; apply MEQ5).
assert (GG : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr).
{ intros z rr Hrr H1. subst rr. exact (K2 _ z eq_refl H1). }
apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat6 md2)).
+ apply (al_frame _ _ LAWS ly S W mem2 (with_vm_backing (m_vm_lazy md2) mat5 md2) (ms_mem ms5) _).
* apply (al_frame _ _ LAWS ly S W mem2 md2 mem2 _ HAR2); [intros; reflexivity | intros a Hv; exact Hv | | | | exact (AE2y.hs_kept_refl _ _)]; apply (same_but_materialized_frame md2 _ (with_vm_backing_same md2 mat5)).
* intros a Hr Hown. apply AV5.
* intros a Hv. rewrite AV5. exact Hv.
* apply MF. * apply MF. * apply MF.
* exact (AE2y.hs_kept_eq _ _ _ MEQ5).
+ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P2. apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P3, (Y 3%nat 3%bv eq_refl), (GG 3 3%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P4, (Y 4%nat 4%bv eq_refl), (GG 4 4%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact Q4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P8. exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P9. exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P18. exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P19, (Y 19%nat 19%bv eq_refl), (GG 19 19%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 19%bv 19%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P20, (Y 20%nat 20%bv eq_refl), (GG 20 20%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 20%bv 20%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P21, (Y 21%nat 21%bv eq_refl), (GG 21 21%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 21%bv 21%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P22, (Y 22%nat 22%bv eq_refl), (GG 22 22%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P23, (Y 23%nat 23%bv eq_refl), (GG 23 23%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P24, (Y 24%nat 24%bv eq_refl), (GG 24 24%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P25, (Y 25%nat 25%bv eq_refl), (GG 25 25%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P26, (Y 26%nat 26%bv eq_refl), (GG 26 26%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P27, (Y 27%nat 27%bv eq_refl), (GG 27 27%bv ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia). exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)).
+ eapply same_but_materialized_trans; [exact MF1|]. eapply same_but_materialized_trans; [exact Hsbm2|]. apply with_vm_backing_same.
+ rewrite P10, (Y 10%nat 10%bv eq_refl). exact A10_2.
+ unfold stderr_after_vfprintf in *. revert HFW2. generalize stderr_fields_after_vf. intros flds Hf.
unfold file_is in *. apply Forall_forall. intros [[o nn] v] Hin. pose proof (proj1 (Forall_forall _ _) Hf _ Hin) as Hv. cbn beta iota in Hv |- *.
apply (AF0x.val_mem_ext (mrestrict H mem2)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply AV5.
+ intros a Hr Hs Hf. rewrite AV5. rewrite AV2; [| exact Hr | unfold sp0 in *; lia | exact Hf]. apply AV1; [exact Hr | unfold sp0 in *; lia].
+ intros a Hr Hf Hp. apply (apresent_same H mem2 (ms_mem ms5) a (MEQ5 _)). apply Hpm2; [exact Hr | exact Hf|]. apply PM1. exact Hp.
+ exact HAI6.
Qed.
End t.
End g.
