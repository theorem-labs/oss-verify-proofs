(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE6y.v through lib/A/Rt/RtFSpChk.v -- the instruction table, the start states and the symbolic runs of the write-range check site of plugin-hostd/fuzz_command's vsprintf interceptor, kept here as the runs-and-shapes half of the walk; the shape check is the one the runs reach (the checked size stays in s1 = atom 41), and a size over 64 leaves the table at the range check 0x5a1ac, which the proof file discharges with lib/A/Rt/RtSRegion.v cmd_region_band. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The code walked, measured on the pinned fuzz_command.asan (dis ___interceptor_vsprintf): the interceptor
   0x49b70 (184 instructions), of which this walk uses the write-range check 0x49c10 .. 0x49c58, its byte path
   0x49dd8 .. 0x49e0c and the range-check call 0x49d34 .. 0x49d4c.  At 0x49c10: s1 = n (the size res + 1),
   s2 = p (the range start), a0 = res = n - 1, sp = the interceptor's sp.
     49c10  addi a1,s1,-65 ; 49c14 li a2,-64 ; 49c18 bltu a1,a2 -> 0x49d34   (taken when n > 64)
     49c1c..49c54  the inline test of the two 8-aligned shadow words of p and p + n - 1, bnez -> 0x49dd8
     49dd8..49e0c  the byte path: beqz a1 -> 0x49c58, else j 0x49d34
     49d34  mv s5,a0 ; mv a0,s2 ; mv a1,s1 ; jal 0x5a1ac (ra 0x49d44) ; mv s2,a0 ; mv a0,s5 ; beqz s2 -> 0x49c58
   __asan_region_is_poisoned 0x5a1ac is NOT in the table: the run stops at its entry and the walk uses the
   proved contract of lib/A/Rt/RtSRegion.v.  Only s2 and s5 of the callee-saved registers change. *)
Definition spc_ranges : list (Z * nat) := [(0x49b70, 184%nat)].
Definition tbl_spc : ctable := Eval vm_compute in build_ranges spc_ranges TEmpty.
Lemma tbl_spc_eq : tbl_spc = build_ranges spc_ranges TEmpty. Proof. vm_cast_no_check (eq_refl tbl_spc). Qed.
Lemma tbl_spc_ok : table_ok tfibsegs tbl_spc.
Proof. rewrite tbl_spc_eq. apply build_ranges_ok; [unfold spc_ranges; repeat constructor; cbn; discriminate | exact (table_ok_empty tfibsegs)]. Qed.
Lemma tbl_spc_probe : clookup tbl_spc 0x5a1ac = None /\ clookup tbl_spc 0x49c10 = Some 0xfbf48593.
Proof. vm_compute. split; reflexivity. Qed.
Definition SPC_ENTRY : Z := 0x49c10.
Definition SPC_END : Z := 0x49c58.
Definition SPC_RGN : Z := 0x5a1ac.
Definition SPC_CALL_RET : Z := 0x49d44.
(* The scratch window: the site itself writes nothing, and the range check writes its own 64-byte frame and
   mem_is_zero's return address 8 bytes below it (RtSRegionDef.RGN_SCR), so 72 bytes is the whole of it. *)
Definition SPC_SCR : Z := 72.
Lemma md_wvb_gen : forall m : Model, m = with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma spc_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_spc FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_spc tbl_spc_ok AF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
Lemma spc_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_spc FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1)).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_spc tbl_spc_ok AF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF _. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1 | exact HF].
Qed.
(* A run whose regions have no writable window leaves the memory as it was: this site writes nothing. *)
Lemma frame_none : forall E rs (m m' : word -> option byte),
forallb (fun t => snd t <=? snd (fst t)) (windows rs) = true -> frame_of E rs m m' -> forall z, m' z = m z.
Proof.
intros E rs m m' Hw HF z. apply HF. intros Hin.
destruct (in_wrange_windows E rs _ Hin) as (b & lo & hi & Ht & Hr).
rewrite forallb_forall in Hw. specialize (Hw _ Ht). cbn [fst snd] in Hw. apply Z.leb_le in Hw. lia.
Qed.
(* The two loads of the walk the table cannot serve by itself: the 8-aligned shadow words of p and of
   p + n - 1.  AE2y.icpt_ld8 is this lemma over tbl_icpt, which does not hold this interceptor's words. *)
Lemma spc_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_spc (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof AF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_spc_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (AE2y.val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfibsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfibsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|exact Hle].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [exact Hbs|].
apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End e.
(* The size test of this site is `addi a1,s1,-65; li a2,-64; bltu a1,a2`: n <= 64 falls through to the inline
   shadow test, n >= 65 goes to the range check. *)
Lemma br_cls64_small : forall E (pn : nat) n, ew E pn = Z_to_bv 64 n -> 1 <= n <= 64 ->
branch_taken BC_LTU (sv_denot E (SOff pn (-65))) (sv_denot E (SLit 18446744073709551552)) = false.
Proof.
intros E pn n Hn Rn. rewrite branch_ltu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
unfold zcanon, M64. change (18446744073709551552 mod 2 ^ 64) with (2 ^ 64 - 64).
replace ((n + -65) mod 2 ^ 64) with (n - 65 + 2 ^ 64).
2:{ replace (n + -65) with ((n - 65 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia. }
apply Z.ltb_ge. lia.
Qed.
Lemma br_cls64_big : forall E (pn : nat) n, ew E pn = Z_to_bv 64 n -> 65 <= n < 2 ^ 63 ->
branch_taken BC_LTU (sv_denot E (SOff pn (-65))) (sv_denot E (SLit 18446744073709551552)) = true.
Proof.
intros E pn n Hn Rn. rewrite branch_ltu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by lia.
unfold zcanon, M64. change (18446744073709551552 mod 2 ^ 64) with (2 ^ 64 - 64). rewrite Z.mod_small by lia.
apply Z.ltb_lt. lia.
Qed.
(* The start states at 0x49c10: a size of 1..64 spanning t + 1 shadow granules (the inline test and its byte
   path), and a size over 64 (the range check).  Atom 41 holds the size, 32..36 the shadow facts. *)
Definition shreg1 (t : Z) : YP09.region :=
YP09.mkRegion (Some 32%nat) SB (SB + t + 1) SB SB
((if 0 <? t then [YP09.mkChunk SB (CZero t)] else []) ++ [YP09.mkChunk (SB + t) (CVal 1 (SOff 34 0))]).
Definition aliasesS (t : Z) : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 18 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 18 (-1)) (SOff 41 0)) (SLit 3), SOff 32 t) ].
Definition factsS1 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (18%nat, mkAF 0 (2^47) 0); (41%nat, mkAF 1 64 0); (32%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0)].
Definition factsS2 : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (18%nat, mkAF 1 (2^47) 0); (41%nat, mkAF 65 (2^32 - 1) 0)].
Definition regsS : list sv := Eval vm_compute in (firstn 9 sr_atoms ++ [SOff 41 0] ++ skipn 10 sr_atoms).
Definition ssS1 (t : Z) : sstate := mkSS SPC_ENTRY regsS (shreg1 t :: map ro_region icpt_rodata) None (mkFacts factsS1 [] (aliasesS t)).
Definition ssS2 : sstate := mkSS SPC_ENTRY regsS [] None (mkFacts factsS2 [] []).
Section e2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_spc FUEL s.
Definition RUNTO (s : sstate) := sym_run_toN tfibsegs tbl_spc FUEL SPC_END s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* The range-check path: the run stops at the entry of 0x5a1ac with a0 = p, a1 = n and ra = 0x49d44; after the
   call, a0 = 0 makes `beqz s2` at 0x49d4c go to 0x49c58. *)
Definition s2_e : sstate := Eval vm_compute in fst (RUN ssS2).
Lemma r_s2 : RUN ssS2 = (s2_e, RS_stopped SR_fetch). Proof. vm_compute. reflexivity. Qed.
Lemma s2_e_shape : ss_pc s2_e = SPC_RGN /\ ss_resv s2_e = None /\ ss_mem s2_e = [] /\ ss_atoms_lt 42 s2_e = true /\
RG s2_e 1 = SLit SPC_CALL_RET /\ RG s2_e 2 = SOff 2 0 /\ RG s2_e 10 = SOff 18 0 /\ RG s2_e 11 = SOff 41 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition s2_a : sstate := Eval vm_compute in ss_after_call s2_e [] 42 SPC_CALL_RET.
Definition s2_b : sstate := Eval vm_compute in fst (RUN s2_a).
Lemma r_s2_b : RUN s2_a = (s2_b, RS_stopped (SR_branch BC_EQ (SOff 46 0) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition s2_c : sstate := Eval vm_compute in fst (RUNTO (AC s2_b BC_EQ (RG s2_b 18) (SLit 0))).
Lemma r_s2_c : RUNTO (AC s2_b BC_EQ (RG s2_b 18) (SLit 0)) = (s2_c, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t0_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 0)).
Lemma r_t0_0 : RUN (ssS1 0) = (t0_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t0_e1 : sstate := Eval vm_compute in fst (RUN (AC t0_e0 BC_GEU (RG t0_e0 11) (RG t0_e0 12))).
Lemma r_t0_1 : RUN (AC t0_e0 BC_GEU (RG t0_e0 11) (RG t0_e0 12)) = (t0_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t0_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t0_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t0_2 : RUN (set_regs_pc (set_regs_pc t0_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t0_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t0z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t0_e2 BC_EQ (RG t0_e2 14) (SLit 0))).
Lemma r_t0z_0 : RUNTO (AC t0_e2 BC_EQ (RG t0_e2 14) (SLit 0)) = (t0z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t0n_e0 : sstate := Eval vm_compute in fst (RUN (AC t0_e2 BC_NE (RG t0_e2 14) (SLit 0))).
Lemma r_t0n_0 : RUN (AC t0_e2 BC_NE (RG t0_e2 14) (SLit 0)) = (t0n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 0%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t0n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t0n_e0 BC_EQ (RG t0n_e0 11) (SLit 0))).
Lemma r_t0n_1 : RUNTO (AC t0n_e0 BC_EQ (RG t0n_e0 11) (SLit 0)) = (t0n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t1_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 1)).
Lemma r_t1_0 : RUN (ssS1 1) = (t1_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t1_e1 : sstate := Eval vm_compute in fst (RUN (AC t1_e0 BC_GEU (RG t1_e0 11) (RG t1_e0 12))).
Lemma r_t1_1 : RUN (AC t1_e0 BC_GEU (RG t1_e0 11) (RG t1_e0 12)) = (t1_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t1_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t1_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t1_2 : RUN (set_regs_pc (set_regs_pc t1_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t1_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t1z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t1_e2 BC_EQ (RG t1_e2 14) (SLit 0))).
Lemma r_t1z_0 : RUNTO (AC t1_e2 BC_EQ (RG t1_e2 14) (SLit 0)) = (t1z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t1n_e0 : sstate := Eval vm_compute in fst (RUN (AC t1_e2 BC_NE (RG t1_e2 14) (SLit 0))).
Lemma r_t1n_0 : RUN (AC t1_e2 BC_NE (RG t1_e2 14) (SLit 0)) = (t1n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 1%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t1n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t1n_e0 BC_EQ (RG t1n_e0 11) (SLit 0))).
Lemma r_t1n_1 : RUNTO (AC t1n_e0 BC_EQ (RG t1n_e0 11) (SLit 0)) = (t1n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t2_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 2)).
Lemma r_t2_0 : RUN (ssS1 2) = (t2_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t2_e1 : sstate := Eval vm_compute in fst (RUN (AC t2_e0 BC_GEU (RG t2_e0 11) (RG t2_e0 12))).
Lemma r_t2_1 : RUN (AC t2_e0 BC_GEU (RG t2_e0 11) (RG t2_e0 12)) = (t2_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t2_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t2_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t2_2 : RUN (set_regs_pc (set_regs_pc t2_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t2_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t2z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t2_e2 BC_EQ (RG t2_e2 14) (SLit 0))).
Lemma r_t2z_0 : RUNTO (AC t2_e2 BC_EQ (RG t2_e2 14) (SLit 0)) = (t2z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t2n_e0 : sstate := Eval vm_compute in fst (RUN (AC t2_e2 BC_NE (RG t2_e2 14) (SLit 0))).
Lemma r_t2n_0 : RUN (AC t2_e2 BC_NE (RG t2_e2 14) (SLit 0)) = (t2n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 2%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t2n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t2n_e0 BC_EQ (RG t2n_e0 11) (SLit 0))).
Lemma r_t2n_1 : RUNTO (AC t2n_e0 BC_EQ (RG t2n_e0 11) (SLit 0)) = (t2n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t3_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 3)).
Lemma r_t3_0 : RUN (ssS1 3) = (t3_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t3_e1 : sstate := Eval vm_compute in fst (RUN (AC t3_e0 BC_GEU (RG t3_e0 11) (RG t3_e0 12))).
Lemma r_t3_1 : RUN (AC t3_e0 BC_GEU (RG t3_e0 11) (RG t3_e0 12)) = (t3_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t3_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t3_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t3_2 : RUN (set_regs_pc (set_regs_pc t3_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t3_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t3z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t3_e2 BC_EQ (RG t3_e2 14) (SLit 0))).
Lemma r_t3z_0 : RUNTO (AC t3_e2 BC_EQ (RG t3_e2 14) (SLit 0)) = (t3z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t3n_e0 : sstate := Eval vm_compute in fst (RUN (AC t3_e2 BC_NE (RG t3_e2 14) (SLit 0))).
Lemma r_t3n_0 : RUN (AC t3_e2 BC_NE (RG t3_e2 14) (SLit 0)) = (t3n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 3%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t3n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t3n_e0 BC_EQ (RG t3n_e0 11) (SLit 0))).
Lemma r_t3n_1 : RUNTO (AC t3n_e0 BC_EQ (RG t3n_e0 11) (SLit 0)) = (t3n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t4_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 4)).
Lemma r_t4_0 : RUN (ssS1 4) = (t4_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t4_e1 : sstate := Eval vm_compute in fst (RUN (AC t4_e0 BC_GEU (RG t4_e0 11) (RG t4_e0 12))).
Lemma r_t4_1 : RUN (AC t4_e0 BC_GEU (RG t4_e0 11) (RG t4_e0 12)) = (t4_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t4_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t4_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t4_2 : RUN (set_regs_pc (set_regs_pc t4_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t4_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t4z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t4_e2 BC_EQ (RG t4_e2 14) (SLit 0))).
Lemma r_t4z_0 : RUNTO (AC t4_e2 BC_EQ (RG t4_e2 14) (SLit 0)) = (t4z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t4n_e0 : sstate := Eval vm_compute in fst (RUN (AC t4_e2 BC_NE (RG t4_e2 14) (SLit 0))).
Lemma r_t4n_0 : RUN (AC t4_e2 BC_NE (RG t4_e2 14) (SLit 0)) = (t4n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 4%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t4n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t4n_e0 BC_EQ (RG t4n_e0 11) (SLit 0))).
Lemma r_t4n_1 : RUNTO (AC t4n_e0 BC_EQ (RG t4n_e0 11) (SLit 0)) = (t4n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t5_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 5)).
Lemma r_t5_0 : RUN (ssS1 5) = (t5_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t5_e1 : sstate := Eval vm_compute in fst (RUN (AC t5_e0 BC_GEU (RG t5_e0 11) (RG t5_e0 12))).
Lemma r_t5_1 : RUN (AC t5_e0 BC_GEU (RG t5_e0 11) (RG t5_e0 12)) = (t5_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t5_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t5_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t5_2 : RUN (set_regs_pc (set_regs_pc t5_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t5_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t5z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t5_e2 BC_EQ (RG t5_e2 14) (SLit 0))).
Lemma r_t5z_0 : RUNTO (AC t5_e2 BC_EQ (RG t5_e2 14) (SLit 0)) = (t5z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t5n_e0 : sstate := Eval vm_compute in fst (RUN (AC t5_e2 BC_NE (RG t5_e2 14) (SLit 0))).
Lemma r_t5n_0 : RUN (AC t5_e2 BC_NE (RG t5_e2 14) (SLit 0)) = (t5n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 5%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t5n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t5n_e0 BC_EQ (RG t5n_e0 11) (SLit 0))).
Lemma r_t5n_1 : RUNTO (AC t5n_e0 BC_EQ (RG t5n_e0 11) (SLit 0)) = (t5n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t6_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 6)).
Lemma r_t6_0 : RUN (ssS1 6) = (t6_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t6_e1 : sstate := Eval vm_compute in fst (RUN (AC t6_e0 BC_GEU (RG t6_e0 11) (RG t6_e0 12))).
Lemma r_t6_1 : RUN (AC t6_e0 BC_GEU (RG t6_e0 11) (RG t6_e0 12)) = (t6_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t6_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t6_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t6_2 : RUN (set_regs_pc (set_regs_pc t6_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t6_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t6z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t6_e2 BC_EQ (RG t6_e2 14) (SLit 0))).
Lemma r_t6z_0 : RUNTO (AC t6_e2 BC_EQ (RG t6_e2 14) (SLit 0)) = (t6z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t6n_e0 : sstate := Eval vm_compute in fst (RUN (AC t6_e2 BC_NE (RG t6_e2 14) (SLit 0))).
Lemma r_t6n_0 : RUN (AC t6_e2 BC_NE (RG t6_e2 14) (SLit 0)) = (t6n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 6%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t6n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t6n_e0 BC_EQ (RG t6n_e0 11) (SLit 0))).
Lemma r_t6n_1 : RUNTO (AC t6n_e0 BC_EQ (RG t6n_e0 11) (SLit 0)) = (t6n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t7_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 7)).
Lemma r_t7_0 : RUN (ssS1 7) = (t7_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t7_e1 : sstate := Eval vm_compute in fst (RUN (AC t7_e0 BC_GEU (RG t7_e0 11) (RG t7_e0 12))).
Lemma r_t7_1 : RUN (AC t7_e0 BC_GEU (RG t7_e0 11) (RG t7_e0 12)) = (t7_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t7_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t7_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t7_2 : RUN (set_regs_pc (set_regs_pc t7_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t7_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t7z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t7_e2 BC_EQ (RG t7_e2 14) (SLit 0))).
Lemma r_t7z_0 : RUNTO (AC t7_e2 BC_EQ (RG t7_e2 14) (SLit 0)) = (t7z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t7n_e0 : sstate := Eval vm_compute in fst (RUN (AC t7_e2 BC_NE (RG t7_e2 14) (SLit 0))).
Lemma r_t7n_0 : RUN (AC t7_e2 BC_NE (RG t7_e2 14) (SLit 0)) = (t7n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 7%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t7n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t7n_e0 BC_EQ (RG t7n_e0 11) (SLit 0))).
Lemma r_t7n_1 : RUNTO (AC t7n_e0 BC_EQ (RG t7n_e0 11) (SLit 0)) = (t7n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t8_e0 : sstate := Eval vm_compute in fst (RUN (ssS1 8)).
Lemma r_t8_0 : RUN (ssS1 8) = (t8_e0, RS_stopped (SR_branch BC_LTU (SOff 41 (-65)) (SLit 18446744073709551552))). Proof. vm_compute. reflexivity. Qed.
Definition t8_e1 : sstate := Eval vm_compute in fst (RUN (AC t8_e0 BC_GEU (RG t8_e0 11) (RG t8_e0 12))).
Lemma r_t8_1 : RUN (AC t8_e0 BC_GEU (RG t8_e0 11) (RG t8_e0 12)) = (t8_e1, RS_stopped (SR_addr (SAlu ALU_ADD (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) (SLit 0)))). Proof. vm_compute. reflexivity. Qed.
Definition t8_e2 : sstate := Eval vm_compute in fst (RUN (set_regs_pc (set_regs_pc t8_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50)).
Lemma r_t8_2 : RUN (set_regs_pc (set_regs_pc t8_e1 [((14%bv : bv 5), SOff 35 0)] 0x49c4c) [((15%bv : bv 5), SOff 36 0)] 0x49c50) = (t8_e2, RS_stopped (SR_branch BC_NE (SAlu ALU_OR (SOff 36 0) (SOff 35 0)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t8z_e0 : sstate := Eval vm_compute in fst (RUNTO (AC t8_e2 BC_EQ (RG t8_e2 14) (SLit 0))).
Lemma r_t8z_0 : RUNTO (AC t8_e2 BC_EQ (RG t8_e2 14) (SLit 0)) = (t8z_e0, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition t8n_e0 : sstate := Eval vm_compute in fst (RUN (AC t8_e2 BC_NE (RG t8_e2 14) (SLit 0))).
Lemma r_t8n_0 : RUN (AC t8_e2 BC_NE (RG t8_e2 14) (SLit 0)) = (t8n_e0, RS_stopped (SR_branch BC_EQ (qc_flag 8%nat 18 41 34) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition t8n_e1 : sstate := Eval vm_compute in fst (RUNTO (AC t8n_e0 BC_EQ (RG t8n_e0 11) (SLit 0))).
Lemma r_t8n_1 : RUNTO (AC t8n_e0 BC_EQ (RG t8n_e0 11) (SLit 0)) = (t8n_e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
(* Measured on every end state below: the walk leaves a0 and every
   callee-saved register but s2 (18) and s5 (21) at its entry value, and s1 (9) at the size atom 41. *)
Definition KEPT : list Z := [2; 3; 4; 8; 19; 20; 22; 23; 24; 25; 26; 27].
Definition shapeR (ss : sstate) : bool :=
(ss_pc ss =? SPC_END) && reg_is ss 10 (SOff 10 0) && reg_is ss 9 (SOff 41 0) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT.
Definition nowin (rs : smem) : bool := forallb (fun t => snd t <=? snd (fst t)) (windows rs).
End e2.
