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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE3f AE2p AE3i AE3h AE3m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition VP_ENTRY : Z := 0x41920.
Definition FP_REAL : Z := 0x93ad0.
Definition VP_RET2 : Z := 0x44db8.
Definition VP_RET1 : Z := 0x44248.
Definition VP_WIN : Z := 2432.
Definition VPI_STK : Z := 9200.
Definition FMT : Z := 0x147ea.
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
Definition vpA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x9df88, 8, [(0, 8%N, 0x137b28)]); (0x137b7c, 1, [(0, 1%N, 1)]); (0x9fd08, 16, [(0, 8%N, 0x96be0); (8, 8%N, 0x93ad0)])].
Lemma vpA_rodata_chk : forall ly, rodata_chk ly vpA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition SH_LO : Z := 0x7fffa8f8.  Definition SH_HI : Z := 0x7fffa900.
Definition shz : YP09.region := YP09.mkRegion None SH_LO SH_HI SH_LO SH_LO [YP09.mkChunk SH_LO (CZero (SH_HI - SH_LO))].
Definition hull_zero (rd : Z -> option Z) (x n : Z) : Prop := forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd s = Some 0.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- VP_WIN) 0 (- VP_WIN) 0 [].
Definition apr : YP09.region := YP09.mkRegion (Some 11%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0))].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (11%nat, mkAF (2^44) (2^47) 3)].
Definition regsA : list sv := Eval vm_compute in (firstn 10 sr_atoms ++ [SLit FMT] ++ skipn 11 sr_atoms).
Definition memA : smem := stkA :: apr :: shz :: img_ro_region :: map ro_region vpA_rodata.
Definition ssA : sstate := mkSS VP_ENTRY regsA memA None (mkFacts factsA [] []).
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
Lemma r_A1 : RUNTOR ssA = (eA1, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2264))) (SLit 15)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition eA2 : sstate := Eval vm_compute in fst (RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0))).
Lemma r_A2 : RUNTOR (AC eA1 BC_NE (RG eA1 13) (SLit 0)) = (eA2, RS_stopped (SR_branch BC_EQ (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (-2312))) (SLit 15)) (SLit 0))). Proof. vm_compute. reflexivity. Qed.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR (AC eA2 BC_NE (RG eA2 13) (SLit 0))).
Lemma r_A3 : RUNTOR (AC eA2 BC_NE (RG eA2 13) (SLit 0)) = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition SAVEDA : list (Z * sv) :=
[(-8, SOff 1 0); (-16, SOff 8 0); (-24, SOff 9 0); (-80, SOff 18 0); (-72, SOff 11 0); (-64, SLit FMT); (-56, SLit VP_RET1)].
Definition KEPTA : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FP_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - VP_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_is ss 10 (SLit F_STDOUT) && reg_is ss 11 (SLit FMT) && reg_is ss 12 (SOff 11 0) &&
reg_is ss 1 (SLit VP_RET2) && reg_is ss 2 (SOff 2 (-96)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (fst p) (snd p)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma br_memset_align : forall E sp0 d, bv_unsigned (ew E 2) = sp0 -> sp0 mod 16 = 0 -> d mod 16 = 8 -> 0 <= d <= 4096 -> 2 ^ 44 <= sp0 < 2 ^ 64 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SLit 40) (SOff 2 (- d))) (SLit 15))) (sv_denot E (SLit 0)) = false.
Proof.
intros E sp0 d H2 Hal Hd Hdr Hsp. rewrite branch_eq_U, !U_SAlu, !U_SLit, U_SOff, H2. cbn [zalu_raw].
rewrite (zcanon_small 40), (zcanon_small 15), (zcanon_small 0), (zcanon_small (sp0 + - d)) by lia.
assert (Hm : (sp0 + - d) mod 16 = 8).
{ replace (sp0 + - d) with (sp0 - d) by lia. rewrite Zminus_mod, Hal, Hd. reflexivity. }
assert (Hand : Z.land (Z.lor 40 (sp0 + - d)) 15 = 8).
{ rewrite Z.land_lor_distr_l. change 15 with (Z.ones 4). rewrite !Z.land_ones by lia. change (2 ^ 4) with 16. rewrite Hm. reflexivity. }
assert (Hlt : Z.lor 40 (sp0 + - d) < 2 ^ 64).
{ destruct (Z.eq_dec (Z.lor 40 (sp0 + - d)) 0) as [E0|E0]; [rewrite E0; lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg 40 (sp0 + - d)); lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; [cbv; reflexivity | apply Z.log2_lt_pow2; lia]. }
rewrite (zcanon_small (Z.lor 40 (sp0 + - d))) by (pose proof (Z.lor_nonneg 40 (sp0 + - d)); lia).
rewrite Hand. reflexivity.
Qed.
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 (SOff 34 0));
YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 8 (SOff 36 0)); YP09.mkChunk 32 (CVal 8 (SLit FMT));
YP09.mkChunk 40 (CVal 8 (SLit VP_RET1))].
Definition ss_epi : sstate := mkSS VP_RET2 sr_atoms [YP09.mkRegion (Some 2%nat) 0 96 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.
Definition shapeE (ss : sstate) : bool :=
reg_is ss 1 (SOff 32 0) && reg_is ss 8 (SOff 33 0) && reg_is ss 9 (SOff 34 0) && reg_is ss 18 (SOff 35 0) && reg_is ss 2 (SOff 2 96) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31].
Lemma shapeE_ok : shapeE epi_e = true. Proof. vm_compute. reflexivity. Qed.
Definition vpf_saved (regs : bvmap 5 word) (m : word -> option byte) (sp0 : Z) : Prop :=
val_mem tfibsegs m (sp0 - 8) 8 (bv_unsigned (getr regs 1)) /\ val_mem tfibsegs m (sp0 - 16) 8 (bv_unsigned (getr regs 8)) /\
val_mem tfibsegs m (sp0 - 24) 8 (bv_unsigned (getr regs 9)) /\ val_mem tfibsegs m (sp0 - 80) 8 (bv_unsigned (getr regs 18)) /\
val_mem tfibsegs m (sp0 - 72) 8 (sp0 + 24) /\ val_mem tfibsegs m (sp0 - 64) 8 FMT /\ val_mem tfibsegs m (sp0 - 56) 8 VP_RET1.
Lemma vpf_saved_kept : forall regs (H : word -> bool) (m m' : word -> option byte) sp0,
vpf_saved regs (mrestrict H m) sp0 -> (forall b, sp0 - 96 <= b < sp0 -> aview tfibsegs H m' b = aview tfibsegs H m b) ->
vpf_saved regs (mrestrict H m') sp0.
Proof.
intros regs H m m' sp0 (V1 & V2 & V3 & V4 & V5 & V6 & V7) Heq.
assert (T : forall a v, sp0 - 96 <= a -> a + 8 <= sp0 -> val_mem tfibsegs (mrestrict H m) a 8 v -> val_mem tfibsegs (mrestrict H m') a 8 v).
{ intros a v H1 H2 Hv. eapply val_mem_kept; [|exact Hv]. intros k Hk. apply Heq. cbn in Hk. lia. }
repeat split; (apply T; [lia | lia | assumption]).
Qed.
Section g.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem tfib_vprintf_icpt_A : forall ly S (W : world tfibsegs) regs mem md T,
ecall_pre tfibsegs B ly S W regs mem md ->
ly_stk_lo ly + VPI_STK <= spZ regs ->
(forall a, spZ regs - VPI_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
spZ regs + 32 <= 2 ^ 47 ->
getr regs 10 = w64 FMT -> getr regs 11 = w64 (spZ regs + 24) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (spZ regs + 24) 8 0 ->
ro_img (mrestrict (w_H W) mem) ->
hull_zero (aview tfibsegs (w_H W) mem) FMT 4 ->
AI tfibsegs (w_H W) (w_A W) md ->
(forall regs1 mem1 md1,
ecall_pre tfibsegs B ly S W regs1 mem1 md1 ->
spZ regs1 = spZ regs - 96 -> raZ regs1 = VP_RET2 ->
getr regs1 10 = w64 F_STDOUT -> getr regs1 11 = w64 FMT -> getr regs1 12 = w64 (spZ regs + 24) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr regs1 r = getr regs r) ->
same_but_materialized md md1 ->
(forall z : word, ~ (spZ regs - VP_WIN <= bv_unsigned z < spZ regs) -> mem1 z = mem z) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - VP_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
vpf_saved regs (mrestrict (w_H W) mem1) (spZ regs) ->
AI tfibsegs (w_H W) (w_A W) md1 ->
srealizes tfibsegs (cfg_at tfibsegs A_vfprintf regs1 mem1 md1) T) ->
srealizes tfibsegs (cfg_at tfibsegs VP_ENTRY regs mem md) T.
Proof.
intros ly S W regs mem md T HPRE Hstk Hpres Hsphi G10 G11 Harg Hro HZ HAI0 HK.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
unfold VPI_STK in *.
assert (HFMT : FMT = 83946) by reflexivity. assert (HFO : F_STDOUT = 665192) by reflexivity.
assert (KHI : kHighMemEnd = 2 ^ 47) by reflexivity.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (subst sp0; lia).
pose proof AF0x.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a (nn : nat) v, val_mem tfibsegs (mrestrict H m) a nn v ->
(forall b, a <= b < a + Z.of_nat nn -> aview tfibsegs H m' b = aview tfibsegs H m b) -> val_mem tfibsegs (mrestrict H m') a nn v).
{ intros m m' a nn v Hv Hf. apply (AF0x.val_mem_ext (mrestrict H m)); [|exact Hv]. intros j Hj. apply mbyte_of_aview. apply Hf. lia. }
unfold cfg_at. change (w64 VP_ENTRY) with (Z_to_bv 64 VP_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE11 : ew EE 11 = Z_to_bv 64 (sp0 + 24)) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (EE11u : bv_unsigned (ew EE 11) = sp0 + 24) by (rewrite EE11; apply unsigned_lit_small; lia).
assert (HZ' : forall s, SH_LO <= s < SH_HI -> aview tfibsegs H mem s = Some 0).
{ intros s Hs. apply HZ. unfold SH_LO, SH_HI in Hs.
match goal with |- ?a <= s < ?b => let a' := eval vm_compute in a in change a with a'; let b' := eval vm_compute in b in change b with b' end. lia. }
assert (HS0 : st_ok tfibsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 VP_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
apply (st_ok_regs tfibsegs EE (mkSS VP_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EE; rewrite (AE2y.Env_reg regs _ 10 10%bv eq_refl), G10; reflexivity) ] |]).
destruct Hr. }
unfold memA, EE, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [apply Hro | exact (rodata_ok B TB vpA_rodata ly S H mem EE (vpA_rodata_chk ly) (proj1 HAR))]]]].
+ unfold stkA, VP_WIN. apply (region_ok_stack tfibsegs EE _ 2 sp0 (- 2432)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresE. subst sp0. lia.
+ unfold apr, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite EE11u.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val tfibsegs EE _ (sp0 + 24) 0 8 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Harg].
+ unfold shz, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
unfold SH_LO, SH_HI. split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte H mem _ 0); [reflexivity|]. apply HZ'. unfold SH_LO, SH_HI. cbn in Hi. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, apr, shz, img_ro_region, vpA_rodata, icpt_rodata, ro_region, extent_of_region, VP_WIN, SH_LO, SH_HI, IMG_RO_LO, IMG_RO_HI.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2, EE11u.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE11u.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. repeat split; try (subst sp0; lia); try exact Hal16.
replace (sp0 + 24) with ((3 + 2 * (sp0 / 16)) * 8) by (pose proof (Z.div_mod sp0 16 ltac:(lia)) as Dm; rewrite Hal16 in Dm; lia). apply Z_mod_mult. }
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HS0 r_A1) HAI0).
intros Wa ca _ HAIa (-> & msa & mata & -> & HSa & HFa & HFra). cbn [cfg_model] in HAIa. rewrite ?wvb_wvb in HAIa |- *.
assert (MEQa : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msa z = mem z).
{ intros z Hz. apply (HFa z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- VP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold VP_WIN in *. lia. }
clear HFa HFra.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG eA1 13) (SLit 0) HSa (br_memset_align EE sp0 2264 EE2 Hal16 eq_refl ltac:(lia) ltac:(lia))) as HSa'.
change (neg_bc BC_EQ) with BC_NE in HSa'. clear HSa.
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSa' r_A2) HAIa).
intros Wb cb _ HAIb (-> & msb & matb & -> & HSb & HFb & HFrb). cbn [cfg_model] in HAIb. rewrite ?wvb_wvb in HAIb |- *.
assert (MEQb : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem msb z = mem z).
{ intros z Hz. rewrite (HFb z); [apply MEQa; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- VP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold VP_WIN in *. lia. }
clear HFb HFrb.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG eA2 13) (SLit 0) HSb (br_memset_align EE sp0 2312 EE2 Hal16 eq_refl ltac:(lia) ltac:(lia))) as HSb'.
change (neg_bc BC_EQ) with BC_NE in HSb'. clear HSb.
eapply (SRr_srealizes tfibsegs W _ _ _ (fp_phase_to W EE FP_REAL _ _ _ _ _ HSb' r_A3) HAIb).
intros W1' c1 _ HAI1 (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). cbn [cfg_model] in HAI1. rewrite ?wvb_wvb in HAI1 |- *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2432 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQb; exact Hz|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- VP_WIN) 0 sp0 _ EE2 Hin) as X0; [vm_compute; reflexivity|]. unfold VP_WIN in *. lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11]. apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'. rewrite <- Hi, Nat2Z.id in HK'.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK']. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall off v z, In (off, v) SAVEDA -> sv_denot EE v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 z).
{ intros off v z Hj Hv Hz. rewrite forallb_forall in HSV. specialize (HSV (off, v) Hj). cbn [fst snd] in HSV.
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
change 8%nat with (N.to_nat 8). apply (val_of_chunk_ok tfibsegs EE _ _ off 8 v _ Hck Hv); cbn; lia. }
set (regs1 := ms_regs ms1) in *.
assert (Q10 : getr regs1 10 = w64 F_STDOUT) by (rewrite (RD 10%bv (SLit F_STDOUT) R10); reflexivity).
assert (Q11 : getr regs1 11 = w64 FMT) by (rewrite (RD 11%bv (SLit FMT) R11); reflexivity).
assert (Q12 : getr regs1 12 = w64 (sp0 + 24)) by (rewrite (RD 12%bv (SOff 11 0) R12); cbn [sv_denot]; rewrite EE11u, Z.add_0_r; reflexivity).
assert (Q1 : getr regs1 1 = w64 VP_RET2) by (rewrite (RD 1%bv (SLit VP_RET2) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (sp0 - 96)) by (rewrite (RD 2%bv (SOff 2 (-96)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = sp0 - 96) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
assert (R1ra : raZ regs1 = VP_RET2) by (unfold raZ; rewrite Q1; unfold w64; apply unsigned_lit_small; unfold VP_RET2; lia).
pose proof (st_ok_restrict_mkst tfibsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
assert (MF1 : same_but_materialized md md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2432 <= a < sp0) -> aview tfibsegs H (ms_mem ms1) a = aview tfibsegs H mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, sp0 - 2432 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)); [| unfold TFIB_IMG_END; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold VP_WIN. lia. }
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
{ split; [exact HAR1|]. split; [rewrite Q1; apply (ret_ok_lit VP_RET2); [unfold VP_RET2; lia | reflexivity]|].
split; [rewrite R1sp; replace (sp0 - 96) with (sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite R1sp; unfold ESTACK; unfold sp0 in *; lia|]. split; [rewrite R1sp; unfold sp0 in *; lia|].
split; [intros a Ha; rewrite R1sp in Ha; unfold ESTACK in Ha; apply PM1; apply Hpres; unfold sp0 in *; lia|].
split; [rewrite Q3; exact Hgp | rewrite Q4; exact Htp]. }
change (mkCfg (mkst regs1 (Z_to_bv 64 FP_REAL) (ms_mem ms1) (seg_rom tfibsegs)) md1) with (cfg_at tfibsegs A_vfprintf regs1 (ms_mem ms1) md1).
apply (HK regs1 (ms_mem ms1) md1 HPRE1 R1sp R1ra Q10 Q11 Q12 Q3 Q4 RK MF1 ltac:(unfold VP_WIN; exact MEQ1) AV1 PM1).
-
assert (U : forall (r : bv 5), sv_denot EE (SOff (Z.to_nat (bv_unsigned r)) 0) = Z_to_bv 64 (bv_unsigned (getr regs r))).
{ intros r. cbn [sv_denot]. rewrite (EEreg (Z.to_nat (bv_unsigned r)) r) by (pose proof (bv_unsigned_in_range 5 r); lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (fun (r : bv 5) => u64_range (getr regs r)) as UR.
split; [| split; [| split; [| split; [| split; [| split]]]]].
+ replace (sp0 - 8) with (sp0 + -8) by lia. apply (CK (-8) (SOff 1 0)); [cbn; tauto | exact (U 1%bv) | apply UR].
+ replace (sp0 - 16) with (sp0 + -16) by lia. apply (CK (-16) (SOff 8 0)); [cbn; tauto | exact (U 8%bv) | apply UR].
+ replace (sp0 - 24) with (sp0 + -24) by lia. apply (CK (-24) (SOff 9 0)); [cbn; tauto | exact (U 9%bv) | apply UR].
+ replace (sp0 - 80) with (sp0 + -80) by lia. apply (CK (-80) (SOff 18 0)); [cbn; tauto | exact (U 18%bv) | apply UR].
+ replace (sp0 - 72) with (sp0 + -72) by lia. apply (CK (-72) (SOff 11 0)); [cbn; tauto | cbn [sv_denot]; rewrite EE11u, Z.add_0_r; reflexivity | lia].
+ replace (sp0 - 64) with (sp0 + -64) by lia. apply (CK (-64) (SLit FMT)); [cbn; tauto | reflexivity | rewrite HFMT; lia].
+ replace (sp0 - 56) with (sp0 + -56) by lia. apply (CK (-56) (SLit VP_RET1)); [cbn; tauto | reflexivity | unfold VP_RET1; lia].
- exact HAI1.
Qed.
Theorem tfib_vprintf_icpt_E : forall (W : world tfibsegs) (regs regs2 : bvmap 5 word) mem2 md2 (T : TSet),
2 ^ 44 <= spZ regs -> spZ regs + 32 <= 2 ^ 47 -> spZ regs mod 16 = 0 -> YK0s.ret_ok (getr regs 1) ->
getr regs2 2 = w64 (spZ regs - 96) ->
vpf_saved regs (mrestrict (w_H W) mem2) (spZ regs) ->
AI tfibsegs (w_H W) (w_A W) md2 ->
(forall regs3 mem3 md3,
(forall z, mem3 z = mem2 z) ->
getr regs3 2 = getr regs 2 -> getr regs3 1 = getr regs 1 -> getr regs3 8 = getr regs 8 -> getr regs3 9 = getr regs 9 -> getr regs3 18 = getr regs 18 ->
(forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) [3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31] ->
getr regs3 r = getr regs2 r) ->
same_but_materialized md2 md3 -> AI tfibsegs (w_H W) (w_A W) md3 ->
srealizes tfibsegs (cfg_at tfibsegs (raZ regs) regs3 mem3 md3) T) ->
srealizes tfibsegs (cfg_at tfibsegs VP_RET2 regs2 mem2 md2) T.
Proof.
intros W regs regs2 mem2 md2 T Hsp44 Hsphi Hal16 Hret R4sp (V1 & V2 & V3 & V4 & V5 & V6 & V7) HAI2 HK.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
pose proof AF0x.Hwx_tfa as Hwx. assert (HFMT : FMT = 83946) by reflexivity.
unfold cfg_at. change (w64 VP_RET2) with (Z_to_bv 64 VP_RET2).
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)]).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 96).
{ subst E4. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R4sp. unfold w64. apply unsigned_lit_small. lia. }
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 VP_RET2) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 96) by (symmetry; exact E4_2).
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold epi_chunks.
assert (CK4 : forall (j : nat) off w z, nth_error [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)] j = Some w ->
bv_unsigned w = z -> val_mem tfibsegs (mrestrict H mem2) (sp0 - 96 + off) 8 z ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem2) (sp0 - 96) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off w z Hnth Hz Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 96) off 8 _ z).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs2 _ j), (nth_error_nth _ _ _ Hnth), Z.add_0_r, <- Hz, Z_to_bv_bv_unsigned. reflexivity.
- subst z. pose proof (u64_range w). zside.
- zside.
- exact Hv. }
assert (CKL : forall off z, 0 <= z < 2 ^ 64 -> val_mem tfibsegs (mrestrict H mem2) (sp0 - 96 + off) 8 z ->
YP09.chunk_ok tfibsegs E4 (mrestrict H mem2) (sp0 - 96) (YP09.mkChunk off (CVal 8 (SLit z)))).
{ intros off z Hz Hv. eapply (chunk_ok_val tfibsegs E4 _ (sp0 - 96) off 8 _ z); [reflexivity | zside | zside | exact Hv]. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK4 0%nat 88 (getr regs 1) _ eq_refl eq_refl). replace (sp0 - 96 + 88) with (sp0 - 8) by lia. exact V1.
+ apply (CK4 1%nat 80 (getr regs 8) _ eq_refl eq_refl). replace (sp0 - 96 + 80) with (sp0 - 16) by lia. exact V2.
+ apply (CK4 2%nat 72 (getr regs 9) _ eq_refl eq_refl). replace (sp0 - 96 + 72) with (sp0 - 24) by lia. exact V3.
+ apply (CK4 3%nat 16 (getr regs 18) _ eq_refl eq_refl). replace (sp0 - 96 + 16) with (sp0 - 80) by lia. exact V4.
+ apply (CK4 4%nat 24 (Z_to_bv 64 (sp0 + 24)) (sp0 + 24) eq_refl ltac:(apply unsigned_lit_small; lia)). replace (sp0 - 96 + 24) with (sp0 - 72) by lia. exact V5.
+ apply (CKL 32 FMT ltac:(rewrite HFMT; lia)). replace (sp0 - 96 + 32) with (sp0 - 64) by lia. exact V6.
+ apply (CKL 40 VP_RET1 ltac:(unfold VP_RET1; lia)). replace (sp0 - 96 + 40) with (sp0 - 56) by lia. exact V7.
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
change (2 ^ 4) with 16. repeat split; try lia.
replace (sp0 - 96) with (sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full; exact Hal16. }
eapply (SRr_srealizes tfibsegs W _ _ T (fp_phase W E4 ss_epi epi_e _ _ _ HSe r_epi) HAI2).
intros W5' c5 _ HAI5 (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). cbn [cfg_model] in HAI5. rewrite ?wvb_wvb in HAI5 |- *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem2 z) by (intros z; apply HF5; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; lia).
eapply (SRr_srealizes tfibsegs W _
(fun W' c' => W' = W /\ exists mat', c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md2) mat' md2)) T); [ | exact HAI5 | ].
{ eapply (SRr_ret_at tfibsegs tbl_fp tbl_fp_ok Hwx W E4); [exact HS5 | reflexivity | vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
intros W6' c6 _ HAI6 (-> & mat6 & ->). cbn [cfg_model] in HAI6.
pose proof shapeE_ok as HshE. unfold shapeE in HshE.
apply andb_prop in HshE as [HshE HKE]. apply andb_prop in HshE as [HshE P2]. apply andb_prop in HshE as [HshE P18].
apply andb_prop in HshE as [HshE P9]. apply andb_prop in HshE as [P1 P8].
assert (RD : forall (r : bv 5) v, reg_is epi_e (bv_unsigned r) v = true -> getr (ms_regs ms5) r = sv_denot E4 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E4 epi_e ms5 r HS5). }
assert (X : forall j w, nth_error [getr regs 1; getr regs 8; getr regs 9; getr regs 18; Z_to_bv 64 (sp0 + 24)] j = Some w -> ew E4 (32 + j) = w)
by (intros jj w Hnth; subst E4; rewrite (ew_Ereg_extra regs2 _ jj); exact (nth_error_nth _ _ _ Hnth)).
pose proof (X 0%nat _ eq_refl) as X0. pose proof (X 1%nat _ eq_refl) as X1. pose proof (X 2%nat _ eq_refl) as X2. pose proof (X 3%nat _ eq_refl) as X3.
cbn [Nat.add] in X0, X1, X2, X3.
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs2 _ ii rr Hnth)).
assert (P1' : getr (ms_regs ms5) 1 = getr regs 1) by (rewrite (RD 1%bv (SOff 32 0) P1); cbn [sv_denot]; rewrite X0, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)) by (rewrite P1'; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hret).
apply (HK (ms_regs ms5) (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat6 md2) MEQ5).
- rewrite (RD 2%bv (SOff 2 96) P2). cbn [sv_denot]. rewrite E4_2. unfold sp0, spZ. rewrite <- (Z_to_bv_bv_unsigned 64 (getr regs 2)) at 2. f_equal. lia.
- exact P1'.
- rewrite (RD 8%bv (SOff 33 0) P8). cbn [sv_denot]. rewrite X1, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (RD 9%bv (SOff 34 0) P9). cbn [sv_denot]. rewrite X2, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite (RD 18%bv (SOff 35 0) P18). cbn [sv_denot]. rewrite X3, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- intros r i Hi Hin. rewrite forallb_forall in HKE. rewrite Hi in Hin. specialize (HKE _ Hin). cbn beta in HKE. rewrite <- Hi, Nat2Z.id in HKE.
rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HKE]. cbn [sv_denot]. rewrite (Y i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- rewrite <- (wvb_collapse (m_vm_lazy md2) mat6 mat5 md2). eapply same_but_materialized_trans; [apply with_vm_backing_same | apply with_vm_backing_same].
- exact HAI6.
Qed.
End g.
End f.
