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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE1j YF8r YE04 YE0v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO38.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF62 YE0z YE10 YE0y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition MC_ENTRY {imgk : img} : Z := (0x420d8 + D_2c4).
Definition MC_REAL {imgk : img} : Z := (0x9b390 + D_10ec).
Definition MC_RSTOP {imgk : img} : Z := (0x420d4 + D_2c4).
Definition MC_XENT {imgk : img} : Z := (0x42f10 + D_2c4).
Definition MC_YEND {imgk : img} : Z := (0x42fb0 + D_2c4).
Definition MC_CALLRET {imgk : img} : Z := (0x42fbc + D_2c4).
Definition MC_RETC {imgk : img} : Z := (0x43848 + D_2c4).
Definition MC_FRAME : Z := 2240.
Definition MC_SCR : Z := 2312.
Lemma mc_phase {imgk : img} : forall (W : world tfxsegs) E ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> sym_runN tfxsegs tbl_mc FUEL ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfxsegs tbl_mc tbl_mc_ok YF8r.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|]. split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Lemma mc_phase_to {imgk : img} : forall (W : world tfxsegs) E stop ss ss' st ms md,
st_ok tfxsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfxsegs tbl_mc FUEL stop ss = (ss', st) ->
SRr tfxsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfxsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfxsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfxsegs tbl_mc tbl_mc_ok YF8r.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. img_apply SRr_ret. split; [img_refl|]. exists ms1, mat1. split; [img_refl|]. split; [img_try (img_exact HS1)|]. split; [img_try (img_exact HF) | img_try (img_exact HFr)].
Qed.
Definition mcA_rodata {imgk : img} : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [((0xa2150 + D_10f0), 8, [(0, 8%N, (0x13bce8 + D_10c0))]); ((0x13bde0 + D_10c0), 8, [(0, 8%N, 0x101010101010101)]); ((0xa3ea8 + D_10f0), 8, [(0, 8%N, (0x9b390 + D_10ec))])].
Lemma mcA_rodata_chk {imgk : img} : forall ly, rodata_chk ly mcA_rodata = true.
Proof. intros ly. img_case; vm_compute. all: img_refl. Qed.
Definition stkA : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (- MC_FRAME) 0 (- MC_FRAME) 0 [].
Definition factsA : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 0 (2^47) 0); (12%nat, mkAF 0 (2^32 - 1) 0)].
Definition ssA {imgk : img} : sstate := mkSS MC_ENTRY sr_atoms (stkA :: map ro_region mcA_rodata) None (mkFacts factsA [] []).
Definition RUNTOX {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_mc FUEL MC_XENT s.
Definition eA {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOX ssA)))).
Lemma r_A {imgk : img} : RUNTOX ssA = (eA, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition RUN {imgk : img} (s : sstate) := sym_runN tfxsegs tbl_mc FUEL s.
Definition RUNTOR {imgk : img} (s : sstate) := sym_run_toN tfxsegs tbl_mc FUEL MC_RSTOP s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YQ09.add_cond s (mkAC c a b).
Definition regs0 {imgk : img} : list sv := ltac:(img_eval_last (fun imgk : img => ((firstn 21 sr_atoms ++ [SLit (0x9b390 + D_10ec)] ++ skipn 22 sr_atoms)))).
Definition facts0 : list (nat * afact) := [(20%nat, mkAF 0 (2^47) 0); (18%nat, mkAF 0 (2^47) 0); (9%nat, mkAF 0 0 0)].
Definition ss0 {imgk : img} : sstate := mkSS MC_XENT regs0 [] None (mkFacts facts0 [] []).
Definition z0_e0 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (ss0))))).
Lemma r_z0_0 {imgk : img} : RUN (ss0) = (z0_e0, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 20 0) (SLit (-1))) (SOff 9 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition z0_e1 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC z0_e0 BC_GEU (RG z0_e0 11) (RG z0_e0 9)))))).
Lemma r_z0_1 {imgk : img} : RUN (AC z0_e0 BC_GEU (RG z0_e0 11) (RG z0_e0 9)) = (z0_e1, RS_stopped (SR_branch BC_GEU (SLit 18446744073709551551) (SOff 9 (-65)))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition z0_e2 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC z0_e1 BC_GEU (RG z0_e1 11) (RG z0_e1 25)))))).
Lemma r_z0_2 {imgk : img} : RUN (AC z0_e1 BC_GEU (RG z0_e1 11) (RG z0_e1 25)) = (z0_e2, RS_stopped (SR_branch BC_NE (SOff 9 0) (SLit 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition z0_e3 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN (AC z0_e2 BC_EQ (RG z0_e2 9) (SLit 0)))))).
Lemma r_z0_3 {imgk : img} : RUN (AC z0_e2 BC_EQ (RG z0_e2 9) (SLit 0)) = (z0_e3, RS_stopped (SR_branch BC_LTU (SAlu ALU_XOR (SOff 18 0) (SLit (-1))) (SOff 9 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition z0_e4 {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR (AC z0_e3 BC_GEU (RG z0_e3 11) (RG z0_e3 9)))))).
Lemma r_z0_4 {imgk : img} : RUNTOR (AC z0_e3 BC_GEU (RG z0_e3 11) (RG z0_e3 9)) = (z0_e4, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition regsC {imgk : img} : list sv := regs0.
Definition ssC {imgk : img} : sstate := mkSS MC_YEND regsC [] None (mkFacts [] [] []).
Definition eC {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUNTOR ssC)))).
Lemma r_C {imgk : img} : RUNTOR ssC = (eC, RS_running). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition epi_chunks {imgk : img} : list YQ0b.chunk :=
[YQ0b.mkChunk 2232 (CVal 8 (SOff 32 0));
YQ0b.mkChunk 2224 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 2216 (CVal 8 (SOff 34 0));
YQ0b.mkChunk 2208 (CVal 8 (SOff 35 0));
YQ0b.mkChunk 2176 (CVal 8 (SOff 36 0));
YQ0b.mkChunk 2168 (CVal 8 (SOff 37 0));
YQ0b.mkChunk 2160 (CVal 8 (SOff 38 0));
YQ0b.mkChunk 2152 (CVal 8 (SOff 39 0));
YQ0b.mkChunk 2144 (CVal 8 (SOff 40 0));
YQ0b.mkChunk 2136 (CVal 8 (SOff 41 0));
YQ0b.mkChunk 2128 (CVal 8 (SOff 42 0));
YQ0b.mkChunk 2120 (CVal 8 (SOff 43 0));
YQ0b.mkChunk 2112 (CVal 8 (SOff 44 0));
YQ0b.mkChunk 2104 (CVal 8 (SOff 45 0));
YQ0b.mkChunk 2096 (CVal 8 (SOff 46 0));
YQ0b.mkChunk 2088 (CVal 8 (SOff 47 0));
YQ0b.mkChunk 2184 (CVal 8 (SLit (276552 + D_2c4)))].
Definition ss_epi {imgk : img} : sstate := mkSS MC_CALLRET sr_atoms [YQ0b.mkRegion (Some 2%nat) 0 2240 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e {imgk : img} : sstate := ltac:(img_eval_last (fun imgk : img => (fst (RUN ss_epi)))).
Lemma r_epi {imgk : img} : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition chunk_is (off : Z) (v : sv) (c : YQ0b.chunk) : bool :=
(YQ0b.c_off c =? off) && match YQ0b.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YQ0b.r_chunks r) | [] => false end.
Definition SAVEDA {imgk : img} : list (sv * Z) := [(SOff 1 0, -8); (SOff 8 0, -16); (SOff 9 0, -24); (SOff 18 0, -32); (SLit (276552 + D_2c4), -56); (SOff 12 0, -64); (SOff 11 0, -72); (SOff 10 0, -80); (SOff 19 0, -88); (SOff 20 0, -96); (SOff 21 0, -104); (SOff 22 0, -112); (SOff 23 0, -120); (SOff 24 0, -128); (SOff 25 0, -136); (SOff 26 0, -144); (SOff 27 0, -152)].
Definition KEPTA : list Z := [3; 4; 22; 25; 26; 27].
Definition shapeA {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? MC_XENT) &&
match ss_mem ss with r :: _ => obase_eqb (YQ0b.r_base r) (Some 2%nat) && (YQ0b.r_wlo r =? - MC_FRAME) && (YQ0b.r_whi r =? 0) | [] => false end &&
reg_is ss 20 (SOff 10 0) && reg_is ss 18 (SOff 11 0) && reg_is ss 9 (SOff 12 0) && reg_is ss 21 (SLit MC_REAL) && reg_is ss 19 (SLit MC_RETC) &&
reg_is ss 2 (SOff 2 (-2240)) && reg_is ss 10 (SOff 2 (-40)) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunk ss (snd p) (fst p)) SAVEDA.
Lemma shapeA_ok {imgk : img} : shapeA eA = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Definition shapeC {imgk : img} (ss : sstate) : bool :=
(ss_pc ss =? MC_RSTOP) && reg_is ss 10 (SOff 10 0) && reg_is ss 11 (SOff 18 0) && reg_is ss 12 (SOff 9 0) && reg_is ss 1 (SLit MC_CALLRET) &&
forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27].
Lemma shapeC_ok {imgk : img} : shapeC eC = true. Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YQ0b.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YQ0b.c_off YQ0b.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. (subst; cbv beta). img_refl.
Qed.
Lemma munrestrict_mrestrict_same : forall (H : word -> bool) (m : word -> option byte) z, munrestrict H m (mrestrict H m) z = m z.
Proof. intros H m z. unfold munrestrict, mrestrict. destruct (H z); img_refl. Qed.
Lemma br_cls65_zero : forall E (pn : nat), ew E pn = Z_to_bv 64 0 ->
branch_taken BC_GEU (sv_denot E (SLit 18446744073709551551)) (sv_denot E (SOff pn (-65))) = true.
Proof.
intros E pn Hn. rewrite branch_geu_U, U_SLit, U_SOff, Hn, unsigned_lit_small by img_lia.
unfold zcanon, M64. img_change (18446744073709551551 mod 2 ^ 64) with (2 ^ 64 - 65). img_change ((0 + -65) mod 2 ^ 64) with (2 ^ 64 - 65).
rewrite Z.ltb_irrefl. img_refl.
Qed.
Lemma br_atom_zero : forall E (pn : nat), ew E pn = Z_to_bv 64 0 ->
branch_taken BC_NE (sv_denot E (SOff pn 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E pn Hn. unfold branch_taken. cbn [sv_denot]. rewrite Hn, unsigned_lit_small by img_lia. img_refl.
Qed.
Section f. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Lemma mc_tail : forall ly S (W : world tfxsegs) regs mem md (regsR : bvmap 5 word) (memR : word -> option byte) mdR x y n,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok tfxsegs W regs mem x n -> src_ok tfxsegs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) y n) ->
AR tfxsegs B ly S W memR mdR -> same_but_materialized md mdR ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - MC_SCR <= a < spZ regs) -> aview tfxsegs (w_H W) memR a = aview tfxsegs (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memR a) ->
getr regsR 10 = w64 x -> getr regsR 11 = w64 y -> getr regsR 12 = w64 n ->
getr regsR 1 = w64 MC_CALLRET -> getr regsR 2 = w64 (spZ regs - 2240) -> getr regsR 19 = w64 MC_RETC ->
getr regsR 3 = getr regs 3 -> getr regsR 4 = getr regs 4 ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 56) 8 (276552 + D_2c4) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 64) 8 (bv_unsigned (getr regs 12)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 72) 8 (bv_unsigned (getr regs 11)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 80) 8 (bv_unsigned (getr regs 10)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 88) 8 (bv_unsigned (getr regs 19)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 96) 8 (bv_unsigned (getr regs 20)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 104) 8 (bv_unsigned (getr regs 21)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 112) 8 (bv_unsigned (getr regs 22)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 120) 8 (bv_unsigned (getr regs 23)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 128) 8 (bv_unsigned (getr regs 24)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 136) 8 (bv_unsigned (getr regs 25)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 144) 8 (bv_unsigned (getr regs 26)) ->
val_mem tfxsegs (mrestrict (w_H W) memR) (spZ regs - 152) 8 (bv_unsigned (getr regs 27)) ->
SRr tfxsegs W (mkCfg (mkst regsR (Z_to_bv 64 MC_RSTOP) memR (seg_rom tfxsegs)) mdR)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem (x + i) = aview tfxsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md regsR memR mdR x y n HPRE Hslo2 Hpres2 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy
HARR HsbmR AVR PMR G10 G11 G12 G1 G2 G19 G3 G4 V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13 V14 V15 V16.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp).
pose proof YF8r.Hwx_tfa as Hwx. unfold src_ok in Hsx, Hsy. unfold ESTACK, MC_SCR in *.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
set (sp0 := spZ regs) in *. assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by img_lia.
set (H := w_H W) in *.
assert (Hamr : x + n <= 2 ^ 47 - 1 /\ y + n <= 2 ^ 47 - 1) by (img_try (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamx, Hamy; img_lia)).
assert (RRsp : spZ regsR = sp0 - 2240) by (img_try (unfold spZ; rewrite G2; unfold w64; img_apply unsigned_lit_small; img_lia)).
assert (HPRER : ecall_pre tfxsegs B ly S W regsR memR mdR).
{ split; [img_try (img_exact HARR)|]. split; [img_try (rewrite G1; img_apply (ret_ok_lit MC_CALLRET); [unfold MC_CALLRET; img_lia | img_refl])|].
split; [img_try (rewrite RRsp; replace (sp0 - 2240) with (sp0 + (-140) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16)|].
split; [img_try (rewrite RRsp; unfold ESTACK; unfold sp0 in *; img_lia)|]. split; [img_try (rewrite RRsp; unfold sp0 in *; img_lia)|].
split; [img_try (intros a Ha; rewrite RRsp in Ha; unfold ESTACK in Ha; img_apply PMR; img_apply Hpres2; unfold sp0 in *; img_lia)|].
split; [img_try (rewrite G3; img_exact Hgp) | img_try (rewrite G4; img_exact Htp)]. }
pose proof (memcmp_icpt_contract B LAWS TB ly S W regsR memR mdR x y n HPRER G10 G11 G12 Hn Hx Hxn Hy Hyn) as HR.
unfold cfg_at in HR. img_change (w64 (270548 + D_2c4)) with (Z_to_bv 64 MC_RSTOP) in HR.
eapply SRr_bind.
{ img_apply HR; clear HR.
- intros a Ha. rewrite RRsp. unfold ESTACK. split; [| img_try (pose proof (Hbx a Ha); unfold sp0 in *; img_lia)].
fold H. rewrite AVR; [img_try (img_exact (proj1 (Hsx a Ha))) | img_lia | img_try (pose proof (Hbx a Ha); unfold sp0 in *; img_lia)].
- intros a Ha. rewrite RRsp. unfold ESTACK. split; [| img_try (pose proof (Hby a Ha); unfold sp0 in *; img_lia)].
fold H. rewrite AVR; [img_try (img_exact (proj1 (Hsy a Ha))) | img_lia | img_try (pose proof (Hby a Ha); unfold sp0 in *; img_lia)].
- img_exact Hamx.
- img_exact Hamy.
- eapply range_addressable_agree; [|img_try (img_exact Hrax)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. fold H. img_apply AVR; unfold sp0 in *; img_lia.
- intros Hn0 s' Hs. fold H. rewrite AVR; [img_try (img_exact (Hhx Hn0 s' Hs)) | |];
pose proof (shadow_addr_bounds x ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (x + n - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia.
- eapply range_addressable_agree; [|img_try (img_exact Hray)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. fold H. img_apply AVR; unfold sp0 in *; img_lia.
- intros Hn0 s' Hs. fold H. rewrite AVR; [img_try (img_exact (Hhy Hn0 s' Hs)) | |];
pose proof (shadow_addr_bounds y ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (y + n - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr y) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (y + n - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (y + n - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & model' & v & -> & HAR2 & AP2 & Hsbm & A10 & HIFFR & Hfr2 & Hpm2).
unfold raZ. rewrite G1. unfold w64 at 1. rewrite unsigned_lit_small by (img_try (unfold MC_CALLRET; img_lia)). rewrite RRsp in Hfr2. unfold ESTACK in Hfr2.
unfold cfg_at. img_change (w64 MC_CALLRET) with (Z_to_bv 64 MC_CALLRET).
assert (K2 : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regsR rr) by (img_try (intros rr z -> Hcs; img_exact (AP2 z Hcs))).
assert (AV2' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 - 4096 <= a < sp0 - 2240) -> aview tfxsegs H mem2 a = aview tfxsegs H memR a) by (img_try (intros a Hr Ha; img_exact (Hfr2 a Hr Ha))).
assert (VM : forall a (nn : nat) (vv : Z), val_mem tfxsegs (mrestrict H memR) a nn vv -> sp0 - 160 <= a -> a + Z.of_nat nn <= sp0 -> val_mem tfxsegs (mrestrict H mem2) a nn vv).
{ intros a nn vv Hv Hlo Hhi. img_apply (YF8r.val_mem_ext (mrestrict H memR)); [|img_try (img_exact Hv)]. intros j Hj. img_apply mbyte_of_aview. img_apply AV2'; img_lia. }
assert (HIFF : v = w64 0 <-> forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem (x + i) = aview tfxsegs (w_H W) mem (y + i)).
{ rewrite HIFFR. fold H. split; intros HE i Hi; specialize (HE i Hi).
+ rewrite <- (AVR (x + i)), <- (AVR (y + i)); [img_try (img_exact HE) | img_lia | img_try (pose proof (Hby (y + i) ltac:(img_lia)); unfold sp0 in *; img_lia) | img_lia | img_try (pose proof (Hbx (x + i) ltac:(img_lia)); unfold sp0 in *; img_lia)].
+ rewrite (AVR (x + i)), (AVR (y + i)); [img_try (img_exact HE) | img_lia | img_try (pose proof (Hby (y + i) ltac:(img_lia)); unfold sp0 in *; img_lia) | img_lia | img_try (pose proof (Hbx (x + i) ltac:(img_lia)); unfold sp0 in *; img_lia)]. }
clear HIFFR.
set (E4 := Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]).
assert (R2sp : getr regs2 2 = w64 (sp0 - 2240)) by (img_try (rewrite (K2 2%bv 2 ltac:(img_apply bv_eq; img_refl)) by (unfold acallee_saved; img_lia); img_exact G2)).
assert (E4_2 : bv_unsigned (ew E4 2) = sp0 - 2240).
{ (subst E4; cbv beta). rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), R2sp. unfold w64. img_apply unsigned_lit_small. img_lia. }
assert (HSe : st_ok tfxsegs E4 ss_epi (restrict H (mkst regs2 (Z_to_bv 64 MC_CALLRET) mem2 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. img_apply (entry_st_ok_full tfxsegs);
img_change (Ereg regs2 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27]) with E4.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [|img_try (img_apply Forall_nil)].
unfold region_ok. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks].
replace (base_val E4 (Some 2%nat)) with (sp0 - 2240) by (img_try (symmetry; img_exact E4_2)).
split; [img_lia|]. split; [img_lia|]. split; [img_try (intros o Ho; exfalso; img_lia)|].
unfold epi_chunks.
assert (CK : forall (j : nat) (rq : bv 5) off, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rq -> Z.of_nat j < 16 ->
val_mem tfxsegs (mrestrict H mem2) (sp0 - 2240 + off) 8 (bv_unsigned (getr regs rq)) ->
YQ0b.chunk_ok tfxsegs E4 (mrestrict H mem2) (sp0 - 2240) (YQ0b.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j rq off Hnth Hj8 Hv. eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 2240) off 8 _ (bv_unsigned (getr regs rq))).
- cbn [sv_denot]. (subst E4; cbv beta). rewrite (ew_Ereg_extra regs2 _ j), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. img_refl.
- pose proof (u64_range (getr regs rq)). zside.
- zside.
- img_exact Hv. }
repeat img_apply Forall_cons; try img_apply Forall_nil.
+ img_apply (CK 0%nat 1%bv (2232)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2232) with (sp0 - 8) by img_lia; img_exact (VM _ _ _ V0 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 1%nat 8%bv (2224)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2224) with (sp0 - 16) by img_lia; img_exact (VM _ _ _ V1 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 2%nat 9%bv (2216)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2216) with (sp0 - 24) by img_lia; img_exact (VM _ _ _ V2 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 3%nat 18%bv (2208)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2208) with (sp0 - 32) by img_lia; img_exact (VM _ _ _ V3 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 4%nat 12%bv (2176)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2176) with (sp0 - 64) by img_lia; img_exact (VM _ _ _ V5 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 5%nat 11%bv (2168)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2168) with (sp0 - 72) by img_lia; img_exact (VM _ _ _ V6 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 6%nat 10%bv (2160)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2160) with (sp0 - 80) by img_lia; img_exact (VM _ _ _ V7 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 7%nat 19%bv (2152)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2152) with (sp0 - 88) by img_lia; img_exact (VM _ _ _ V8 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 8%nat 20%bv (2144)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2144) with (sp0 - 96) by img_lia; img_exact (VM _ _ _ V9 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 9%nat 21%bv (2136)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2136) with (sp0 - 104) by img_lia; img_exact (VM _ _ _ V10 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 10%nat 22%bv (2128)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2128) with (sp0 - 112) by img_lia; img_exact (VM _ _ _ V11 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 11%nat 23%bv (2120)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2120) with (sp0 - 120) by img_lia; img_exact (VM _ _ _ V12 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 12%nat 24%bv (2112)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2112) with (sp0 - 128) by img_lia; img_exact (VM _ _ _ V13 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 13%nat 25%bv (2104)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2104) with (sp0 - 136) by img_lia; img_exact (VM _ _ _ V14 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 14%nat 26%bv (2096)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2096) with (sp0 - 144) by img_lia; img_exact (VM _ _ _ V15 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ img_apply (CK 15%nat 27%bv (2088)); [img_refl | img_try (cbn; img_lia) | img_try (replace (sp0 - 2240 + 2088) with (sp0 - 152) by img_lia; img_exact (VM _ _ _ V16 ltac:(img_lia) ltac:(cbn; img_lia)))].
+ eapply (chunk_ok_val tfxsegs E4 _ (sp0 - 2240) 2184 8 (SLit (276552 + D_2c4)) (276552 + D_2c4)); [img_refl | img_try (zside) | img_try (zside) | img_try (replace (sp0 - 2240 + 2184) with (sp0 - 56) by img_lia; img_exact (VM _ _ _ V4 ltac:(img_lia) ltac:(cbn; img_lia)))].
- img_apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E4_2.
img_change (2 ^ 4) with 16. unfold sp0 in *. repeat split; try img_lia.
all: replace (spZ regs - 2240) with (spZ regs + (-140) * 16) by img_lia; rewrite Z_mod_plus_full; img_exact Hal16. }
eapply SRr_bind; [img_try (img_apply (mc_phase W E4 ss_epi epi_e _ _ _ HSe r_epi))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & HFr4). rewrite ?wvb_wvb in *.
eapply (SRr_ret_at tfxsegs tbl_mc tbl_mc_ok Hwx W E4); [img_try (img_exact HS4) | img_refl | img_try ((img_case; vm_compute); img_refl) |].
intros mat'. rewrite wvb_wvb.
assert (MEQ4 : forall z, ms_mem ms4 z = mem2 z) by (img_try (intros z; img_apply HF4; intros Hin; destruct (in_wrange_windows E4 _ _ Hin) as (b & lo & hi & Ht & Hw); cbn in Ht; destruct Ht as [Hq|[]]; injection Hq as <- <- <-; cbn [base_val] in Hw; img_lia)).
rreg HS4 (1%bv : bv 5) Q1. rreg HS4 (2%bv : bv 5) Q2. rreg HS4 (10%bv : bv 5) Q10. rreg HS4 (3%bv : bv 5) Q3. rreg HS4 (4%bv : bv 5) Q4.
rreg HS4 (8%bv : bv 5) Q8. rreg HS4 (9%bv : bv 5) Q9. rreg HS4 (18%bv : bv 5) Q18. rreg HS4 (19%bv : bv 5) Q19.
rreg HS4 (20%bv : bv 5) Q20. rreg HS4 (21%bv : bv 5) Q21. rreg HS4 (22%bv : bv 5) Q22. rreg HS4 (23%bv : bv 5) Q23.
rreg HS4 (24%bv : bv 5) Q24. rreg HS4 (25%bv : bv 5) Q25. rreg HS4 (26%bv : bv 5) Q26. rreg HS4 (27%bv : bv 5) Q27.
assert (X : forall j rr, nth j [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 12; getr regs 11; getr regs 10; getr regs 19; getr regs 20; getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26; getr regs 27] (Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + j) = getr regs rr)
by (img_try (intros jj rr Hnth; (subst E4; cbv beta); rewrite (ew_Ereg_extra regs2 _ jj); img_exact Hnth)).
assert (Y : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs2 rr) by (img_try (intros ii rr Hnth; (subst E4; cbv beta); img_exact (ew_Ereg_nat regs2 _ ii rr Hnth))).
assert (X32 : ew E4 32 = getr regs 1) by (img_try ((subst E4; cbv beta); img_exact (ew_Ereg_extra regs2 _ 0))). rewrite X32 in Q1.
replace (v_jalr (getr (ms_regs ms4) 1) 0) with (w64 (raZ regs)) by (img_try (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; img_exact Hra')).
split; [img_refl|]. exists (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy model') mat' model'), v.
pose proof (same_but_materialized_frame model' _ (with_vm_backing_same model' mat')) as MF.
assert (AV4 : forall a, aview tfxsegs H (ms_mem ms4) a = aview tfxsegs H mem2 a) by (img_try (intros a; img_apply aview_same; img_apply MEQ4)).
split; [img_refl|].
split; [|img_try (split; [|split; [|split; [|split; [|split]]]])].
+   img_apply (al_frame _ _ LAWS ly S W mem2 model' (ms_mem ms4) _ HAR2).
* intros a Hr Hown. img_apply AV4.
* intros a Hv. rewrite AV4. img_exact Hv.
* img_apply MF. * img_apply MF. * img_apply MF.
* img_exact (YE0v.hs_kept_eq _ _ _ MEQ4).
+
intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q2. img_apply bv_eq. rewrite Z_to_bv_unsigned, E4_2. unfold sp0, spZ, bv_wrap. img_change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by img_lia. img_lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q3, (Y 3%nat 3%bv eq_refl). rewrite (K2 3%bv 3 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q4, (Y 4%nat 4%bv eq_refl). rewrite (K2 4%bv 4 ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact G4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q8. img_exact (X 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q9. img_exact (X 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by img_lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q18. img_exact (X 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q19. img_exact (X 7%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q20. img_exact (X 8%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q21. img_exact (X 9%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q22. img_exact (X 10%nat 22%bv eq_refl).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q23. img_exact (X 11%nat 23%bv eq_refl).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q24. img_exact (X 12%nat 24%bv eq_refl).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q25. img_exact (X 13%nat 25%bv eq_refl).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q26. img_exact (X 14%nat 26%bv eq_refl).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (img_try (img_apply bv_eq; img_refl)). rewrite Q27. img_exact (X 15%nat 27%bv eq_refl).
+ eapply same_but_materialized_trans; [img_try (img_exact HsbmR)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm) | img_try (img_apply with_vm_backing_same)].
+ rewrite Q10, (Y 10%nat 10%bv eq_refl). img_exact A10.
+ img_exact HIFF.
+ intros a Hr Hs. rewrite AV4. rewrite AV2' by (img_try (unfold sp0 in *; img_lia)). img_apply AVR; [img_try (img_exact Hr) | img_try (unfold sp0 in *; img_lia)].
+ intros a Hp. img_apply (apresent_same H mem2 (ms_mem ms4) a (MEQ4 _)). img_apply Hpm2. img_apply PMR. img_exact Hp.
Qed.
End f.
Section g. Context {imgk : img}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfxsegs B.
Hypothesis TB : TfxSyms B.
Variables (ly : alayout) (S : astate) (W : world tfxsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x y n : Z).
Hypothesis HPRE : ecall_pre tfxsegs B ly S W regs mem md.
Hypothesis Hslo2 : ly_stk_lo ly + 2 * ESTACK <= spZ regs.
Hypothesis Hpres2 : forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 y.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hx : 0 <= x.
Hypothesis Hxn : x + n <= 2 ^ 63.
Hypothesis Hy : 0 <= y.
Hypothesis Hyn : y + n <= 2 ^ 63.
Hypothesis Hsx : src_ok tfxsegs W regs mem x n.
Hypothesis Hsy : src_ok tfxsegs W regs mem y n.
Hypothesis Hbx : forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs).
Hypothesis Hby : forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs).
Hypothesis Hamx : amem_range x n.
Hypothesis Hamy : amem_range y n.
Hypothesis Hrax : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n.
Hypothesis Hhx : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n.
Hypothesis Hray : range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF y n.
Hypothesis Hhy : 0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) y n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Theorem bc_icpt_srr : SRr tfxsegs W (cfg_at tfxsegs MC_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem (x + i) = aview tfxsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
pose proof HPRE as (HAR & Hra' & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof (am_layout B ly S _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
assert (Hsp : 2 ^ 44 <= sp0 <= 2 ^ 47) by (img_try ((subst sp0; cbv beta); img_lia)).
assert (Hamr : x + n <= 2 ^ 47 - 1 /\ y + n <= 2 ^ 47 - 1) by (img_try (pose proof Hamx as X1; pose proof Hamy as Y1; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in X1, Y1; img_lia)).
pose proof YF8r.Hwx_tfa as Hwx.
assert (VT : forall (m m' : word -> option byte) a v, val_mem tfxsegs (mrestrict H m) a 8 v ->
(forall b, a <= b < a + 8 -> aview tfxsegs H m' b = aview tfxsegs H m b) -> val_mem tfxsegs (mrestrict H m') a 8 v).
{ intros m m' a v Hv Hf. img_apply (YF8r.val_mem_ext (mrestrict H m)); [|img_try (img_exact Hv)]. intros j Hj. img_apply mbyte_of_aview. img_apply Hf. img_lia. }
unfold cfg_at. img_change (w64 MC_ENTRY) with (Z_to_bv 64 MC_ENTRY).
set (EE := YE0v.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (EE2 : bv_unsigned (ew EE 2) = sp0) by (img_try (rewrite (EEreg 2%nat 2%bv eq_refl); img_refl)).
assert (EE10 : ew EE 10 = Z_to_bv 64 x) by (img_try (rewrite (EEreg 10%nat 10%bv eq_refl); img_exact G10)).
assert (EE11 : ew EE 11 = Z_to_bv 64 y) by (img_try (rewrite (EEreg 11%nat 11%bv eq_refl); img_exact G11)).
assert (EE12 : ew EE 12 = Z_to_bv 64 n) by (img_try (rewrite (EEreg 12%nat 12%bv eq_refl); img_exact G12)).
assert (HS0 : st_ok tfxsegs EE ssA (restrict H (mkst regs (Z_to_bv 64 MC_ENTRY) mem (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- img_apply regs_ok_Ereg.
- img_case; vm_compute. all: img_refl.
- img_apply Forall_cons; [| img_try (img_exact (rodata_ok B TB mcA_rodata ly S H mem EE (mcA_rodata_chk ly) (proj1 HAR)))].
unfold stkA, MC_FRAME. img_apply (region_ok_stack tfxsegs EE _ 2 sp0 (- 2240)); [img_try (img_exact EE2) | img_lia | img_lia |].
intros a Ha. img_apply YF8r.apresent_writable; [img_try (unfold YF8r.TFX_IMG_END, kHighMemBeg in *; img_lia)|]. img_apply HpresE. (subst sp0; cbv beta). img_lia.
- img_apply pairwise_disjoint_of_extents. unfold stkA, mcA_rodata, icpt_rodata, ro_region, extent_of_region, MC_FRAME.
cbn [map app fst snd YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; img_lia.
- split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, EE12, !unsigned_lit_small by img_lia.
img_change (2 ^ 4) with 16. img_change (2 ^ 0) with 1. repeat split; first [img_exact Hal16 | img_apply Z.mod_1_r | (subst sp0; cbv beta); img_lia]. }
eapply SRr_bind; [img_try (img_apply (mc_phase_to W EE MC_XENT _ _ _ _ _ HS0 r_A))|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - 2240 <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. img_apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MC_FRAME) 0 sp0 _ EE2 Hin) as X0; [img_try ((img_case; vm_compute); img_refl)|]. unfold MC_FRAME in *. img_lia. }
clear HF1 HFr1.
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R19]. apply andb_prop in Hsh as [Hsh R21].
apply andb_prop in Hsh as [Hsh R9]. apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [img_try (discriminate)|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EE v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr (ms_regs ms1) r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK. rewrite Hi in Hin. specialize (HK _ Hin). cbn beta in HK. rewrite <- Hi, Nat2Z.id in HK.
rewrite (RD r (SOff i 0)); [| img_try (rewrite <- Hi; img_exact HK)]. cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
assert (CK : forall j v off, nth_error SAVEDA j = Some (v, off) -> forall z, sv_denot EE v = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
val_mem tfxsegs (mrestrict H (ms_mem ms1)) (sp0 + off) 8 z).
{ intros j v off Hj z Hz Hrg. rewrite forallb_forall in HSV. specialize (HSV (v, off) (nth_error_In _ _ Hj)). cbn [fst snd] in HSV.
unfold has_chunk in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc). apply chunk_is_sound in Hc. (subst c; cbv beta).
pose proof (st_ok_mem_ok tfxsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck. rewrite EE2 in Hck.
img_apply (val_of_chunk_ok tfxsegs EE _ _ off 8 v _ Hck Hz); zside. }
set (regs1 := ms_regs ms1) in *.
assert (Q20 : getr regs1 20 = w64 x) by (img_try (rewrite (RD 20%bv (SOff 10 0) R20); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q18 : getr regs1 18 = w64 y) by (img_try (rewrite (RD 18%bv (SOff 11 0) R18); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q9 : getr regs1 9 = w64 n) by (img_try (rewrite (RD 9%bv (SOff 12 0) R9); cbn [sv_denot]; rewrite EE12, unsigned_lit_small by img_lia; rewrite Z.add_0_r; img_refl)).
assert (Q21 : getr regs1 21 = w64 MC_REAL) by (img_try (rewrite (RD 21%bv (SLit MC_REAL) R21); img_refl)).
assert (Q19 : getr regs1 19 = w64 MC_RETC) by (img_try (rewrite (RD 19%bv (SLit MC_RETC) R19); img_refl)).
assert (Q2 : getr regs1 2 = w64 (sp0 - 2240)) by (img_try (rewrite (RD 2%bv (SOff 2 (-2240)) R2); cbn [sv_denot]; rewrite EE2; img_refl)).
assert (Q3 : getr regs1 3 = getr regs 3) by (img_try (img_exact (RK 3%bv 3%nat eq_refl ltac:(cbn; img_lia)))).
assert (Q4 : getr regs1 4 = getr regs 4) by (img_try (img_exact (RK 4%bv 4%nat eq_refl ltac:(cbn; img_lia)))).
assert (R1sp : spZ regs1 = sp0 - 2240) by (img_try (unfold spZ; rewrite Q2; unfold w64; img_apply unsigned_lit_small; img_lia)).
pose proof (st_ok_restrict_mkst tfxsegs H EE _ _ HS1 eq_refl) as Hshape. rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md).
assert (MF1 : same_but_materialized md md1) by (img_try ((subst md1; cbv beta); img_apply with_vm_backing_same)).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 <= a < sp0) -> aview tfxsegs H (ms_mem ms1) a = aview tfxsegs H mem a).
{ intros a Hr Ha. img_apply aview_same. img_apply MEQ1. rewrite unsigned_lit_small by img_lia. img_exact Ha. }
assert (PRS1 : forall a, sp0 - 2240 <= a < sp0 -> apresent H (ms_mem ms1) a).
{ intros a Ha. img_apply (st_ok_window_apresent H EE eA ms1 0 r0 a HS1 ltac:(img_try (rewrite Hmem; img_refl))); [| img_try (unfold TFX_IMG_END; img_lia)].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold MC_FRAME. img_lia. }
assert (PM1 : forall a, apresent H mem a -> apresent H (ms_mem ms1) a).
{ intros a Hp. pose proof Hp as [Hh [b Hb]].
rewrite (YE0v.apresent_mod _ (ms_mem ms1) a). rewrite (YE0v.apresent_mod _ mem a) in Hp.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2240)) as [L1|L1]; [img_try (img_apply (apresent_same H mem (ms_mem ms1) a'); [img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia | img_exact Hp])|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [img_try (img_apply PRS1; img_lia)|].
img_apply (apresent_same H mem (ms_mem ms1) a'); [img_try (img_apply MEQ1; rewrite unsigned_lit_small by img_lia; img_lia) | img_try (img_exact Hp)]. }
assert (HAR1 : AR tfxsegs B ly S W (ms_mem ms1) md1).
{ img_apply (al_frame _ _ LAWS ly S W mem md (ms_mem ms1) _ HAR).
+ intros a Hr Hown. img_apply AV1; [img_try (img_exact Hr)|]. intros Hs. img_exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(img_try (unfold sp0 in *; img_lia)) Hown).
+ intros a Hv. rewrite (YE0v.aview_mod _ (ms_mem ms1) a). rewrite (YE0v.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (img_try (img_apply Z.mod_pos_bound; img_lia)). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (sp0 - 2240)) as [L1|L1]; [img_try (rewrite AV1 by img_lia; img_exact Hv)|].
destruct (Z_lt_le_dec a' sp0) as [L3|L3]; [| img_try (rewrite AV1 by img_lia; img_exact Hv)].
img_apply aview_some_of_apresent. img_apply PRS1. img_lia.
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_apply (same_but_materialized_frame md _ MF1).
+ img_exact (YE0v.hs_kept_win _ _ _ _ _ _ _ _ MEQ1 HpresE ltac:(img_try (unfold sp0 in *; img_lia)) ltac:(img_lia)). }
destruct (Z.eq_dec n 0) as [Hn0|Hn0].
-
set (E0 := YE0v.Env regs1 []).
assert (E0reg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E0 i = getr regs1 r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (E0_20 : ew E0 20 = Z_to_bv 64 x) by (img_try (rewrite (E0reg 20%nat 20%bv eq_refl); img_exact Q20)).
assert (E0_18 : ew E0 18 = Z_to_bv 64 y) by (img_try (rewrite (E0reg 18%nat 18%bv eq_refl); img_exact Q18)).
assert (E0_9 : ew E0 9 = Z_to_bv 64 0) by (img_try (rewrite (E0reg 9%nat 9%bv eq_refl), Q9, Hn0; img_refl)).
assert (HZ0 : st_ok tfxsegs E0 ss0 (restrict H (mkst regs1 (Z_to_bv 64 MC_XENT) (ms_mem ms1) (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ss0.
img_apply (st_ok_regs tfxsegs E0 (mkSS MC_XENT sr_atoms [] None (mkFacts facts0 [] [])) _ regs0).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold E0; rewrite (YE0v.Env_reg regs1 _ 21 21%bv eq_refl), Q21; img_refl) ] |]).
destruct Hr. }
unfold E0, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs1 (map (Z_to_bv 64) [])) with E0.
+ img_apply regs_ok_Ereg.
+ img_case; vm_compute. all: img_refl.
+ img_apply Forall_nil.
+ cbn. img_exact I.
+ split; [|img_try (split; img_exact I)]. cbn [f_atoms atoms_ok facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E0_20, E0_18, E0_9, !unsigned_lit_small by img_lia. img_change (2 ^ 0) with 1. repeat split; first [img_apply Z.mod_1_r | img_lia]. }
assert (MZ0 : forall z, ms_mem (mkst regs1 (Z_to_bv 64 MC_XENT) (ms_mem ms1) (seg_rom tfxsegs)) z = ms_mem ms1 z) by (img_try (intros z; img_refl)).
eapply SRr_bind; [img_try (img_apply (mc_phase W E0 _ _ _ _ _ HZ0 r_z0_0))|].
cbv beta. intros W01 c01 _ (-> & mz1 & mt1 & -> & HZ1 & HFz1 & _). rewrite ?wvb_wvb in *.
assert (MZ1 : forall z, ms_mem mz1 z = ms_mem ms1 z) by (img_try (intros z; rewrite (HFz1 z); [img_try (img_apply MZ0) | img_try (intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht)])).
clear HFz1 HZ0.
pose proof (st_ok_add_cond_neg tfxsegs E0 _ _ BC_LTU (RG z0_e0 11) (RG z0_e0 9) HZ1 (br_ovf_false E0 20 9 x 0 E0_20 E0_9 ltac:(img_lia) ltac:(img_lia))) as HZ1'.
img_change (neg_bc BC_LTU) with BC_GEU in HZ1'. clear HZ1.
eapply SRr_bind; [img_try (img_apply (mc_phase W E0 _ _ _ _ _ HZ1' r_z0_1))|].
cbv beta. intros W02 c02 _ (-> & mz2 & mt2 & -> & HZ2 & HFz2 & _). rewrite ?wvb_wvb in *.
assert (MZ2 : forall z, ms_mem mz2 z = ms_mem ms1 z) by (img_try (intros z; rewrite (HFz2 z); [img_try (img_apply MZ1) | img_try (intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht)])).
clear HFz2 HZ1'.
pose proof (st_ok_add_cond tfxsegs E0 _ _ BC_GEU (RG z0_e1 11) (RG z0_e1 25) HZ2 (br_cls65_zero E0 9 E0_9)) as HZ2'. clear HZ2.
eapply SRr_bind; [img_try (img_apply (mc_phase W E0 _ _ _ _ _ HZ2' r_z0_2))|].
cbv beta. intros W03 c03 _ (-> & mz3 & mt3 & -> & HZ3 & HFz3 & _). rewrite ?wvb_wvb in *.
assert (MZ3 : forall z, ms_mem mz3 z = ms_mem ms1 z) by (img_try (intros z; rewrite (HFz3 z); [img_try (img_apply MZ2) | img_try (intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht)])).
clear HFz3 HZ2'.
pose proof (st_ok_add_cond_neg tfxsegs E0 _ _ BC_NE (RG z0_e2 9) (SLit 0) HZ3 (br_atom_zero E0 9 E0_9)) as HZ3'.
img_change (neg_bc BC_NE) with BC_EQ in HZ3'. clear HZ3.
eapply SRr_bind; [img_try (img_apply (mc_phase W E0 _ _ _ _ _ HZ3' r_z0_3))|].
cbv beta. intros W04 c04 _ (-> & mz4 & mt4 & -> & HZ4 & HFz4 & _). rewrite ?wvb_wvb in *.
assert (MZ4 : forall z, ms_mem mz4 z = ms_mem ms1 z) by (img_try (intros z; rewrite (HFz4 z); [img_try (img_apply MZ3) | img_try (intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht)])).
clear HFz4 HZ3'.
pose proof (st_ok_add_cond_neg tfxsegs E0 _ _ BC_LTU (RG z0_e3 11) (RG z0_e3 9) HZ4 (br_ovf_false E0 18 9 y 0 E0_18 E0_9 ltac:(img_lia) ltac:(img_lia))) as HZ4'.
img_change (neg_bc BC_LTU) with BC_GEU in HZ4'. clear HZ4.
eapply SRr_bind; [img_try (img_apply (mc_phase_to W E0 MC_RSTOP _ _ _ _ _ HZ4' r_z0_4))|].
cbv beta. intros W05 c05 _ (-> & mz5 & mt5 & -> & HZ5 & HFz5 & _). rewrite ?wvb_wvb in *.
assert (MZ5 : forall z, ms_mem mz5 z = ms_mem ms1 z) by (img_try (intros z; rewrite (HFz5 z); [img_try (img_apply MZ4) | img_try (intros Hin; destruct (in_wrange_windows E0 _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht)])).
clear HFz5.
assert (SH0 : (ss_pc z0_e4 =? MC_RSTOP) && reg_is z0_e4 10 (SOff 20 0) && reg_is z0_e4 11 (SOff 18 0) && reg_is z0_e4 12 (SOff 9 0) && reg_is z0_e4 1 (SLit MC_CALLRET) &&
reg_is z0_e4 2 (SOff 2 0) && reg_is z0_e4 19 (SOff 19 0) && reg_is z0_e4 3 (SOff 3 0) && reg_is z0_e4 4 (SOff 4 0) = true) by (img_try ((img_case; vm_compute); img_refl)).
apply andb_prop in SH0 as [SH0 Z4]. apply andb_prop in SH0 as [SH0 Z3]. apply andb_prop in SH0 as [SH0 Z19]. apply andb_prop in SH0 as [SH0 Z2].
apply andb_prop in SH0 as [SH0 Z1]. apply andb_prop in SH0 as [SH0 Z12]. apply andb_prop in SH0 as [SH0 Z11]. apply andb_prop in SH0 as [Zpc Z10]. apply Z.eqb_eq in Zpc.
assert (RDZ : forall (r : bv 5) v, reg_is z0_e4 (bv_unsigned r) v = true -> getr (ms_regs mz5) r = sv_denot E0 v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H E0 z0_e4 mz5 r HZ5). }
pose proof (st_ok_restrict_mkst tfxsegs H E0 _ _ HZ5 eq_refl) as Zshape. rewrite Zpc in Zshape. rewrite Zshape.
assert (AVT : forall b, sp0 - 160 <= b < sp0 -> aview tfxsegs H (ms_mem mz5) b = aview tfxsegs H (ms_mem ms1) b) by (img_try (intros b Hb; img_apply aview_same; img_apply MZ5)).
img_apply (mc_tail B LAWS TB ly S W regs mem md (ms_regs mz5) (ms_mem mz5) (with_vm_backing (m_vm_lazy md1) mt5 md1) x y n HPRE Hslo2 Hpres2 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
+ img_apply (al_frame _ _ LAWS ly S W (ms_mem ms1) md1 (ms_mem mz5) _ HAR1); [img_try (intros a _ _; img_apply aview_same; img_apply MZ5) | img_try (intros a Hv; erewrite aview_same; [img_exact Hv | img_apply MZ5]) | | | | img_try (img_exact (YE0v.hs_kept_eq _ _ _ MZ5))];
img_apply (same_but_materialized_frame md1 _ (with_vm_backing_same md1 mt5)).
+ eapply same_but_materialized_trans; [img_try (img_exact MF1) | img_try (img_apply with_vm_backing_same)].
+ intros a Hr Ha. unfold MC_SCR in Ha. erewrite aview_same; [| img_try (img_apply MZ5)]. img_apply AV1; [img_try (img_exact Hr) | img_lia].
+ intros a Hp. img_apply (apresent_same H (ms_mem ms1) (ms_mem mz5) a (MZ5 _)). img_apply PM1. img_exact Hp.
+ rewrite (RDZ 10%bv (SOff 20 0) Z10). cbn [sv_denot]. rewrite E0_20, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
+ rewrite (RDZ 11%bv (SOff 18 0) Z11). cbn [sv_denot]. rewrite E0_18, unsigned_lit_small by img_lia. rewrite Z.add_0_r. img_refl.
+ rewrite (RDZ 12%bv (SOff 9 0) Z12). cbn [sv_denot]. rewrite E0_9, unsigned_lit_small by img_lia. rewrite Hn0. img_refl.
+ rewrite (RDZ 1%bv (SLit MC_CALLRET) Z1). img_refl.
+ rewrite (RDZ 2%bv (SOff 2 0) Z2). cbn [sv_denot]. rewrite (E0reg 2%nat 2%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact Q2.
+ rewrite (RDZ 19%bv (SOff 19 0) Z19). cbn [sv_denot]. rewrite (E0reg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact Q19.
+ rewrite (RDZ 3%bv (SOff 3 0) Z3). cbn [sv_denot]. rewrite (E0reg 3%nat 3%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact Q3.
+ rewrite (RDZ 4%bv (SOff 4 0) Z4). cbn [sv_denot]. rewrite (E0reg 4%nat 4%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact Q4.
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 0%nat (SOff 1 0) (-8) eq_refl (bv_unsigned (getr regs 1)) ltac:(cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 1)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 1%nat (SOff 8 0) (-16) eq_refl (bv_unsigned (getr regs 8)) ltac:(cbn [sv_denot]; rewrite (EEreg 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 8)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 2%nat (SOff 9 0) (-24) eq_refl (bv_unsigned (getr regs 9)) ltac:(cbn [sv_denot]; rewrite (EEreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 9)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 3%nat (SOff 18 0) (-32) eq_refl (bv_unsigned (getr regs 18)) ltac:(cbn [sv_denot]; rewrite (EEreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 18)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 4%nat (SLit (276552 + D_2c4)) (-56) eq_refl (276552 + D_2c4) eq_refl ltac:(img_lia))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 5%nat (SOff 12 0) (-64) eq_refl (bv_unsigned (getr regs 12)) ltac:(cbn [sv_denot]; rewrite (EEreg 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 12)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 6%nat (SOff 11 0) (-72) eq_refl (bv_unsigned (getr regs 11)) ltac:(cbn [sv_denot]; rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 11)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 7%nat (SOff 10 0) (-80) eq_refl (bv_unsigned (getr regs 10)) ltac:(cbn [sv_denot]; rewrite (EEreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 10)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 8%nat (SOff 19 0) (-88) eq_refl (bv_unsigned (getr regs 19)) ltac:(cbn [sv_denot]; rewrite (EEreg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 19)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 9%nat (SOff 20 0) (-96) eq_refl (bv_unsigned (getr regs 20)) ltac:(cbn [sv_denot]; rewrite (EEreg 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 20)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 10%nat (SOff 21 0) (-104) eq_refl (bv_unsigned (getr regs 21)) ltac:(cbn [sv_denot]; rewrite (EEreg 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 21)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 11%nat (SOff 22 0) (-112) eq_refl (bv_unsigned (getr regs 22)) ltac:(cbn [sv_denot]; rewrite (EEreg 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 22)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 12%nat (SOff 23 0) (-120) eq_refl (bv_unsigned (getr regs 23)) ltac:(cbn [sv_denot]; rewrite (EEreg 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 23)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 13%nat (SOff 24 0) (-128) eq_refl (bv_unsigned (getr regs 24)) ltac:(cbn [sv_denot]; rewrite (EEreg 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 24)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 14%nat (SOff 25 0) (-136) eq_refl (bv_unsigned (getr regs 25)) ltac:(cbn [sv_denot]; rewrite (EEreg 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 25)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 15%nat (SOff 26 0) (-144) eq_refl (bv_unsigned (getr regs 26)) ltac:(cbn [sv_denot]; rewrite (EEreg 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 26)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 16%nat (SOff 27 0) (-152) eq_refl (bv_unsigned (getr regs 27)) ltac:(cbn [sv_denot]; rewrite (EEreg 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 27)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
-
assert (Hn1 : 1 <= n < 2 ^ 32) by img_lia.
eapply SRr_bind.
{ img_apply (mcmpx_check_srr B LAWS TB ly S W regs1 (ms_mem ms1) md1 x n HAR1).
- rewrite R1sp. replace (sp0 - 2240) with (sp0 + (-140) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal16.
- rewrite R1sp. unfold YE0z.RC_SCR. unfold sp0 in *. img_lia.
- rewrite R1sp. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R1sp in Ha. unfold YE0z.RC_SCR in Ha. img_apply PM1. img_apply HpresE. unfold sp0 in *. img_lia.
- img_exact Q9.
- img_exact Q20.
- img_exact Hn1.
- img_exact Hx.
- img_exact Hxn.
- img_exact Hamx.
- eapply range_addressable_agree; [|img_try (img_exact Hrax)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. img_apply AV1; unfold sp0 in *; img_lia.
- intros s' Hs. rewrite AV1; [img_try (img_exact (Hhx ltac:(img_lia) s' Hs)) | |];
pose proof (shadow_addr_bounds x ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (x + n - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & K2 & Hsbm2 & (A10_2 & A9_2 & A25_2) & Hfr2 & Hpm2).
rewrite R1sp in Hfr2. unfold YE0z.RC_SCR in Hfr2.
assert (KK2 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 22 -> z <> 25 -> z <> 26 -> getr regs2 rr = getr regs1 rr).
{ intros z rr -> H1 H2 H3 H5 H6. img_exact (K2 z H1 H2 H3 H5 H6). }
assert (R2sp : spZ regs2 = sp0 - 2240) by (img_try (unfold spZ; rewrite (KK2 2 2%bv ltac:(img_apply bv_eq; img_refl)) by (unfold acallee_saved; img_lia); img_exact R1sp)).
assert (AV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 - 72 <= a < sp0 - 2240) -> aview tfxsegs H mem2 a = aview tfxsegs H (ms_mem ms1) a) by (img_try (intros a Hr Ha; img_exact (Hfr2 a Hr Ha))).
unfold cfg_at. eapply SRr_bind.
{ img_apply (mcmpy_check_srr B LAWS TB ly S W regs2 mem2 md2 y n HAR2).
- rewrite R2sp. replace (sp0 - 2240) with (sp0 + (-140) * 16) by img_lia. rewrite Z_mod_plus_full. img_exact Hal16.
- rewrite R2sp. unfold YE10.RC_SCR. unfold sp0 in *. img_lia.
- rewrite R2sp. unfold sp0 in *. img_lia.
- intros a Ha. rewrite R2sp in Ha. unfold YE10.RC_SCR in Ha. img_apply Hpm2. img_apply PM1. img_apply HpresE. unfold sp0 in *. img_lia.
- img_exact A9_2.
- rewrite (KK2 18 18%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q18.
- img_exact A25_2.
- img_exact Hn1.
- img_exact Hy.
- img_exact Hyn.
- img_exact Hamy.
- eapply range_addressable_agree; [|img_try (img_exact Hray)]. intros z Hz. img_change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z).
pose proof (shadow_addr_bounds z ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]. unfold kLowMemEnd, kHighShadowEnd in B1, B2. rewrite AV2 by (img_try (unfold sp0 in *; img_lia)). img_apply AV1; unfold sp0 in *; img_lia.
- intros s' Hs. rewrite AV2, AV1; [img_try (img_exact (Hhy ltac:(img_lia) s' Hs)) | | | |];
pose proof (shadow_addr_bounds y ltac:(img_try (unfold kHighMemEnd; img_lia))) as [B1 B2]; pose proof (shadow_addr_bounds (y + n - 1) ltac:(img_try (unfold kHighMemEnd; img_lia))) as [T1 T2];
unfold kLowMemEnd, kHighShadowEnd in B1, B2, T1, T2;
pose proof (Z.div_mod (shadow_addr y) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr y) 8 ltac:(img_lia));
pose proof (Z.div_mod (shadow_addr (y + n - 1)) 8 ltac:(img_lia)); pose proof (Z.mod_pos_bound (shadow_addr (y + n - 1)) 8 ltac:(img_lia)); unfold sp0 in *; img_lia. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HAR3 & K3 & Hsbm3 & (A10_3 & A9_3) & Hfr3 & Hpm3).
rewrite R2sp in Hfr3. unfold YE10.RC_SCR in Hfr3.
assert (KK3 : forall z (rr : bv 5), rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 22 -> z <> 25 -> getr regs3 rr = getr regs2 rr).
{ intros z rr -> H1 H2 H3 H5. img_exact (K3 z H1 H2 H3 H5). }
assert (AV3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 2240 - 72 <= a < sp0 - 2240) -> aview tfxsegs H mem3 a = aview tfxsegs H mem2 a) by (img_try (intros a Hr Ha; img_exact (Hfr3 a Hr Ha))).
set (EC := YE0v.Env regs3 []).
assert (ECreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EC i = getr regs3 r) by (img_try (intros; img_apply YE0v.Env_reg; assumption)).
assert (Q21_3 : getr regs3 21 = w64 MC_REAL).
{ rewrite (KK3 21 21%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (KK2 21 21%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q21. }
assert (HC0 : st_ok tfxsegs EC ssC (restrict H (mkst regs3 (w64 YE10.RC_END) mem3 (seg_rom tfxsegs)))).
{ rewrite restrict_mkst_fx. unfold ssC, regsC.
img_apply (st_ok_regs tfxsegs EC (mkSS MC_YEND sr_atoms [] None (mkFacts [] [] [])) _ regs0).
2:{ img_apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := img_ev (sr_get a r) in img_change (sr_get a r) with v;
let v2 := img_ev (sr_get b r2) in img_change (sr_get b r2) with v2 end;
first [ img_refl
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; unfold EC; rewrite (YE0v.Env_reg regs3 _ 21 21%bv eq_refl), Q21_3; img_refl) ] |]).
destruct Hr. }
unfold EC, YE0v.Env. img_apply (entry_st_ok_full tfxsegs); img_change (Ereg regs3 (map (Z_to_bv 64) [])) with EC.
+ img_apply regs_ok_Ereg.
+ img_case; vm_compute. all: img_refl.
+ img_apply Forall_nil.
+ cbn. img_exact I.
+ split; [|img_try (split; img_exact I)]. cbn. img_exact I. }
eapply SRr_bind; [img_try (img_apply (mc_phase_to W EC MC_RSTOP _ _ _ _ _ HC0 r_C))|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HF4 & _). rewrite ?wvb_wvb in *.
assert (MEQ4 : forall z, ms_mem ms4 z = mem3 z) by (img_try (intros z; rewrite (HF4 z); [img_refl | img_try (intros Hin; destruct (in_wrange_windows EC _ _ Hin) as (bb & lo & hi & Ht & Hw); destruct Ht)])).
clear HF4.
pose proof shapeC_ok as SC. unfold shapeC in SC.
apply andb_prop in SC as [SC CK4]. apply andb_prop in SC as [SC C1]. apply andb_prop in SC as [SC C12]. apply andb_prop in SC as [SC C11]. apply andb_prop in SC as [Cpc C10]. apply Z.eqb_eq in Cpc.
assert (RDC : forall (r : bv 5) v, reg_is eC (bv_unsigned r) v = true -> getr (ms_regs ms4) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. img_apply (st_ok_reg_denot H EC eC ms4 r HS4). }
assert (RKC : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms4) r = getr regs3 r).
{ intros r i Hi Hin. rewrite forallb_forall in CK4. rewrite Hi in Hin. specialize (CK4 _ Hin). cbn beta in CK4. rewrite <- Hi, Nat2Z.id in CK4.
rewrite (RDC r (SOff i 0)); [| img_try (rewrite <- Hi; img_exact CK4)]. cbn [sv_denot]. rewrite (ECreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. img_refl. }
pose proof (st_ok_restrict_mkst tfxsegs H EC _ _ HS4 eq_refl) as Cshape. rewrite Cpc in Cshape. rewrite Cshape.
assert (AVT : forall b, sp0 - 160 <= b < sp0 -> aview tfxsegs H (ms_mem ms4) b = aview tfxsegs H (ms_mem ms1) b).
{ intros b Hb. erewrite aview_same; [| img_try (img_apply MEQ4)]. rewrite AV3 by (img_try (unfold sp0 in *; img_lia)). img_apply AV2; unfold sp0 in *; img_lia. }
img_apply (mc_tail B LAWS TB ly S W regs mem md (ms_regs ms4) (ms_mem ms4) (with_vm_backing (m_vm_lazy md3) mat4 md3) x y n HPRE Hslo2 Hpres2 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
+ img_apply (al_frame _ _ LAWS ly S W mem3 md3 (ms_mem ms4) _ HAR3); [img_try (intros a _ _; img_apply aview_same; img_apply MEQ4) | img_try (intros a Hv; erewrite aview_same; [img_exact Hv | img_apply MEQ4]) | | | | img_try (img_exact (YE0v.hs_kept_eq _ _ _ MEQ4))];
img_apply (same_but_materialized_frame md3 _ (with_vm_backing_same md3 mat4)).
+ eapply same_but_materialized_trans; [img_try (img_exact MF1)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm2)|]. eapply same_but_materialized_trans; [img_try (img_exact Hsbm3) | img_try (img_apply with_vm_backing_same)].
+ intros a Hr Ha. unfold MC_SCR in Ha. erewrite aview_same; [| img_try (img_apply MEQ4)]. rewrite AV3, AV2; [img_try (img_apply AV1; [img_exact Hr | img_lia]) | img_try (img_exact Hr) | img_lia | img_try (img_exact Hr) | img_lia].
+ intros a Hp. img_apply (apresent_same H mem3 (ms_mem ms4) a (MEQ4 _)). img_apply Hpm3. img_apply Hpm2. img_apply PM1. img_exact Hp.
+ rewrite (RDC 10%bv (SOff 10 0) C10). cbn [sv_denot]. rewrite (ECreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned, A10_3.
rewrite (KK2 20 20%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q20.
+ rewrite (RDC 11%bv (SOff 18 0) C11). cbn [sv_denot]. rewrite (ECreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite (KK3 18 18%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (KK2 18 18%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q18.
+ rewrite (RDC 12%bv (SOff 9 0) C12). cbn [sv_denot]. rewrite (ECreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned. img_exact A9_3.
+ rewrite (RDC 1%bv (SLit MC_CALLRET) C1). img_refl.
+ rewrite (RKC 2%bv 2%nat eq_refl ltac:(img_try (cbn; img_lia))). rewrite (KK3 2 2%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (KK2 2 2%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q2.
+ rewrite (RKC 19%bv 19%nat eq_refl ltac:(img_try (cbn; img_lia))). rewrite (KK3 19 19%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (KK2 19 19%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q19.
+ rewrite (RKC 3%bv 3%nat eq_refl ltac:(img_try (cbn; img_lia))). rewrite (KK3 3 3%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (KK2 3 3%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q3.
+ rewrite (RKC 4%bv 4%nat eq_refl ltac:(img_try (cbn; img_lia))). rewrite (KK3 4 4%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). rewrite (KK2 4 4%bv ltac:(img_try (img_apply bv_eq; img_refl))) by (img_try (unfold acallee_saved; img_lia)). img_exact Q4.
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 0%nat (SOff 1 0) (-8) eq_refl (bv_unsigned (getr regs 1)) ltac:(cbn [sv_denot]; rewrite (EEreg 1%nat 1%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 1)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 1%nat (SOff 8 0) (-16) eq_refl (bv_unsigned (getr regs 8)) ltac:(cbn [sv_denot]; rewrite (EEreg 8%nat 8%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 8)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 2%nat (SOff 9 0) (-24) eq_refl (bv_unsigned (getr regs 9)) ltac:(cbn [sv_denot]; rewrite (EEreg 9%nat 9%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 9)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 3%nat (SOff 18 0) (-32) eq_refl (bv_unsigned (getr regs 18)) ltac:(cbn [sv_denot]; rewrite (EEreg 18%nat 18%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 18)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 4%nat (SLit (276552 + D_2c4)) (-56) eq_refl (276552 + D_2c4) eq_refl ltac:(img_lia))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 5%nat (SOff 12 0) (-64) eq_refl (bv_unsigned (getr regs 12)) ltac:(cbn [sv_denot]; rewrite (EEreg 12%nat 12%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 12)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 6%nat (SOff 11 0) (-72) eq_refl (bv_unsigned (getr regs 11)) ltac:(cbn [sv_denot]; rewrite (EEreg 11%nat 11%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 11)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 7%nat (SOff 10 0) (-80) eq_refl (bv_unsigned (getr regs 10)) ltac:(cbn [sv_denot]; rewrite (EEreg 10%nat 10%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 10)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 8%nat (SOff 19 0) (-88) eq_refl (bv_unsigned (getr regs 19)) ltac:(cbn [sv_denot]; rewrite (EEreg 19%nat 19%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 19)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 9%nat (SOff 20 0) (-96) eq_refl (bv_unsigned (getr regs 20)) ltac:(cbn [sv_denot]; rewrite (EEreg 20%nat 20%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 20)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 10%nat (SOff 21 0) (-104) eq_refl (bv_unsigned (getr regs 21)) ltac:(cbn [sv_denot]; rewrite (EEreg 21%nat 21%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 21)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 11%nat (SOff 22 0) (-112) eq_refl (bv_unsigned (getr regs 22)) ltac:(cbn [sv_denot]; rewrite (EEreg 22%nat 22%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 22)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 12%nat (SOff 23 0) (-120) eq_refl (bv_unsigned (getr regs 23)) ltac:(cbn [sv_denot]; rewrite (EEreg 23%nat 23%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 23)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 13%nat (SOff 24 0) (-128) eq_refl (bv_unsigned (getr regs 24)) ltac:(cbn [sv_denot]; rewrite (EEreg 24%nat 24%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 24)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 14%nat (SOff 25 0) (-136) eq_refl (bv_unsigned (getr regs 25)) ltac:(cbn [sv_denot]; rewrite (EEreg 25%nat 25%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 25)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 15%nat (SOff 26 0) (-144) eq_refl (bv_unsigned (getr regs 26)) ltac:(cbn [sv_denot]; rewrite (EEreg 26%nat 26%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 26)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
+ img_apply (VT (ms_mem ms1)); [img_try (img_exact (CK 16%nat (SOff 27 0) (-152) eq_refl (bv_unsigned (getr regs 27)) ltac:(cbn [sv_denot]; rewrite (EEreg 27%nat 27%bv eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; img_refl) (u64_range (getr regs 27)))) | img_try (intros b Hb; img_apply AVT; img_lia)].
Qed.
End g.
Theorem bc_icpt_realizes {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B ->
forall ly S (W : world tfxsegs) regs mem md x y n,
ecall_pre tfxsegs B ly S W regs mem md ->
ly_stk_lo ly + 2 * ESTACK <= spZ regs -> (forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 y -> getr regs 12 = w64 n -> 0 <= n < 2 ^ 32 ->
0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
src_ok tfxsegs W regs mem x n -> src_ok tfxsegs W regs mem y n ->
(forall a, x <= a < x + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
(forall a, y <= a < y + n -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs)) ->
amem_range x n -> amem_range y n ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF x n -> (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) x n) ->
range_addressable (aview tfxsegs (w_H W) mem) SHADOW_OFF y n -> (0 < n -> shadow_hull_vis (aview tfxsegs (w_H W) mem) y n) ->
SRr tfxsegs W (cfg_at tfxsegs (0x420d8 + D_2c4) regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md' (v : word),
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
AR tfxsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = v /\
(v = w64 0 <-> forall i, 0 <= i < n -> aview tfxsegs (w_H W) mem (x + i) = aview tfxsegs (w_H W) mem (y + i)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) -> aview tfxsegs (w_H W) mem' a = aview tfxsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
Proof.
intros B LAWS TB ly S W regs mem md x y n HPRE Hslo2 Hpres2 G10 G11 G12 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy.
img_exact (bc_icpt_srr B LAWS TB ly S W regs mem md x y n HPRE Hslo2 Hpres2 G10 G11 G12 Hn Hx Hxn Hy Hyn Hsx Hsy Hbx Hby Hamx Hamy Hrax Hhx Hray Hhy).
Qed.
Corollary bcmp_icpt_contract {imgk : img} : forall B, AR_laws tfxsegs B -> TfxSyms B -> abcmp_realizes tfxsegs B (0x420d8 + D_2c4).
Proof. intros B LAWS TB. img_exact (bc_icpt_realizes B LAWS TB). Qed.
End d.
