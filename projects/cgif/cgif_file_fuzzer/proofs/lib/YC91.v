(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI08 YI0t YI0m YI0n YI0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI10 YC4a YC8i YC80 YC1f YC1g YC81 YC4b.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8a YC93 YC9g YC95.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC8g.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_both3_1_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_1_listing PI) (@pa_relro_lo _ lib_both3_1_listing PI) (@pa_relro_hi _ lib_both3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Definition APTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Lemma APTR_PTR : forall al, APTR al = PTR al. Proof. intros al. reflexivity. Qed.
Definition shx (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 23 0).
Definition z_nimg (cx : lzw_acx) : Z := 2 ^ 64 - 1 - z_img cx.
Definition asr_fix : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 21%bv (shx 0)) 18%bv (SOff 8 24)) 19%bv (SOff 8 16)) 20%bv (SOff 8 8)) 26%bv (shx 8).
Definition asr_head : list sv := sr_set asr_fix 15%bv (SOff 39 0).
Definition actx_chunks : list YP09.chunk :=
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 4 (SOff 39 0)); YP09.mkChunk 60 (CVal 4 (SOff 41 0));
YP09.mkChunk 64 (CVal 2 (SOff 42 0)); YP09.mkChunk 66 (CVal 2 (SOff 43 0))].
Definition actx_region (w : bool) : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 72 (if w then 60 else 0) (if w then 68 else 0) actx_chunks.
Definition astk_chunks : list YP09.chunk :=
[YP09.mkChunk 40 (CVal 8 (SLit 1)); YP09.mkChunk 48 (CVal 8 (SLit 7)); YP09.mkChunk 56 (CVal 8 (SOff 8 66));
YP09.mkChunk 64 (CVal 8 (shx 64)); YP09.mkChunk 72 (CVal 8 (SOff 8 64)); YP09.mkChunk 80 (CVal 8 (shx 48));
YP09.mkChunk 88 (CVal 8 (SOff 8 48)); YP09.mkChunk 96 (CVal 8 (shx 40)); YP09.mkChunk 104 (CVal 8 (shx 56));
YP09.mkChunk 112 (CVal 8 (SOff 8 56)); YP09.mkChunk 120 (CVal 8 (shx 60)); YP09.mkChunk 128 (CVal 8 (SOff 8 60));
YP09.mkChunk 136 (CVal 8 (SOff 44 0)); YP09.mkChunk 144 (CVal 8 (shx 32)); YP09.mkChunk 152 (CVal 8 (SOff 45 0));
YP09.mkChunk 160 (CVal 8 (SOff 46 0)); YP09.mkChunk 168 (CVal 8 (shx 24)); YP09.mkChunk 176 (CVal 8 (shx 16));
YP09.mkChunk 184 (CVal 8 (SOff 8 40)); YP09.mkChunk 192 (CVal 8 (SOff 8 32))] ++ tsaved_chunks 47.
Definition astk_region (w : bool) : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 304 (if w then 8 else 0) (if w then 40 else 0) astk_chunks.
Definition acommon_facts : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, PTR 4); (23%nat, mkAF SB SB 0); (22%nat, mkAF 2 2 0); (25%nat, mkAF 2 256 0);
(32%nat, PTR 4); (33%nat, PTR 4); (34%nat, PTR 4); (35%nat, PTR 4); (36%nat, PTR 4); (37%nat, PTR 4);
(38%nat, PTR 0); (39%nat, mkAF 1 100000000 0); (40%nat, mkAF (2 ^ 64 - 1 - 140737479966720) (2 ^ 64 - 4097) 0);
(41%nat, mkAF 0 (2^27 - 2) 0); (42%nat, mkAF 4 4096 0); (43%nat, mkAF 1 2047 0);
(44%nat, mkAF 0 (2^47 - 16) 3); (45%nat, mkAF 4 512 0); (46%nat, mkAF 0 12 0) ].
Definition acommon_alias : list (sv * sv) := [ (SAlu ALU_XOR (SOff 38%nat 0) (SLit (-1)), SOff 40%nat 0) ].
Definition acx_extra (cx : lzw_acx) (lp dp mp : Z) (regs0 : bvmap 5 word) : list word :=
[ Z_to_bv 64 (z_ti cx); Z_to_bv 64 (z_lm cx); Z_to_bv 64 (z_lc cx); Z_to_bv 64 (z_li cx); Z_to_bv 64 (z_tm cx); Z_to_bv 64 (z_ld cx);
Z_to_bv 64 (z_img cx); Z_to_bv 64 (z_nP cx); Z_to_bv 64 (z_nimg cx); Z_to_bv 64 lp; Z_to_bv 64 dp; Z_to_bv 64 mp;
Z_to_bv 64 (z_pR cx); Z_to_bv 64 (2 * z_idl cx); Z_to_bv 64 (z_icl cx) ] ++ tsaved_vals regs0.
Definition alzw_ss (pc : Z) (sr : list sv) (wg ws : bool) (rs : smem) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr (actx_region wg :: astk_region ws :: rs) None (mkFacts (acommon_facts ++ fs) cs (acommon_alias ++ al)).
Definition alzw_regs_core (regs : bvmap 5 word) (cx : lzw_acx) : Prop :=
spZ regs = z_sp cx - 304 /\ getr regs 8 = w64 (z_ctx cx) /\
getr regs 18 = w64 (z_ctx cx + 24) /\ getr regs 19 = w64 (z_ctx cx + 16) /\ getr regs 20 = w64 (z_ctx cx + 8) /\
getr regs 23 = w64 SB /\ getr regs 22 = w64 2 /\ getr regs 25 = w64 (z_idl cx) /\
getr regs 3 = w64 (z_gp cx) /\ getr regs 4 = w64 (z_tp cx).
Lemma alzw_regs_core_of_fix : forall regs cx, alzw_regs_fix regs cx -> alzw_regs_core regs cx.
Proof.
intros regs cx (Hsp & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25 & H3 & H4).
unfold alzw_regs_core. repeat (split; [assumption|]). assumption.
Qed.
Section d.
Variables (regs : bvmap 5 word) (cx : lzw_acx) (lp dp mp : Z) (regs0 : bvmap 5 word) (more : list word).
Hypothesis HF : alzw_regs_core regs cx.
Let E := Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)).
Lemma AE_reg : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r.
Proof. intros r n H. apply ew_Eimg_Ereg_nat. exact H. Qed.
Lemma AE_x : forall j w, nth_error (acx_extra cx lp dp mp regs0) j = Some w -> ew E (32 + j) = w.
Proof.
intros j w Hj. subst E.
assert (Hjl : (j < length (acx_extra cx lp dp mp regs0))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hj; discriminate).
rewrite Eimg_low by (revert Hjl; unfold acx_extra, tsaved_vals, TSAVED; rewrite ?length_app, ?length_map; cbn [length Nat.add]; unfold A_TEXT; lia).
rewrite ew_Ereg_extra. rewrite app_nth1; [apply nth_error_nth; exact Hj | exact Hjl].
Qed.
Lemma AE_ti : ew E 32 = Z_to_bv 64 (z_ti cx).      Proof. apply (AE_x 0). reflexivity. Qed.
Lemma AE_lm : ew E 33 = Z_to_bv 64 (z_lm cx).      Proof. apply (AE_x 1). reflexivity. Qed.
Lemma AE_lc : ew E 34 = Z_to_bv 64 (z_lc cx).      Proof. apply (AE_x 2). reflexivity. Qed.
Lemma AE_li : ew E 35 = Z_to_bv 64 (z_li cx).      Proof. apply (AE_x 3). reflexivity. Qed.
Lemma AE_tm : ew E 36 = Z_to_bv 64 (z_tm cx).      Proof. apply (AE_x 4). reflexivity. Qed.
Lemma AE_ld : ew E 37 = Z_to_bv 64 (z_ld cx).      Proof. apply (AE_x 5). reflexivity. Qed.
Lemma AE_img : ew E 38 = Z_to_bv 64 (z_img cx).    Proof. apply (AE_x 6). reflexivity. Qed.
Lemma AE_nP : ew E 39 = Z_to_bv 64 (z_nP cx).      Proof. apply (AE_x 7). reflexivity. Qed.
Lemma AE_nimg : ew E 40 = Z_to_bv 64 (z_nimg cx).  Proof. apply (AE_x 8). reflexivity. Qed.
Lemma AE_lp : ew E 41 = Z_to_bv 64 lp.             Proof. apply (AE_x 9). reflexivity. Qed.
Lemma AE_dp : ew E 42 = Z_to_bv 64 dp.             Proof. apply (AE_x 10). reflexivity. Qed.
Lemma AE_mp : ew E 43 = Z_to_bv 64 mp.             Proof. apply (AE_x 11). reflexivity. Qed.
Lemma AE_pR : ew E 44 = Z_to_bv 64 (z_pR cx).      Proof. apply (AE_x 12). reflexivity. Qed.
Lemma AE_idl2 : ew E 45 = Z_to_bv 64 (2 * z_idl cx). Proof. apply (AE_x 13). reflexivity. Qed.
Lemma AE_icl : ew E 46 = Z_to_bv 64 (z_icl cx).    Proof. apply (AE_x 14). reflexivity. Qed.
Lemma AE_saved : forall j, (j < 13)%nat -> ew E (47 + j) = nth j (tsaved_vals regs0) (Z_to_bv 64 0).
Proof.
intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). replace (47 + j)%nat with (32 + (15 + j))%nat by lia. rewrite ew_Ereg_extra.
unfold acx_extra. rewrite <- app_assoc.
change (15 + j)%nat with (length [ Z_to_bv 64 (z_ti cx); Z_to_bv 64 (z_lm cx); Z_to_bv 64 (z_lc cx); Z_to_bv 64 (z_li cx); Z_to_bv 64 (z_tm cx); Z_to_bv 64 (z_ld cx);
Z_to_bv 64 (z_img cx); Z_to_bv 64 (z_nP cx); Z_to_bv 64 (z_nimg cx); Z_to_bv 64 lp; Z_to_bv 64 dp; Z_to_bv 64 mp;
Z_to_bv 64 (z_pR cx); Z_to_bv 64 (2 * z_idl cx); Z_to_bv 64 (z_icl cx) ] + j)%nat.
rewrite app_nth2_plus. rewrite app_nth1; [reflexivity|]. unfold tsaved_vals. rewrite length_map. cbn. lia.
Qed.
Lemma AE_more : forall j, (60 + j < A_TEXT)%nat -> ew E (60 + j) = nth j more (Z_to_bv 64 0).
Proof.
intros j Hj. subst E. rewrite Eimg_low by exact Hj. replace (60 + j)%nat with (32 + (28 + j))%nat by lia. rewrite ew_Ereg_extra.
change (28 + j)%nat with (length (acx_extra cx lp dp mp regs0) + j)%nat. apply app_nth2_plus.
Qed.
Lemma AE_sp : ew E 2 = Z_to_bv 64 (z_sp cx - 304).
Proof. rewrite (AE_reg 2%bv) by reflexivity. pose proof (proj1 HF) as H. unfold spZ in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma AE_ctx : ew E 8 = Z_to_bv 64 (z_ctx cx).       Proof. rewrite (AE_reg 8%bv) by reflexivity. apply HF. Qed.
Lemma AE_c24 : ew E 18 = Z_to_bv 64 (z_ctx cx + 24). Proof. rewrite (AE_reg 18%bv) by reflexivity. apply HF. Qed.
Lemma AE_c16 : ew E 19 = Z_to_bv 64 (z_ctx cx + 16). Proof. rewrite (AE_reg 19%bv) by reflexivity. apply HF. Qed.
Lemma AE_c8 : ew E 20 = Z_to_bv 64 (z_ctx cx + 8).   Proof. rewrite (AE_reg 20%bv) by reflexivity. apply HF. Qed.
Lemma AE_SB : ew E 23 = Z_to_bv 64 SB.               Proof. rewrite (AE_reg 23%bv) by reflexivity. apply HF. Qed.
Lemma AE_two : ew E 22 = Z_to_bv 64 2.               Proof. rewrite (AE_reg 22%bv) by reflexivity. apply HF. Qed.
Lemma AE_idl : ew E 25 = Z_to_bv 64 (z_idl cx).      Proof. rewrite (AE_reg 25%bv) by reflexivity. apply HF. Qed.
Lemma AE_gp : ew E 3 = Z_to_bv 64 (z_gp cx).         Proof. rewrite (AE_reg 3%bv) by reflexivity. apply HF. Qed.
Lemma AE_tp : ew E 4 = Z_to_bv 64 (z_tp cx).         Proof. rewrite (AE_reg 4%bv) by reflexivity. apply HF. Qed.
End d.
Lemma regs_ok_fix : forall regs cx lp dp mp regs0 more, alzw_regs_fix regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 < 2 ^ 64 ->
regs_ok (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) asr_fix regs.
Proof.
intros regs cx lp dp mp regs0 more (Hsp & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H25 & H3 & H4) Hc0 Hc1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))).
assert (E8 : ew E 8 = w64 (z_ctx cx)) by (subst E; rewrite Eimg_low, ew_Ereg_lt by (unfold A_TEXT; lia); exact H8).
assert (E21 : ew E 23 = w64 SB) by (subst E; rewrite Eimg_low, ew_Ereg_lt by (unfold A_TEXT; lia); exact H21).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?Ex (sr_get ?sr ?r) => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite Z.add_0_r; subst E; rewrite Eimg_low, ew_Ereg_lt by (unfold A_TEXT; lia);
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regs ?x)) => let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity
| rewrite ?E8, ?E21; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
first [ etransitivity; [exact H9 | reflexivity] | etransitivity; [exact H23 | reflexivity]
| etransitivity; [exact H18 | reflexivity] | etransitivity; [exact H19 | reflexivity] | etransitivity; [exact H20 | reflexivity]
| match goal with |- ?g => idtac "REGSOK" g end ] ]
| ]).
destruct Hr.
Qed.
Lemma regs_ok_head : forall regs cx lp dp mp regs0 more, alzw_regs_head regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 < 2 ^ 64 -> 1 <= z_nP cx <= 100000000 ->
regs_ok (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) asr_head regs.
Proof.
intros regs cx lp dp mp regs0 more [HFX H15] Hc0 Hc1 HnP.
unfold asr_head. apply regs_ok_pin; [apply (regs_ok_fix regs cx lp dp mp regs0 more HFX Hc0 Hc1) | intros X; discriminate X |].
cbn [sv_denot]. rewrite (AE_nP regs cx lp dp mp regs0 more), Z.add_0_r, unsigned_lit_small by lia. exact H15.
Qed.
Lemma shx_denot : forall E ctx k,
ew E 8 = Z_to_bv 64 ctx -> ew E 23 = Z_to_bv 64 SB -> 0 <= ctx -> ctx + k < 2 ^ 64 -> 0 <= k ->
sv_denot E (shx k) = Z_to_bv 64 (shadow_word (ctx + k)).
Proof.
intros E ctx k H8 H21 Hc Hk Hk0. unfold shx, shadow_word. cbn [sv_denot]. rewrite H8, H21, !unsigned_lit_small by (unfold SB; lia).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma alias_nimg : forall E n k img,
ew E n = Z_to_bv 64 img -> ew E k = Z_to_bv 64 (2 ^ 64 - 1 - img) -> 0 <= img < 2 ^ 64 ->
sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = sv_denot E (SOff k 0).
Proof.
intros E n k img Hn Hk Hi. apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n img Hn) by lia. rewrite (U_atom E k _ Hk) by lia.
rewrite U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1). rewrite YI08.lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma acommon_facts_ok : forall E cx lp dp mp,
ew E 2 = Z_to_bv 64 (z_sp cx - 304) -> ew E 8 = Z_to_bv 64 (z_ctx cx) -> ew E 23 = Z_to_bv 64 SB -> ew E 22 = Z_to_bv 64 2 -> ew E 25 = Z_to_bv 64 (z_idl cx) ->
ew E 32 = Z_to_bv 64 (z_ti cx) -> ew E 33 = Z_to_bv 64 (z_lm cx) -> ew E 34 = Z_to_bv 64 (z_lc cx) -> ew E 35 = Z_to_bv 64 (z_li cx) ->
ew E 36 = Z_to_bv 64 (z_tm cx) -> ew E 37 = Z_to_bv 64 (z_ld cx) -> ew E 38 = Z_to_bv 64 (z_img cx) -> ew E 39 = Z_to_bv 64 (z_nP cx) ->
ew E 40 = Z_to_bv 64 (z_nimg cx) -> ew E 41 = Z_to_bv 64 lp -> ew E 42 = Z_to_bv 64 dp -> ew E 43 = Z_to_bv 64 mp ->
ew E 44 = Z_to_bv 64 (z_pR cx) -> ew E 45 = Z_to_bv 64 (2 * z_idl cx) -> ew E 46 = Z_to_bv 64 (z_icl cx) ->
acx_ok cx -> acx_ranges cx -> 0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
atoms_ok E acommon_facts.
Proof.
intros E cx lp dp mp HE2 HE8 HE21 HE22 HE25 HE32 HE33 HE34 HE35 HE36 HE37 HE38 HE39 HE40 HE41 HE42 HE43 HE44 HE45 HE46 Hcx Hrg Hlp Hdp Hmp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3).
cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
assert (Hsp16 : (z_sp cx - 304) mod 16 = 0).
{ pose proof (Z.div_mod (z_sp cx) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (z_sp cx / 16) - 304) with ((z_sp cx / 16 - 19) * 16) by lia. apply Z_mod_mult. }
clear Hcx Hrg HMR HMR0 EMR.
cbn [atoms_ok acommon_facts]. unfold afact_ok, PTR, z_nimg in *. cbn [af_lo af_hi af_al2].
rewrite ?C1, ?C2, ?C3, ?C4, ?C5, ?HTS, ?Has in *. clear C2 C3 C4 C5 HTS Has.
rewrite HE2, HE8, HE21, HE22, HE25, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE40, HE41, HE42, HE43, HE44, HE45, HE46.
clear E HE2 HE8 HE21 HE22 HE25 HE32 HE33 HE34 HE35 HE36 HE37 HE38 HE39 HE40 HE41 HE42 HE43 HE44 HE45 HE46.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *.
repeat match goal with |- _ /\ _ => split end.
all: rewrite ?unsigned_lit_small by lia.
all: change (2 ^ 4) with 16 || idtac; change (2 ^ 3) with 8 || idtac; change (2 ^ 0) with 1 || idtac; rewrite ?Z.mod_1_r.
all: first [assumption | lia | match goal with |- ?g => idtac "SEEDFACT" g end].
Qed.
Lemma alzw_st_ok : forall cx regs regs0 lp dp mp more (m : word -> option byte) pc sr wg ws rs fs cs al,
acx_ok cx -> acx_ranges cx -> alzw_regs_core regs cx ->
agen_at m cx lp dp mp -> alzw_slots m cx -> alzw_sslots m cx -> tlzw_frame m (z_sp cx) regs0 ->
(wg = true -> forall a, z_ctx cx + 60 <= a < z_ctx cx + 68 -> writable_at SEGS m a) ->
(ws = true -> forall a, z_sp cx - 304 + 8 <= a < z_sp cx - 304 + 40 -> writable_at SEGS m a) ->
0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
let E := Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) in
regs_ok E sr regs ->
regions_wf (actx_region wg :: astk_region ws :: rs) = true ->
Forall (region_ok SEGS E m) rs ->
all_disjoint E (actx_region wg) rs -> all_disjoint E (astk_region ws) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok_pi SEGS VAL E (alzw_ss pc sr wg ws rs fs cs al) (mkst regs (Z_to_bv 64 (BASE + pc)) m (seg_rom SEGS)).
Proof.
intros cx regs regs0 lp dp mp more m pc sr wg ws rs fs cs al Hcx Hrg HF HG HSL HSS HFR Hwg Hws Hlp Hdp Hmp E Hsr Hwf Hrs Had1 Had2 Hpd Hfs Hcs Hal.
subst E. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 304 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3).
cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
rewrite ?C1, ?C2, ?C3, ?C4, ?C5, ?HTS, ?Has in *. clear C2 C3 C4 C5 HTS Has.
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
destruct HSL as (S40 & S48 & S56 & S72 & S88 & S112 & S128 & S152 & S160 & S136 & S184 & S192).
destruct HSS as (S64 & S80 & S96 & S104 & S120 & S176 & S144 & S168).
pose proof (AE_sp regs cx lp dp mp regs0 more HF) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HF) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HF) as HE21. pose proof (AE_two regs cx lp dp mp regs0 more HF) as HE22.
pose proof (AE_idl regs cx lp dp mp regs0 more HF) as HE25.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE32. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE33.
pose proof (AE_lc regs cx lp dp mp regs0 more) as HE34. pose proof (AE_li regs cx lp dp mp regs0 more) as HE35.
pose proof (AE_tm regs cx lp dp mp regs0 more) as HE36. pose proof (AE_ld regs cx lp dp mp regs0 more) as HE37.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE38. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE39.
pose proof (AE_nimg regs cx lp dp mp regs0 more) as HE40. pose proof (AE_lp regs cx lp dp mp regs0 more) as HE41.
pose proof (AE_dp regs cx lp dp mp regs0 more) as HE42. pose proof (AE_mp regs cx lp dp mp regs0 more) as HE43.
pose proof (AE_pR regs cx lp dp mp regs0 more) as HE44. pose proof (AE_idl2 regs cx lp dp mp regs0 more) as HE45.
pose proof (AE_icl regs cx lp dp mp regs0 more) as HE46.
assert (HR2 : region_ok SEGS (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) m (actx_region wg) /\
region_ok SEGS (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) m (astk_region ws)).
{ clear Hsr Hwf Hrs Had1 Had2 Hpd Hfs Hcs Hal HF Hcx Hrg HMR HMR0 Hgp Htp EMR.
split.
+
unfold region_ok, actx_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct wg; [apply Hwg; [reflexivity | lia] | lia]. }
unfold actx_chunks.
Ltac ack S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia | first [exact S | rewrite Z.add_0_r; exact S] ].
constructor; [ack V0 HE32|]. constructor; [ack V8 HE33|]. constructor; [ack V16 HE34|]. constructor; [ack V24 HE35|].
constructor; [ack V32 HE36|]. constructor; [ack V40 HE37|]. constructor; [ack V48 HE38|]. constructor; [ack V56 HE39|].
constructor; [ack V60 HE41|]. constructor; [ack V64 HE42|]. constructor; [ack V66 HE43|]. constructor.
+
unfold region_ok, astk_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct ws; [apply Hws; [reflexivity | lia] | lia]. }
unfold astk_chunks. apply Forall_app; split.
* Ltac sck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl | first [exact S | match type of S with val_mem _ _ _ _ ?v => match goal with |- val_mem _ _ _ _ ?v' => replace v' with v by lia; exact S end end] ].
Ltac shck S HE8 HE21 := eapply chunk_ok_val; [ eapply shx_denot; [exact HE8 | exact HE21 | lia | lia | lia] | | cbn; apply Z.le_refl | first [exact S | rewrite Z.add_0_r; exact S] ];
[ unfold shadow_word;
match goal with |- 0 <= bv_unsigned ?w < _ => let Hr := fresh in pose proof (bv_unsigned_in_range 64 w) as Hr;
change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr end ].
constructor; [eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact S40]|].
constructor; [eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact S48]|].
constructor; [sck S56 HE8|]. constructor; [shck S64 HE8 HE21|]. constructor; [sck S72 HE8|]. constructor; [shck S80 HE8 HE21|].
constructor; [sck S88 HE8|]. constructor; [shck S96 HE8 HE21|]. constructor; [shck S104 HE8 HE21|]. constructor; [sck S112 HE8|].
constructor; [shck S120 HE8 HE21|]. constructor; [sck S128 HE8|]. constructor; [sck S136 HE44|]. constructor; [shck S144 HE8 HE21|].
constructor; [sck S152 HE45|]. constructor; [sck S160 HE46|]. constructor; [shck S168 HE8 HE21|]. constructor; [shck S176 HE8 HE21|].
constructor; [sck S184 HE8|]. constructor; [sck S192 HE8|]. constructor.
* apply (tsaved_chunks_ok (Eimg (Ereg regs (acx_extra cx lp dp mp regs0 ++ more))) m (z_sp cx) regs0 47); [|exact HFR].
intros j Hj. apply (AE_saved regs cx lp dp mp regs0 more j Hj). }
destruct HR2 as [HRg HRs].
apply pa_entry_st_ok_full.
- exact Hsr.
- exact Hwf.
- constructor; [exact HRg | constructor; [exact HRs | exact Hrs]].
-
split; [|split; [exact Had2 | exact Hpd]].
cbn [all_disjoint]. split; [|exact Had1].
unfold extent_disjoint, actx_region, astk_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite HE8, HE2, !unsigned_lit_small by lia. lia.
-
split; [|split; [exact Hcs |]].
+ unfold alzw_ss. cbn [f_atoms]. apply atoms_ok_app; [|exact Hfs].
eapply (acommon_facts_ok _ cx lp dp mp); eassumption.
+ unfold alzw_ss. cbn [f_alias]. split; [|exact Hal].
apply (alias_nimg _ 38 40 (z_img cx) HE38 HE40). lia.
Qed.
End c.
End b.
