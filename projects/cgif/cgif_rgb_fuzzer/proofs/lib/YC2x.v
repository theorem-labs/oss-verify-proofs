(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI01 YI07 YI03 YI04 YI06.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC0x YC3g YC2z YC3e YC31.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition APTR (al : Z) : afact := mkAF 4096 140737479966720 al.

Definition shx (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 k) (SLit 3)) (SOff 27 0).
Definition asr_fix : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 1%bv (SOff 8 40)) 9%bv (SOff 8 32)) 18%bv (SOff 8 24)) 19%bv (SOff 8 16))
20%bv (SOff 8 8)) 22%bv (shx 0)) 26%bv (shx 8).
Definition asr_t5 : list sv := sr_set asr_fix 30%bv (SOff 8 60).
Definition asr_head : list sv := sr_set asr_t5 16%bv (SOff 59 0).
Definition actx_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 0 (CVal 8 (SOff 53 0)); YQ0b.mkChunk 8 (CVal 8 (SOff 54 0)); YQ0b.mkChunk 16 (CVal 8 (SOff 55 0));
YQ0b.mkChunk 24 (CVal 8 (SOff 56 0)); YQ0b.mkChunk 32 (CVal 8 (SOff 57 0)); YQ0b.mkChunk 40 (CVal 8 (SOff 58 0));
YQ0b.mkChunk 48 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 56 (CVal 4 (SOff 59 0)); YQ0b.mkChunk 60 (CVal 4 (SOff 33 0));
YQ0b.mkChunk 64 (CVal 2 (SOff 34 0)); YQ0b.mkChunk 66 (CVal 2 (SOff 35 0))].
Definition actx_region (w : bool) : YQ0b.region :=
YQ0b.mkRegion (Some 8%nat) 0 72 (if w then 60 else 0) (if w then 68 else 0) actx_chunks.
Definition astk_chunks : list YQ0b.chunk :=
[YQ0b.mkChunk 56 (CVal 8 (SOff 25 2)); YQ0b.mkChunk 64 (CVal 8 (shx 66));
YQ0b.mkChunk 72 (CVal 8 (SOff 8 66)); YQ0b.mkChunk 80 (CVal 8 (shx 64)); YQ0b.mkChunk 88 (CVal 8 (SOff 8 60)); YQ0b.mkChunk 96 (CVal 8 (SOff 8 64));
YQ0b.mkChunk 104 (CVal 8 (shx 60)); YQ0b.mkChunk 112 (CVal 8 (shx 48)); YQ0b.mkChunk 120 (CVal 8 (SOff 8 48)); YQ0b.mkChunk 128 (CVal 8 (shx 40));
YQ0b.mkChunk 136 (CVal 8 (shx 56)); YQ0b.mkChunk 144 (CVal 8 (SOff 8 56)); YQ0b.mkChunk 152 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 160 (CVal 8 (shx 32));
YQ0b.mkChunk 168 (CVal 8 (SOff 37 0)); YQ0b.mkChunk 176 (CVal 8 (SOff 39 0)); YQ0b.mkChunk 184 (CVal 8 (SOff 38 0)); YQ0b.mkChunk 192 (CVal 8 (shx 24));
YQ0b.mkChunk 200 (CVal 8 (shx 16)); YQ0b.mkChunk 208 (CVal 8 (SOff 8 40))] ++ tsaved_chunks 40.
Definition astk_region (w : bool) : YQ0b.region :=
YQ0b.mkRegion (Some 2%nat) 0 320 (if w then 8 else 0) (if w then 56 else 0) astk_chunks.
Definition acommon_facts : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (8%nat, PTR 4); (27%nat, mkAF SB SB 0); (21%nat, mkAF 2 2 0);
(53%nat, PTR 4); (54%nat, PTR 4); (55%nat, PTR 4); (56%nat, PTR 4); (57%nat, PTR 4); (58%nat, PTR 4);
(25%nat, mkAF 2 256 0); (59%nat, mkAF 1 100000000 0); (32%nat, PTR 0);
(33%nat, mkAF 0 (2^27 - 2) 0); (34%nat, mkAF 4 4096 0); (35%nat, mkAF 1 2047 0); (36%nat, mkAF 0 (2^47 - 16) 3);
(37%nat, mkAF 4 512 0); (38%nat, mkAF 8 131072 0); (39%nat, mkAF 0 12 0) ].
Definition acx_extra (cx : lzw_acx) (lp dp mp : Z) (regs0 : bvmap 5 word) : list word :=
[ Z_to_bv 64 (z_img cx); Z_to_bv 64 lp; Z_to_bv 64 dp; Z_to_bv 64 mp; Z_to_bv 64 (z_pR cx); Z_to_bv 64 (2 * z_idl cx);
Z_to_bv 64 (z_tisz cx); Z_to_bv 64 (z_icl cx) ] ++ tsaved_vals regs0 ++
[ Z_to_bv 64 (z_ti cx); Z_to_bv 64 (z_lm cx); Z_to_bv 64 (z_lc cx); Z_to_bv 64 (z_li cx); Z_to_bv 64 (z_tm cx); Z_to_bv 64 (z_ld cx);
Z_to_bv 64 (z_nP cx) ].
Definition alzw_ss (pc : Z) (sr : list sv) (wg ws : bool) (rs : smem) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr (actx_region wg :: astk_region ws :: rs) None (mkFacts (acommon_facts ++ fs) cs al).
Definition alzw_regs_core (regs : bvmap 5 word) (cx : lzw_acx) : Prop := alzw_regs_fix regs cx.
Lemma alzw_regs_core_of_fix : forall regs cx, alzw_regs_fix regs cx -> alzw_regs_core regs cx.
Proof. intros regs cx H. exact H. Qed.
Section c.
Variables (regs : bvmap 5 word) (cx : lzw_acx) (lp dp mp : Z) (regs0 : bvmap 5 word) (more : list word).
Hypothesis HF : alzw_regs_core regs cx.
Let E := Ereg regs (acx_extra cx lp dp mp regs0 ++ more).
Lemma AE_reg : forall (r : bv 5) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r.
Proof. intros r n H. apply ew_Ereg_nat. exact H. Qed.
Lemma AE_x : forall j w, nth_error (acx_extra cx lp dp mp regs0) j = Some w -> ew E (32 + j) = w.
Proof.
intros j w Hj. subst E. rewrite ew_Ereg_extra. rewrite app_nth1.
- apply nth_error_nth. exact Hj.
- apply (proj1 (nth_error_Some _ _)). rewrite Hj. discriminate.
Qed.
Lemma AE_img : ew E 32 = Z_to_bv 64 (z_img cx).     Proof. apply (AE_x 0). reflexivity. Qed.
Lemma AE_lp : ew E 33 = Z_to_bv 64 lp.              Proof. apply (AE_x 1). reflexivity. Qed.
Lemma AE_dp : ew E 34 = Z_to_bv 64 dp.              Proof. apply (AE_x 2). reflexivity. Qed.
Lemma AE_mp : ew E 35 = Z_to_bv 64 mp.              Proof. apply (AE_x 3). reflexivity. Qed.
Lemma AE_pR : ew E 36 = Z_to_bv 64 (z_pR cx).       Proof. apply (AE_x 4). reflexivity. Qed.
Lemma AE_idl2 : ew E 37 = Z_to_bv 64 (2 * z_idl cx). Proof. apply (AE_x 5). reflexivity. Qed.
Lemma AE_tisz : ew E 38 = Z_to_bv 64 (z_tisz cx).   Proof. apply (AE_x 6). reflexivity. Qed.
Lemma AE_icl : ew E 39 = Z_to_bv 64 (z_icl cx).     Proof. apply (AE_x 7). reflexivity. Qed.
Lemma AE_saved : forall j, (j < 13)%nat -> ew E (40 + j) = nth j (tsaved_vals regs0) (Z_to_bv 64 0).
Proof.
intros j Hj. subst E. replace (40 + j)%nat with (32 + (8 + j))%nat by lia. rewrite ew_Ereg_extra.
unfold acx_extra. rewrite <- !app_assoc. change (8 + j)%nat with (length [ Z_to_bv 64 (z_img cx); Z_to_bv 64 lp; Z_to_bv 64 dp; Z_to_bv 64 mp; Z_to_bv 64 (z_pR cx); Z_to_bv 64 (2 * z_idl cx);
Z_to_bv 64 (z_tisz cx); Z_to_bv 64 (z_icl cx) ] + j)%nat.
rewrite app_nth2_plus. rewrite app_nth1; [reflexivity|]. unfold tsaved_vals. rewrite length_map. cbn. lia.
Qed.
Lemma AE_ti : ew E 53 = Z_to_bv 64 (z_ti cx).     Proof. apply (AE_x 21). reflexivity. Qed.
Lemma AE_lm : ew E 54 = Z_to_bv 64 (z_lm cx).     Proof. apply (AE_x 22). reflexivity. Qed.
Lemma AE_lc : ew E 55 = Z_to_bv 64 (z_lc cx).     Proof. apply (AE_x 23). reflexivity. Qed.
Lemma AE_li : ew E 56 = Z_to_bv 64 (z_li cx).     Proof. apply (AE_x 24). reflexivity. Qed.
Lemma AE_tm : ew E 57 = Z_to_bv 64 (z_tm cx).     Proof. apply (AE_x 25). reflexivity. Qed.
Lemma AE_ld : ew E 58 = Z_to_bv 64 (z_ld cx).     Proof. apply (AE_x 26). reflexivity. Qed.
Lemma AE_nP : ew E 59 = Z_to_bv 64 (z_nP cx).     Proof. apply (AE_x 27). reflexivity. Qed.
Lemma AE_more : forall j, ew E (60 + j) = nth j more (Z_to_bv 64 0).
Proof.
intros j. subst E. replace (60 + j)%nat with (32 + (28 + j))%nat by lia. rewrite ew_Ereg_extra.
change (28 + j)%nat with (length (acx_extra cx lp dp mp regs0) + j)%nat. apply app_nth2_plus.
Qed.
Lemma AE_sp : ew E 2 = Z_to_bv 64 (z_sp cx - 320).
Proof. rewrite (AE_reg 2%bv) by reflexivity. pose proof (proj1 HF) as H. unfold spZ in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma AE_ctx : ew E 8 = Z_to_bv 64 (z_ctx cx).  Proof. rewrite (AE_reg 8%bv) by reflexivity. apply HF. Qed.
Lemma AE_SB : ew E 27 = Z_to_bv 64 SB.           Proof. rewrite (AE_reg 27%bv) by reflexivity. apply HF. Qed.
Lemma AE_two : ew E 21 = Z_to_bv 64 2.           Proof. rewrite (AE_reg 21%bv) by reflexivity. apply HF. Qed.
Lemma AE_idl : ew E 25 = Z_to_bv 64 (z_idl cx).  Proof. rewrite (AE_reg 25%bv) by reflexivity. apply HF. Qed.
Lemma AE_gp : ew E 3 = Z_to_bv 64 (z_gp cx).     Proof. rewrite (AE_reg 3%bv) by reflexivity. apply HF. Qed.
Lemma AE_tp : ew E 4 = Z_to_bv 64 (z_tp cx).     Proof. rewrite (AE_reg 4%bv) by reflexivity. apply HF. Qed.
End c.
Lemma regs_ok_fix : forall regs cx ext, alzw_regs_fix regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 < 2 ^ 64 ->
regs_ok (Ereg regs ext) asr_fix regs.
Proof.
intros regs cx ext (Hsp & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H25 & H26 & H27 & H1 & H3 & H4) Hctx0 Hctx.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (E8 : ew (Ereg regs ext) 8 = w64 (z_ctx cx)) by (rewrite ew_Ereg_lt by lia; exact H8).
assert (E27 : ew (Ereg regs ext) 27 = w64 SB) by (rewrite ew_Ereg_lt by lia; exact H27).
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
[ match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
cbn [sv_denot];
first [ rewrite getr_zero; reflexivity
| rewrite Z.add_0_r, ew_Ereg_lt by lia;
match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr regs ?x)) => let y := eval vm_compute in x in change x with y end;
rewrite Z_to_bv_bv_unsigned; reflexivity
| rewrite ?E8, ?E27; unfold w64; rewrite ?unsigned_lit_small by (unfold SB; lia); rewrite ?Z.add_0_r;
first [ etransitivity; [exact H1 | reflexivity] | etransitivity; [exact H9 | reflexivity] | etransitivity; [exact H18 | reflexivity]
| etransitivity; [exact H19 | reflexivity] | etransitivity; [exact H20 | reflexivity]
| etransitivity; [exact H22 | reflexivity] | etransitivity; [exact H26 | reflexivity]
| match goal with |- ?g => idtac "REGSOK" g end ] ]
| ]).
destruct Hr.
Qed.
Lemma regs_ok_t5 : forall regs cx ext, alzw_regs_fix regs cx -> getr regs 30 = w64 (z_ctx cx + 60) -> 0 <= z_ctx cx -> z_ctx cx + 72 < 2 ^ 64 ->
regs_ok (Ereg regs ext) asr_t5 regs.
Proof.
intros regs cx ext HF H30 Hc0 Hc. unfold asr_t5.
apply regs_ok_pin; [exact (regs_ok_fix regs cx ext HF Hc0 Hc) | intros X; discriminate X |].
destruct HF as (_ & H8 & _).
assert (E8 : ew (Ereg regs ext) 8 = w64 (z_ctx cx)) by (rewrite ew_Ereg_lt by lia; exact H8).
cbn [sv_denot]. rewrite E8, H30. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma regs_ok_head : forall regs cx lp dp mp regs0 more, alzw_regs_head regs cx -> 0 <= z_ctx cx -> z_ctx cx + 72 < 2 ^ 64 -> 1 <= z_nP cx <= 100000000 ->
regs_ok (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) asr_head regs.
Proof.
intros regs cx lp dp mp regs0 more (HF & H30 & H16) Hc0 Hc HnP. unfold asr_head.
apply regs_ok_pin; [exact (regs_ok_t5 regs cx _ HF H30 Hc0 Hc) | intros X; discriminate X |].
cbn [sv_denot]. rewrite (AE_nP regs cx lp dp mp regs0 more), H16. unfold w64. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma shx_denot : forall E ctx k,
ew E 8 = Z_to_bv 64 ctx -> ew E 27 = Z_to_bv 64 SB -> 0 <= ctx -> ctx + k < 2 ^ 64 -> 0 <= k ->
sv_denot E (shx k) = Z_to_bv 64 (shadow_word (ctx + k)).
Proof.
intros E ctx k H8 H27 Hc Hk Hk0. unfold shx, shadow_word. cbn [sv_denot]. rewrite H8, H27, !unsigned_lit_small by (unfold SB; lia).
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma acommon_facts_ok : forall E cx lp dp mp,
ew E 2 = Z_to_bv 64 (z_sp cx - 320) -> ew E 8 = Z_to_bv 64 (z_ctx cx) -> ew E 27 = Z_to_bv 64 SB -> ew E 21 = Z_to_bv 64 2 ->
ew E 53 = Z_to_bv 64 (z_ti cx) -> ew E 54 = Z_to_bv 64 (z_lm cx) -> ew E 56 = Z_to_bv 64 (z_li cx) -> ew E 55 = Z_to_bv 64 (z_lc cx) ->
ew E 57 = Z_to_bv 64 (z_tm cx) -> ew E 58 = Z_to_bv 64 (z_ld cx) -> ew E 25 = Z_to_bv 64 (z_idl cx) -> ew E 59 = Z_to_bv 64 (z_nP cx) ->
ew E 32 = Z_to_bv 64 (z_img cx) -> ew E 33 = Z_to_bv 64 lp -> ew E 34 = Z_to_bv 64 dp -> ew E 35 = Z_to_bv 64 mp ->
ew E 36 = Z_to_bv 64 (z_pR cx) -> ew E 37 = Z_to_bv 64 (2 * z_idl cx) -> ew E 38 = Z_to_bv 64 (z_tisz cx) -> ew E 39 = Z_to_bv 64 (z_icl cx) ->
acx_ok cx -> acx_ranges cx -> 0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
atoms_ok E acommon_facts.
Proof.
intros E cx lp dp mp HE2 HE8 HE20 HE21 HE22 HE23 HE26 HE30 HE1 HE31 HE25 HE29 HE32 HE33 HE34 HE35 HE36 HE37 HE38 HE39 Hcx Hrg Hlp Hdp Hmp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3).
cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
assert (Hsp16 : (z_sp cx - 320) mod 16 = 0).
{ pose proof (Z.div_mod (z_sp cx) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (z_sp cx / 16) - 320) with ((z_sp cx / 16 - 20) * 16) by lia. apply Z_mod_mult. }
clear Hcx Hrg HMR HMR0 EMR.
cbn [atoms_ok acommon_facts]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
rewrite ?C1, ?C2, ?C3, ?C4, ?C5, ?HTS, ?Has in *. clear C2 C3 C4 C5 HTS Has.
rewrite HE2, HE8, HE20, HE21, HE22, HE23, HE26, HE30, HE1, HE31, HE25, HE29, HE32, HE33, HE34, HE35, HE36, HE37, HE38, HE39.
clear E HE2 HE8 HE20 HE21 HE22 HE23 HE26 HE30 HE1 HE31 HE25 HE29 HE32 HE33 HE34 HE35 HE36 HE37 HE38 HE39.
ceil; unfold SB, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *.
repeat match goal with |- _ /\ _ => split end.
all: rewrite ?unsigned_lit_small by lia.
all: change (2 ^ 4) with 16 || idtac; change (2 ^ 3) with 8 || idtac; change (2 ^ 0) with 1 || idtac; rewrite ?Z.mod_1_r.
all: first [assumption | lia | match goal with |- ?g => idtac "SEEDFACT" g end].
Qed.
Lemma alzw_st_ok : forall cx regs regs0 lp dp mp more (m : word -> option byte) pc sr wg ws rs fs cs al,
acx_ok cx -> acx_ranges cx -> alzw_regs_core regs cx ->
agen_at m cx lp dp mp -> alzw_slots m cx -> alzw_sslots m cx -> tlzw_frame m (z_sp cx) regs0 ->
(wg = true -> forall a, z_ctx cx + 60 <= a < z_ctx cx + 68 -> writable_at trasegs m a) ->
(ws = true -> forall a, z_sp cx - 320 + 8 <= a < z_sp cx - 320 + 56 -> writable_at trasegs m a) ->
0 <= lp <= 2 ^ 27 - 2 -> 4 <= dp <= 4096 -> 1 <= mp <= 2047 ->
let E := Ereg regs (acx_extra cx lp dp mp regs0 ++ more) in
regs_ok E sr regs ->
regions_wf (actx_region wg :: astk_region ws :: rs) = true ->
Forall (region_ok trasegs E m) rs ->
all_disjoint E (actx_region wg) rs -> all_disjoint E (astk_region ws) rs -> pairwise_disjoint E rs ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok trasegs E (alzw_ss pc sr wg ws rs fs cs al) (mkst regs (Z_to_bv 64 pc) m (seg_rom trasegs)).
Proof.
intros cx regs regs0 lp dp mp more m pc sr wg ws rs fs cs al Hcx Hrg HF HG HSL HSS HFR Hwg Hws Hlp Hdp Hmp E Hsr Hwf Hrs Had1 Had2 Hpd Hfs Hcs Hal.
subst E. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : LZW_TSTK = 336 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
pose proof Hcx as (Hidl & HnP & HMR & HMR0 & Hicl & Hal16 & Hsplo & Hsphi & HpR0 & HpR47 & HpR8 & Hgp & Htp & EMR).
pose proof Hrg as (HR & Hbi0 & Hbi1 & Hbi2 & Hbi3).
cbn [ranges acx_tabs lzw_tabs app] in HR.
destruct HR as ((Rld1 & Rld2 & Rld3 & Rld4) & (Rti1 & Rti2 & Rti3 & Rti4) & (Rlm1 & Rlm2 & Rlm3 & _) & (Rlc1 & Rlc2 & Rlc3 & _) & (Rli1 & Rli2 & Rli3 & _) &
(Rtm1 & Rtm2 & Rtm3 & Rtm4) & (Rg1 & Rg2 & Rg3 & _) & _).
pose proof (req_size_pos (z_Li cx)) as HrLi.
assert (Htisz : 8 <= z_tisz cx <= 131072) by (unfold z_tisz; clear - Hidl; nia).
rewrite ?C1, ?C2, ?C3, ?C4, ?C5, ?HTS, ?Has in *. clear C2 C3 C4 C5 HTS Has.
destruct HG as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V60 & V64 & V66).
destruct HSL as (S56 & S72 & S88 & S96 & S120 & S144 & S152 & S168 & S176 & S184 & S208).
destruct HSS as (S64 & S80 & S104 & S112 & S128 & S136 & S160 & S192 & S200).
pose proof (AE_sp regs cx lp dp mp regs0 more HF) as HE2. pose proof (AE_ctx regs cx lp dp mp regs0 more HF) as HE8.
pose proof (AE_SB regs cx lp dp mp regs0 more HF) as HE20. pose proof (AE_two regs cx lp dp mp regs0 more HF) as HE21.
pose proof (AE_ti regs cx lp dp mp regs0 more) as HE22. pose proof (AE_lm regs cx lp dp mp regs0 more) as HE23.
pose proof (AE_idl regs cx lp dp mp regs0 more HF) as HE25. pose proof (AE_li regs cx lp dp mp regs0 more) as HE26.
pose proof (AE_lc regs cx lp dp mp regs0 more) as HE30. pose proof (AE_tm regs cx lp dp mp regs0 more) as HE1.
pose proof (AE_ld regs cx lp dp mp regs0 more) as HE31. pose proof (AE_nP regs cx lp dp mp regs0 more) as HE29.
pose proof (AE_img regs cx lp dp mp regs0 more) as HE32. pose proof (AE_lp regs cx lp dp mp regs0 more) as HE33.
pose proof (AE_dp regs cx lp dp mp regs0 more) as HE34. pose proof (AE_mp regs cx lp dp mp regs0 more) as HE35.
pose proof (AE_pR regs cx lp dp mp regs0 more) as HE36. pose proof (AE_idl2 regs cx lp dp mp regs0 more) as HE37.
pose proof (AE_tisz regs cx lp dp mp regs0 more) as HE38. pose proof (AE_icl regs cx lp dp mp regs0 more) as HE39.
assert (HR2 : region_ok trasegs (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) m (actx_region wg) /\
region_ok trasegs (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) m (astk_region ws)).
{ clear Hsr Hwf Hrs Had1 Had2 Hpd Hfs Hcs Hal HF Hcx Hrg HMR HMR0 Hgp Htp EMR.
split.
+
unfold region_ok, actx_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE8, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct wg; [apply Hwg; [reflexivity | lia] | lia]. }
unfold actx_chunks.
Ltac ack S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl || lia | first [exact S | rewrite Z.add_0_r; exact S] ].
constructor; [ack V0 HE22|]. constructor; [ack V8 HE23|]. constructor; [ack V16 HE30|]. constructor; [ack V24 HE26|].
constructor; [ack V32 HE1|]. constructor; [ack V40 HE31|]. constructor; [ack V48 HE32|]. constructor; [ack V56 HE29|].
constructor; [ack V60 HE33|]. constructor; [ack V64 HE34|]. constructor; [ack V66 HE35|]. constructor.
+
unfold region_ok, astk_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct ws; [apply Hws; [reflexivity | lia] | lia]. }
unfold astk_chunks. apply Forall_app; split.
* Ltac sck S HE := eapply chunk_ok_val; [ cbn [sv_denot]; rewrite HE, unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity | cbn; lia | cbn; apply Z.le_refl | first [exact S | match type of S with val_mem _ _ _ _ ?v => match goal with |- val_mem _ _ _ _ ?v' => replace v' with v by lia; exact S end end] ].
Ltac shck S HE8 HE20 := eapply chunk_ok_val; [ eapply shx_denot; [exact HE8 | exact HE20 | lia | lia | lia] | | cbn; apply Z.le_refl | first [exact S | rewrite Z.add_0_r; exact S] ];
[ unfold shadow_word;
match goal with |- 0 <= bv_unsigned ?w < _ => let Hr := fresh in pose proof (bv_unsigned_in_range 64 w) as Hr;
change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr; exact Hr end ].
constructor; [sck S56 HE25|]. constructor; [shck S64 HE8 HE20|]. constructor; [sck S72 HE8|]. constructor; [shck S80 HE8 HE20|].
constructor; [sck S88 HE8|]. constructor; [sck S96 HE8|]. constructor; [shck S104 HE8 HE20|]. constructor; [shck S112 HE8 HE20|].
constructor; [sck S120 HE8|]. constructor; [shck S128 HE8 HE20|]. constructor; [shck S136 HE8 HE20|]. constructor; [sck S144 HE8|].
constructor; [sck S152 HE36|]. constructor; [shck S160 HE8 HE20|]. constructor; [sck S168 HE37|]. constructor; [sck S176 HE39|].
constructor; [sck S184 HE38|]. constructor; [shck S192 HE8 HE20|]. constructor; [shck S200 HE8 HE20|]. constructor; [sck S208 HE8|]. constructor.
* apply (tsaved_chunks_ok (Ereg regs (acx_extra cx lp dp mp regs0 ++ more)) m (z_sp cx) regs0 40); [|exact HFR].
intros j Hj. apply (AE_saved regs cx lp dp mp regs0 more j Hj). }
destruct HR2 as [HRg HRs].
apply entry_st_ok_full.
- exact Hsr.
- exact Hwf.
- constructor; [exact HRg | constructor; [exact HRs | exact Hrs]].
-
split; [|split; [exact Had2 | exact Hpd]].
cbn [all_disjoint]. split; [|exact Had1].
unfold extent_disjoint, actx_region, astk_region. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite HE8, HE2, !unsigned_lit_small by lia. lia.
-
split; [|split; [exact Hcs | exact Hal]].
unfold alzw_ss. cbn [f_atoms]. apply atoms_ok_app; [|exact Hfs].
eapply (acommon_facts_ok _ cx lp dp mp); eassumption.
Qed.
End b.
