(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0p YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI1i UI59 UI56 YI0x YL0e YI08 YI0c UI3h UI3d
UI39 UI57 UI58 UI4y UI54 UI55 UI4z UI51 UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_rret0 : sstate :=
mkSS RL_RET0 sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 128 8 128 (rsaved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB - 128) (2^63 - 128) 4) ] [] []).
Definition ss_rmain : sstate :=
mkSS RL_MUL sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 128 8 128
([mkChunk 8 (CVal 8 (SOff 45 0)); mkChunk 16 (CVal 8 (SOff 36 0)); mkChunk 24 (CVal 8 (SOff 46 0))]
++ obj_chunks_gen (lay_shift 56 LAY_RgbConfig) 37 [Some 0; Some 0; Some 0; None; None; None; None; None]
++ rsaved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB - 128) (2^63 - 128) 4);
(36%nat, mkAF 14 CEIL_MAX 0); (43%nat, mkAF 0 65535 0); (44%nat, mkAF 0 65535 0);
(45%nat, mkAF 4096 CEIL_MAX 0); (46%nat, mkAF 14 14 0) ] [] []).
Definition ss_rmain_c : sstate := Eval vm_compute in ss_rmain.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis NEWG : rgb_newgif_spec API.
Hypothesis CLOSE : forall fx', rgb_close_spec (fx:=fx') API.
Hypothesis ADDF : forall fx', rgb_addframe_spec (fx:=fx') API.
Lemma rl_ret0 :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc,
frm_zero fp_csr ->
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> spZ regs0 mod 16 = 0 ->
(forall b, In b (blocks L A) -> In b (blocks Lc Ac)) ->
rsaved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 128) -> runtouched_ok regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 RL_RET0) memc (seg_rom ubs2segs)) mdc)
(rllvm_post API regs0 L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc HFZ HJ Hid Hra0 Hal16 Hbase HSV G2 (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 128) mod 16 = 0) by (replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (rsaved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs2segs E ss_rret0 (mkst regs1 (Z_to_bv 64 RL_RET0) memc (seg_rom ubs2segs))).
{ unfold ss_rret0. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (rsaved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 128 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ [])) memc (sp0 - 128) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
unfold rsaved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 120 0%nat _ eq_refl); [replace (sp0 - 128 + 120) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 112 1%nat _ eq_refl); [replace (sp0 - 128 + 112) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 104 2%nat _ eq_refl); [replace (sp0 - 128 + 104) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 96 3%nat _ eq_refl); [replace (sp0 - 128 + 96) with (sp0 - 32) by lia; exact W18 | apply RU] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; try lia; exact Hspm. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 RL_RET0) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
unfold rllvm_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists fx, Lc, Ac, (ms_regs msf), (ms_mem msf), mdc end.
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HW32, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact HFZ|].
split; [exact HJ|].
split.
{ apply regs_preserved_intro; cbn [ms_regs mkst].
- reg_nowF HS ltac:(rewrite HU2; replace (sp0 - 128 + 128) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4).
- reg_nowF HS ltac:(rewrite HW33; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW34; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite HW35; apply Z_to_bv_bv_unsigned).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26).
- reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27). }
split; [exact Hid|].
split; [reg_nowF HS ltac:(reflexivity)|].
exact Hbase.
Qed.
Lemma rl_main :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (p n W H attr gen loops : Z),
frm_zero fp_csr ->
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> spZ regs0 mod 16 = 0 ->
ubs2_rgb_rodata_ok mem ->
(forall b, In b (blocks L A) -> In b (blocks Lc Ac)) -> In (p, n) (blocks L A) -> 14 <= n ->
0 <= W < 65536 -> 0 <= H < 65536 ->
rsaved_ok memc (spZ regs0) regs0 ->
word_mem ubs2segs memc (spZ regs0 - 120) p -> word_mem ubs2segs memc (spZ regs0 - 112) n -> word_mem ubs2segs memc (spZ regs0 - 104) 14 ->
obj_at ubs2segs memc (spZ regs0 - 72) LAY_RgbConfig [0; 0; 0; attr; gen; loops; W; H] ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 128) -> runtouched_ok regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 RL_MUL) memc (seg_rom ubs2segs)) mdc)
(rllvm_post API regs0 L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc p n W H attr gen loops
HFZ HJ Hid Hra0 Htp0 Hal16 HRO Hbase Hpd Hn HW HH HSV Wp Wn Wc Hcfg G2 HUT.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity.
assert (HRSv : RRFC_STK = 8272) by reflexivity. assert (HNGv : RGBNEWGIF_STK = 9296) by reflexivity.
assert (HNMv : RGB_NMAX = 10000) by reflexivity. assert (HFCv : RGBFC_SIZE = 24) by reflexivity. assert (HCSv : RGBCONFIG_SIZE = 40) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _ & Hik).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 128) mod 16 = 0) by (replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 96) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 96) with ((2 * (sp0 / 16) - 12) * 8) by lia. apply Z_mod_mult. }
assert (Hst8 : (sp0 - 120) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 120) with ((2 * (sp0 / 16) - 15) * 8) by lia. apply Z_mod_mult. }
assert (Hg8 : (sp0 - 72) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 72) with ((2 * (sp0 / 16) - 9) * 8) by lia. apply Z_mod_mult. }
assert (Hpdc : In (p, n) (blocks Lc Ac)) by (apply Hbase; exact Hpd).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc p n HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
set (cvals := [0; 0; 0; attr; gen; loops; W; H]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ map (Z_to_bv 64) ([n] ++ cvals ++ [p; 14]) ++ [])).
assert (HE : forall k (rr : reg), Z.of_nat k = bv_unsigned rr -> ew E k = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (rsaved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([n] ++ cvals ++ [p; 14]) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (rsaved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (37 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (37 + j)%nat with (36 + (1 + j))%nat by lia. apply HY. change (nth_error (cvals ++ [p; 14]) j = Some v).
rewrite nth_error_app1; [exact Hj|]. apply nth_error_Some. congruence. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HX45 : ew E 45 = Z_to_bv 64 p) by (apply (HY 9%nat); reflexivity).
assert (HX46 : ew E 46 = Z_to_bv 64 14) by (apply (HY 10%nat); reflexivity).
assert (HE43 : ew E 43 = Z_to_bv 64 W) by (apply (HCV 6%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 H) by (apply (HCV 7%nat); reflexivity).
assert (HX36 : ew E 36 = Z_to_bv 64 n) by (apply (HY 0%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs2segs E ss_rmain_c (mkst regs1 (Z_to_bv 64 RL_MUL) memc (seg_rom ubs2segs))).
{ change ss_rmain_c with ss_rmain. unfold ss_rmain. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ p); [cbn [sv_denot]; rewrite Z.add_0_r, HX45; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity] | cbn; lia | cbn; lia | replace (sp0 - 128 + 8) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ n); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 128 + 16) with (sp0 - 112) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 14); [cbn [sv_denot]; rewrite Z.add_0_r, HX46; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity] | cbn; lia | cbn; lia | replace (sp0 - 128 + 24) with (sp0 - 104) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok ubs2segs _ _ (sp0 - 128) _ cvals 37); [| reflexivity | |].
* apply (proj1 (obj_at_shift _ _ (sp0 - 128) 56 LAY_RgbConfig cvals)). replace (sp0 - 128 + 56) with (sp0 - 72) by lia. exact Hcfg.
* intros j v Hj. apply (HCV j v Hj).
* intros j z Hj. do 8 (destruct j as [|j]; [cbn in Hj |- *; congruence|]). destruct j; discriminate Hj.
+ assert (CK : forall off j (w : Z), nth_error (rsaved_vals regs0) j = Some w -> word_mem ubs2segs memc (sp0 - 128 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs2segs (Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ map (Z_to_bv 64) ([n] ++ cvals ++ [p; 14]) ++ [])) memc (sp0 - 128) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
unfold rsaved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 120 0%nat _ eq_refl); [replace (sp0 - 128 + 120) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 112 1%nat _ eq_refl); [replace (sp0 - 128 + 112) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 104 2%nat _ eq_refl); [replace (sp0 - 128 + 104) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 96 3%nat _ eq_refl); [replace (sp0 - 128 + 96) with (sp0 - 32) by lia; exact W18 | apply RU] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HX36, HE43, HE44, HX45, HX46, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 RL_MUL) memc (seg_rom ubs2segs))) in HJ.
jrun LAWS ubs2tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
assert (HUN : U E (SMd M_MUL (SOff 44 0) (SOff 43 0)) = H * W).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom _ 44 H HE44), (U_atom _ 43 W HE43) by lia. apply zcanon_id. clear -HW HH. unfold M64; nia. }
jbranch ubs2tbl HS.
-
jrun_to LAWS ubs2tbl_ok HS HJ RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 L A mem md regs0 rg Lc Ac mm mdc) end.
+ exact HFZ. + exact HJ. + exact Hid. + exact Hra0. + exact Hal16. + exact Hbase.
+ rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
-
rewrite branch_ltu_U, U_lit, HUN in Hc by lia.
assert (HNle : H * W <= 10000) by (destruct (Z.ltb_spec 10000 (H * W)); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_rgb_newgif.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha10. rewrite HU2 in Ha10.
jreg HS (2%bv:reg) as Ha2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Ha2.
jreg HS (4%bv:reg) as Ha4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Ha4.
jreg HS (1%bv:reg) as Ha1.
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := RGBNEWGIF_STK) (FP1 := @nil (Z * Z))
(K := fun L4 A4 (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) =>
exists res : Z, getr regs4 10 = Z_to_bv 64 res /\
((res = 0 /\ exists leak, Permutation (blocks L4 A4) (leak ++ blocks Lc Ac)) \/
(res <> 0 /\ res mod 16 = 0 /\ exists g s,
obj_at ubs2segs mem4 res LAY_Rgb [g; ubs2_A_writecb; 0; 0; attr; gen; loops; W; H; 0; 0; R_PENDING] /\
cgif_at mem4 g s /\ cgif_wf s (W * H) /\
cg_frames s = [None; None; None] /\ cg_W s = W /\ cg_H s = H /\ cg_attr s = RGB_GIFATTR /\
cg_cur s = R_PENDING /\ cg_ihead s = 1 /\
Permutation (blocks L4 A4) ((res, RGB_SIZE) :: cgif_blocks g s (W * H) ++ blocks Lc Ac))));
[ exact HS | reflexivity | exact HJ | exact Ha1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; exact Hspm | lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | exact Ha4 | intros a Ha; destruct Ha as (rr & Hrr & _); destruct Hrr ].
intros HPRE1. eapply SR_mono.
{ eapply (NEWG _ _ _ _ _ (sp0 - 72) attr gen loops W H HPRE1 Hid);
[ rewrite Ha10; f_equal; lia | exact Hg8 | unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | lia | | | nia ].
- replace (sp0 - 72) with (sp0 - 128 + 56) by lia. apply (proj2 (obj_at_shift _ _ (sp0 - 128) 56 LAY_RgbConfig _)).
eapply (st_obj_at ubs2segs _ _ _ 0%nat _ 2%nat (sp0 - 128) _ _ 37 [Some ubs2_A_writecb; Some 0; Some 0; None; None; None; None; None] HS eq_refl eq_refl HU2);
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj. split.
+ rewrite nth_lay_shift_snd. destruct j as [|j]; [cbn in Hj; injection Hj as <-; unfold ubs2_A_writecb; cbn; lia | exact (Rcfg (Datatypes.S j) v Hj)].
+ destruct j as [|[|[|[|[|[|[|[|j]]]]]]]]; cbn [nth_error]; cbn in Hj;
first [ congruence | injection Hj as <-; first [ exact (HCV 3%nat _ eq_refl) | exact (HCV 4%nat _ eq_refl) | exact (HCV 5%nat _ eq_refl) | exact (HCV 6%nat _ eq_refl) | exact (HCV 7%nat _ eq_refl) ] | destruct j; discriminate Hj ].
- intros i Hi. cbn [ms_mem mkst]. apply (present_mbyte ubs2_msyms).
apply writable_off_img_present; [lia | unfold in_img1; lia |]. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & res & -> & HJc4 & HP4 & Hr10 & ALT).
exists L4, A4, regs4, mem4, md4. split; [rewrite Ha1; reflexivity|]. split; [exact HJc4|]. split; [exact HP4|].
exists res. split; [exact Hr10 | exact ALT]. }
cbv beta. intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & res & Hr10 & ALT). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc4, HP4, HJ4, Hr10.
pose proof HJc4 as (_ & _ & Hhi4 & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
jafter_call_keep HS 47%nat regs4 mem4 HP4 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi4 | lia | lia | unfold spZ; rewrite Ha2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq10. cbn [ms_regs mkst] in Hq10. rewrite Hr10 in Hq10. symmetry in Hq10.
destruct ALT as [(-> & leak & HB4) | (Hnz & Hres16 & g & s & Hobj4 & Hat4 & Hwf4 & Hfr3 & HsW & HsH & Hattr & Hcur4 & Hih4 & HB4)].
+
pin_reg HS (10%bv:reg) 0 Hr10.
jrun_to LAWS ubs2tbl_ok HS HJ4 RL_RET0.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (rl_ret0 L A mem md regs0 rg L4 A4 mm md4) end.
* exact HFZ. * exact HJ4.
* assert (Hp4 : In (p, n) (blocks L4 A4)) by (eapply Permutation_in; [apply Permutation_sym; exact HB4 | apply in_app_iff; right; exact Hpdc]).
apply blocks_In in Hp4 as (q & _ & Hq). exact (init_done_of_block A4 (q, n) (proj1 (proj2 HH4)) Hq).
* exact Hra0. * exact Hal16.
* intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB4|]. apply in_app_iff. right. apply Hbase. exact Hb.
* rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
+
rename res into r.
set (N := W * H) in *.
assert (Hrin : In (r, RGB_SIZE) (blocks L4 A4)) by (eapply blocks_perm_in; [exact HB4 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L4 A4 mem4 md4 r RGB_SIZE HH4 Hrin ltac:(unfold RGB_SIZE; lia)) as (Hr0 & Hr1 & Hr16). unfold RGB_SIZE in Hr1.
pose proof Hwf4 as (Hlen3 & HW1 & HH1 & HN & HNle' & Hngp & Hih & Hfwf).
assert (Hid4 : st_init_done A4 = true).
{ apply blocks_In in Hrin as (q & _ & Hq). exact (init_done_of_block A4 (q, RGB_SIZE) (proj1 (proj2 HH4)) Hq). }
add_fact HS 51%nat (mkAF 4096 (CEIL_MAX - 64) 4).
2:{ ew_havocA. rewrite Hq10, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS ubs2tbl_ok HS HJ4 ubs2_A_read_frameconfig.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hd10. rewrite HU2 in Hd10. jreg HS (11%bv:reg) as Hd11. rewrite HU2 in Hd11.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => pose proof (st_ok_reg ubs2segs Ec ssc msc (12%bv:reg) HS) as Hd12; eval_sr_get_in Hd12 end.
rewrite (denot_add0_mul _ 44 43 H W) in Hd12 by first [ew_havocA; assumption | clear -HW HH; nia].
jreg HS (2%bv:reg) as Hd2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hd2.
jreg HS (4%bv:reg) as Hd4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hd4. jreg HS (1%bv:reg) as Hd1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 128) by (unfold spZ; rewrite Hd2; apply unsigned_lit_small; lia) end.
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
eapply SR_bind.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (ubs2_read_frameconfig API IMG LIB_STACK_RGB sp0 [] L A mem md L4 A4 mm md4 rg ((r, RGB_SIZE) :: cgif_blocks g s N ++ blocks Lc Ac) (sp0 - 120) (sp0 - 96) N p n 14) end.
* exact HJ4. * exact Hid4.
* intros b Hb. right. apply in_app_iff. right. apply Hbase. exact Hb.
* exact HB4.
* right. apply in_app_iff. right. exact Hpdc.
* rewrite Hd1. apply ret_ok_even. vm_compute. reflexivity.
* exact Hd4.
* rewrite Hd10. f_equal. lia. * rewrite Hd11. f_equal. lia. * rewrite Hd12. subst N. f_equal. lia.
* rewrite Hsp. exact Hspm. * rewrite Hsp. lia. * rewrite Hsp. lia. * lia. * rewrite Hsp. lia. * unfold RGBFC_SIZE. lia. * unfold RGBFC_SIZE. lia.
* exact Hst8. * exact Hcf8. * lia. * subst N. unfold RGB_NMAX. nia. * lia. * lia.
* rstack_word HS HU2 45%nat HX45. lia.
* replace (sp0 - 120 + 8) with (sp0 - 112) by lia. rstack_word HS HU2 36%nat HX36. lia.
* replace (sp0 - 120 + 16) with (sp0 - 104) by lia. rstack_word HS HU2 46%nat HX46. lia. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & res & cur2 & -> & HJ7 & Hid7 & HP7 & Hr10' & Hres & Hfr7 & Hbb7 & Wp7 & Wn7 & Wc7 & Hcur7 & ALT). clear HJ4.
cbn [ms_regs ms_mem mkst] in HP7, Hfr7, Hbb7, Hr10'.
rewrite Hsp in Hfr7. rewrite Hd1.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_after_call ubs2segs 77 E1 ss1 ms1 regs7 mem7
[YQ0b.mkRegion (Some 2%nat) 56 128 56 128 (rsaved_chunks 32)] (ubs2_A_LLVMFuzzerTestOneInput + 0xe4) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [| apply submem_nil]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|]; split; [cbn; lia|];
apply incl_chunks_sound; vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) HP7) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss1 [YQ0b.mkRegion (Some 2%nat) 56 128 56 128 (rsaved_chunks 32)] 77 (ubs2_A_LLVMFuzzerTestOneInput + 0xe4)) in
change (ss_after_call ss1 _ 77 _) with ss2 in HS2 end.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite HU2; intros a Ha.
- apply Hfr7; unfold RGBFC_SIZE; lia.
- intros _. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7). lia. }
clear HS. rename HS2 into HS.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7) as HH7.
assert (Hr_bb : In (r, RGB_SIZE) ((r, RGB_SIZE) :: cgif_blocks g s N ++ blocks Lc Ac)) by (left; reflexivity).
assert (Hobj7 : obj_at ubs2segs mem7 r LAY_Rgb [g; ubs2_A_writecb; 0; 0; attr; gen; loops; W; H; 0; 0; R_PENDING]).
{ eapply obj_at_transport_range; [exact Hobj4 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi.
rewrite (Hbb7 r RGB_SIZE i Hr_bb) by (unfold RGB_SIZE; lia). mem_back ltac:(rewrite ?HU2) ltac:(lia). }
assert (Hat7 : cgif_at mem7 g s).
{ eapply (cgif_at_kept _ _ g s N ((r, RGB_SIZE) :: cgif_blocks g s N ++ blocks Lc Ac) ((r, RGB_SIZE) :: blocks Lc Ac)); [apply Permutation_middle | | exact Hbb7].
eapply (cgif_at_low API); [exact HH4 | | exact Hat4 |]; [eapply Permutation_trans; [exact HB4 | apply Permutation_middle] |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
clear HF HF0 HF1.
destruct ALT as [(-> & HB7) | (Hnz' & img' & fmt' & fattr' & fgen' & delay' & Hfc7 & Himg07 & Rimg7 & HB7)].
*
pin_reg HS (10%bv:reg) 0 Hr10'.
jrun_to LAWS ubs2tbl_ok HS HJ7 RL_CLOSE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rl_close API IMG (CLOSE fx) L A mem md regs0 rg L7 A7 mm md7 r _ g s N 0 0 (blocks Lc Ac)) end.
-- exact HFZ. -- exact HJ7. -- exact Hid7. -- exact Hra0. -- exact Htp0. -- exact Hal16.
-- eapply obj_at_transport_range; [exact Hobj7 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
-- reflexivity. -- reflexivity.
-- eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |]; [eapply Permutation_trans; [exact HB7 | apply Permutation_middle] |].
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
-- exact Hwf4. -- cbn [optb Z.eqb app]. exact HB7. -- exact Hbase.
-- exists (p, n). split; [exact Hpd | cbn; lia].
-- rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
-- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
-- reg_nowF HS ltac:(ew_havocA; rewrite Hq10, Z_to_bv_bv_unsigned; reflexivity).
-- runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
*
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_fact ubs2segs E1 ss1 ms1 81 (mkAF 1 (2 ^ 64 - 1) 0)) in HS;
[| unfold afact_ok; cbn [af_lo af_hi af_al2 ms_regs mkst];
lazymatch goal with |- context [ew ?Ex 81] =>
replace (ew Ex 81) with (getr regs7 10) by reflexivity end;
rewrite Hr10', unsigned_lit_small by lia; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia ] end.
lazymatch type of HS with st_ok _ _ ?ss1 _ => let v := eval vm_compute in ss1 in change ss1 with v in HS end.
jrun_to LAWS ubs2tbl_ok HS HJ7 RL_LH.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (rl_loop API IMG CLOSE ADDF 16 ltac:(lia) fx L A mem md regs0 rg L7 A7 mm md7 r g ubs2_A_writecb 0 0 attr gen loops W H 0 0 R_PENDING s N (blocks Lc Ac) p n cur2 img' fmt' fattr' fgen' delay') end.
-- exact HFZ. -- exact HJ7. -- exact Hid7. -- exact Hra0. -- exact Htp0. -- exact Hal16. -- exact HRO.
-- eapply obj_at_transport_range; [exact Hobj7 | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi. mem_back ltac:(rewrite ?HU2) ltac:(lia).
-- eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |].
{ eapply Permutation_trans; [exact HB7|]. eapply Permutation_trans; [apply (perm_ib_back _ _ _ []) | apply Permutation_middle]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
-- exact Hwf4. -- exact HsW. -- exact HsH. -- subst N. unfold RGB_NMAX. lia. -- left; reflexivity.
-- eapply Permutation_trans; [exact HB7 | ]. cbn [optb Z.eqb]. apply (perm_ib_back _ _ _ []).
-- exact Hbase. -- exact Hpd. -- lia.
-- rsaved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
-- intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). apply Wp7. exact Hkk.
-- intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 112 + Z.of_nat kk) with (sp0 - 120 + 8 + Z.of_nat kk) by lia. apply Wn7. exact Hkk.
-- intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 104 + Z.of_nat kk) with (sp0 - 120 + 16 + Z.of_nat kk) by lia. apply Wc7. exact Hkk.
-- lia.
-- fold sp0. eapply (obj_at_transport_range _ _ _ _ _ _ 24); [exact Hfc7 | reflexivity |]. intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). reflexivity.
-- exact Himg07. -- exact Rimg7.
-- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
-- lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc => pose proof (st_ok_reg ubs2segs Ec ssc msc (8%bv:reg) HS) as T8; eval_sr_get_in T8 end.
cbn [ms_regs mkst] in T8 |- *. rewrite T8. rewrite (denot_mul_atoms_r _ 44 43 H W) by first [ew_havocA; assumption | clear -HW HH; nia]. subst N. f_equal. lia.
-- reg_nowF HS ltac:(ew_havocA; rewrite Hq10, Z_to_bv_bv_unsigned; reflexivity).
-- reg_nowF HS ltac:(reflexivity).
-- runtouched_tac HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
Qed.
End S.
End c.
