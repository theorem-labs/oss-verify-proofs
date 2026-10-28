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
UI57 UI4y UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition rsaved_chunks (k : nat) : list YQ0b.chunk :=
[mkChunk 120 (CVal 8 (SOff k 0)); mkChunk 112 (CVal 8 (SOff (k+1) 0)); mkChunk 104 (CVal 8 (SOff (k+2) 0)); mkChunk 96 (CVal 8 (SOff (k+3) 0))].
Definition rsaved_vals (regs0 : bvmap 5 word) : list Z :=
[bv_unsigned (getr regs0 1); bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18)].
Lemma rgb_fp_eq : forall r X bef n,
(r, r + RGB_SIZE) :: blocks_fp X ++ optfp bef n = blocks_fp ((r, RGB_SIZE) :: X ++ optb bef n).
Proof.
intros r X bef n. unfold blocks_fp, optfp, optb. cbn [map fst snd]. f_equal. rewrite map_app. f_equal.
destruct (bef =? 0); reflexivity.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition ss_rlclose : sstate :=
mkSS RL_CLOSE sr_atoms
[ YQ0b.mkRegion (Some 2%nat) 8 128 8 128 (rsaved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK_RGB - 128) (2^63 - 128) 4) ] [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Hypothesis CLOSE : rgb_close_spec API.
Lemma rl_close :
forall L A mem md (regs0 regs1 : bvmap 5 word) Lc Ac memc mdc (r : Z) (rv : list Z) (g : Z) (s : cgif_st) (N bef nbef : Z) (rest : list (Z * Z)),
frm_zero fp_csr ->
journal ubs2_msyms MR LIB_STACK_RGB (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs2_msyms) -> spZ regs0 mod 16 = 0 ->
obj_at ubs2segs memc r LAY_Rgb rv -> nth_error rv RG_gif = Some g -> nth_error rv RG_bef = Some bef ->
cgif_at memc g s -> cgif_wf s N ->
Permutation (blocks Lc Ac) ((r, RGB_SIZE) :: cgif_blocks g s N ++ optb bef nbef ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) ->
(exists b, In b (blocks L A) /\ 0 < snd b) ->
rsaved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 128) -> getr regs1 9 = Z_to_bv 64 r -> runtouched_ok regs0 regs1 ->
SR ubs2segs (mkCfg (mkst regs1 (Z_to_bv 64 RL_CLOSE) memc (seg_rom ubs2segs)) mdc)
(rllvm_post API regs0 L A mem md).
Proof.
intros L A mem md regs0 regs1 Lc Ac memc mdc r rv g s N bef nbef rest HFZ HJ Hid Hra0 Htp0 Hal16 Hobj Hg Hbef Hat Hwf HB Hbase Hpay HSV G2 G9
(G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK_RGB = 61440) by reflexivity. assert (HCSv : RGBCLOSE_STK = 9760) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 128) mod 16 = 0) by (replace (sp0 - 128) with (sp0 + (-8) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hrin : In (r, RGB_SIZE) (blocks Lc Ac)) by (eapply Permutation_in; [apply Permutation_sym; exact HB | left; reflexivity]).
destruct (blocks_range _ _ LAWS Lc Ac memc mdc r RGB_SIZE HH0 Hrin) as [Hrlo Hrhi]. unfold RGB_SIZE in Hrhi.
set (E := Ereg regs1 (map (Z_to_bv 64) (rsaved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (rsaved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 128) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs2segs E ss_rlclose (mkst regs1 (Z_to_bv 64 RL_CLOSE) memc (seg_rom ubs2segs))).
{ unfold ss_rlclose. subst E. apply entry_st_ok.
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
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 RL_CLOSE) memc (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_cgif_rgb_close.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := RGBCLOSE_STK) (FP1 := (r, r + RGB_SIZE) :: blocks_fp (cgif_blocks g s N) ++ optfp bef nbef)
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) => Permutation (blocks L5 A5) rest);
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; exact Hspm | lia
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (CLOSE _ _ _ _ _ r rv g s N bef nbef rest HPRE1 Hid Hr10); [| exact Hg | exact Hbef | | exact Hwf | exact HB].
- eapply obj_at_transport_range; [exact Hobj | apply lay_inside_Rgb |]. intros i Hi. unfold RGB_SIZE in Hi.
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity.
- eapply (cgif_at_low API); [exact HH0 | | exact Hat |].
{ eapply Permutation_trans; [exact HB|]. apply Permutation_middle. }
intros a Ha. mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & HB5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5 | exact HB5].
- intros a Ha. right. rewrite rgb_fp_eq in Ha. eapply (tmp_blocks_fp API); [exact HH0 | | exact Hbase | exact Ha].
eapply Permutation_trans; [exact HB|]. cbn [app]. apply perm_skip. rewrite app_assoc. apply Permutation_refl. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & HB5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5.
pose proof HJc5 as (_ & _ & Hhi5 & _).
jafter_call_keep HS 36%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs2segs _ _ _ 2); [exact HU2 | exact Hhi5 | lia | lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ5.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5)))). }
unfold rllvm_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists fx, L5, A5, (ms_regs msf), (ms_mem msf), md5 end.
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
split; [exact HJ5|].
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
split.
{ destruct Hpay as ([pb pn] & Hpin & Hpn). cbn [snd] in Hpn.
assert (Hp5 : In (pb, pn) (blocks L5 A5)) by (eapply Permutation_in; [apply Permutation_sym; exact HB5 | apply Hbase; exact Hpin]).
apply blocks_In in Hp5 as (q & _ & Hq).
exact (init_done_of_block A5 (q, pn) (proj1 (proj2 (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ5))) Hq). }
split; [reg_nowF HS ltac:(reflexivity)|].
intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB5|]. apply Hbase. exact Hb.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
