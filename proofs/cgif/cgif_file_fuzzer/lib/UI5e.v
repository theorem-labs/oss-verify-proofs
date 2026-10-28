(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d YO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b YI06 UI5b YI09 YI08 YI0r
UI1w UI21 UI5o UI5l YI6b YL0g
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l
YI5a UI23 YI0a YL00 YI05 UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition ss_lret0 : sstate :=
mkSS L_RET0 sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144 (saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4) ] [] []).
Definition ss_lunlink : sstate :=
mkSS L_UNLINK sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144 (saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4) ] [] []).
Definition ss_lclose : sstate :=
mkSS L_CLOSE sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144 (saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4) ] [] []).
Lemma u64_range' : forall w : word, 0 <= bv_unsigned w < 2 ^ 64.
Proof using. intros w. pose proof (bv_unsigned_in_range 64 w) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
End c.
Ltac stack_word HS HU2 n Hn :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) ?v =>
replace (spv - dd) with (spv - 144 + (144 - dd)) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat (144 - dd) (SOff n 0) (spv - 144) v HS);
[ reflexivity | reflexivity | cbv; auto 60
| ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hn; first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]
| ]
end.
Ltac saved_ok_tac HS HU2 H32 H33 H34 H35 :=
unfold saved_ok;
split; [stack_word HS HU2 32%nat H32; apply u64_range'|];
split; [stack_word HS HU2 33%nat H33; apply u64_range'|];
split; [stack_word HS HU2 34%nat H34; apply u64_range'|];
stack_word HS HU2 35%nat H35; apply u64_range'.
Ltac he_reg_tac HE :=
rewrite Z_to_bv_bv_unsigned; lazymatch goal with |- ew _ ?n = getr _ ?r => rewrite (HE n r eq_refl) end; assumption.
Ltac ut_tac HS HE :=
unfold untouched_ok; repeat match goal with |- _ /\ _ => split end; reg_nowF HS ltac:(he_reg_tac HE).
Ltac rp_tac HS HE H33 H34 H35 sptac :=
apply regs_preserved_intro; cbn [ms_regs mkst];
[ reg_nowF HS sptac | reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE)
| reg_nowF HS ltac:(rewrite H33; apply Z_to_bv_bv_unsigned) | reg_nowF HS ltac:(rewrite H34; apply Z_to_bv_bv_unsigned)
| reg_nowF HS ltac:(rewrite H35; apply Z_to_bv_bv_unsigned)
| reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE)
| reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE)
| reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE) | reg_nowF HS ltac:(he_reg_tac HE) ].
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis UNLINK : unlink_x ubs0_msyms MR ubs0_A_unlink.
Lemma saved_st_ok : forall pc (rg0 rg1 : bvmap 5 word) mc (spv : Z) STK FP L0 A0 mem0 md0 Lc0 Ac0 mdc0,
journal ubs0_msyms MR STK spv FP L0 A0 mem0 md0 Lc0 Ac0 mc mdc0 -> STK = LIB_STACK -> spv = spZ rg0 ->
(spv - 144) mod 16 = 0 ->
saved_ok mc spv rg0 -> getr rg1 2 = Z_to_bv 64 (spv - 144) ->
st_ok ubs0segs (Ereg rg1 (map (Z_to_bv 64) (saved_vals rg0) ++ []))
(mkSS pc sr_atoms [ YP09.mkRegion (Some 2%nat) 8 144 8 144 (saved_chunks 32) ] None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4) ] [] []))
(mkst rg1 (Z_to_bv 64 pc) mc (seg_rom ubs0segs)).
Proof using API.
intros pc rg0 rg1 mc spv STK FP L0 A0 mem0 md0 Lc0 Ac0 mdc0 HJ -> Hsp0 Hspm HSV G2.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
assert (HSV' : forall j v, nth_error (saved_vals rg0) j = Some v -> ew (Ereg rg1 (map (Z_to_bv 64) (saved_vals rg0) ++ [])) (32 + j) = Z_to_bv 64 v)
by (intros j v Hj; apply Ereg_vals; exact Hj).
assert (HU2 : bv_unsigned (ew (Ereg rg1 (map (Z_to_bv 64) (saved_vals rg0) ++ [])) 2) = spv - 144)
by (rewrite (ew_Ereg_nat _ _ 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
pose proof HSV as (W1 & W8 & W9 & W18).
apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
assert (CK : forall off j (w : Z), nth_error (saved_vals rg0) j = Some w -> word_mem ubs0segs mc (spv - 144 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg rg1 (map (Z_to_bv 64) (saved_vals rg0) ++ [])) mc (spv - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 136 0%nat _ eq_refl); [replace (spv - 144 + 136) with (spv - 8) by lia; exact W1 | apply u64_range']
| apply (CK 128 1%nat _ eq_refl); [replace (spv - 144 + 128) with (spv - 16) by lia; exact W8 | apply u64_range']
| apply (CK 120 2%nat _ eq_refl); [replace (spv - 144 + 120) with (spv - 24) by lia; exact W9 | apply u64_range']
| apply (CK 112 3%nat _ eq_refl); [replace (spv - 144 + 112) with (spv - 32) by lia; exact W18 | apply u64_range'] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2.
change (2 ^ 4) with 16. repeat split; try lia; exact Hspm.
Qed.
Variables (regs0 : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs0 L A mem md (ff_delta plen b0) fs' c' -> realizes ubs0segs c' (K (LL 0 fs' [])).
Lemma llvm_ret0_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (bc : rbound),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> spZ regs0 mod 16 = 0 ->
(forall b, In b (blocks L A) -> In b (blocks Lc Ac)) ->
saved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> untouched_ok regs0 regs1 ->
sink_none ubs0_msyms mem md ->
res_ok Ac bc -> rb_le bc (ff_delta plen b0) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_RET0) memc (seg_rom ubs0segs)) mdc) (K (LL 0 (m_fs md) [])).
Proof using HK IMG LAWS.
intros regs1 Lc Ac memc mdc bc HJ Hid Hra0 Hal16 Hbase HSV G2 HUT HSN0 HRES HBLE.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
apply realizes_via_SR.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_lret0 (mkst regs1 (Z_to_bv 64 L_RET0) memc (seg_rom ubs0segs))).
{ unfold ss_lret0. subst E. eapply (saved_st_ok L_RET0 regs0 regs1 memc sp0); [exact HJ | reflexivity | reflexivity | exact Hspm | exact HSV | exact G2]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_RET0) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ)))). }
apply HK. unfold leaf_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), mdc end.
split. { cbn [ms_regs ms_mem mkst].
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HW32, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end. }
split; [exact (journal_nil_token API _ _ _ _ _ _ _ _ _ _ HJ)|].
split.
{ rp_tac HS HE HW33 HW34 HW35 ltac:(rewrite HU2; replace (sp0 - 144 + 144) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned). }
split; [exact Hid|].
split; [reg_nowF HS ltac:(reflexivity)|].
split; [exact (nil_sink_none API _ _ _ _ _ _ _ _ _ _ HJ HSN0)|].
split; [exact Hbase|].
split; [exact (nil_fs API _ _ _ _ _ _ _ _ _ _ HJ)|].
eapply res_ok_mono; [exact HBLE | exact HRES].
Qed.
Lemma llvm_unlink_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (FSX : Fs.Fs) (bc : rbound),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [sink_token] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 ->
(forall b, In b (blocks L A) -> In b (blocks Lc Ac)) ->
saved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> getr regs1 10 = Z_to_bv 64 ubs0_D_str_tmp_out_gif -> untouched_ok regs0 regs1 ->
sink_none ubs0_msyms memc mdc ->
m_fs mdc = FSX ->
res_ok Ac bc -> rb_le bc (ff_delta plen b0) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_UNLINK) memc (seg_rom ubs0segs)) mdc) (ff_unl K FSX).
Proof using HK IMG LAWS UNLINK.
intros regs1 Lc Ac memc mdc FSX bc HJ Hid Hra0 Htp0 Hal16 Hbase HSV G2 G10 HUT HSN HFS HRES HBLE.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
apply realizes_via_SR.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity. assert (HUSv : UNLINK_STK = 64) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0. pose proof HJ as HJ0.
pose proof HJ as (_ & Hos0 & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_lunlink (mkst regs1 (Z_to_bv 64 L_UNLINK) memc (seg_rom ubs0segs))).
{ unfold ss_lunlink. subst E. eapply (saved_st_ok L_UNLINK regs0 regs1 memc sp0); [exact HJ | reflexivity | reflexivity | exact Hspm | exact HSV | exact G2]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_UNLINK) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_unlink.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10. rewrite (HE 10%nat 10%bv eq_refl), G10 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
apply SR_here. rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
unfold ff_unl, ff_leaf. rewrite <- HFS.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (Hsp : spZ rg = sp0 - 144) by (unfold spZ; rewrite Hr2; apply unsigned_lit_small; lia) end.
eapply (UNLINK Lc Ac _ _ mdc).
{ eapply (fn_pre_of_journal ubs0_msyms MR); [exact HJ | rewrite Hr1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hsp; exact Hspm | unfold UNLINK_STK; lia | rewrite Hsp; lia | rewrite Hsp; lia | exact Hr4]. }
{ exact Hr10. }
{ apply (sink_none_frame ubs0_msyms memc); [| exact HSN]. intros a Ha. pose proof (ubs0_env_addr_range a Ha) as Hea.
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
1: intros c' (regs5 & mem5 & md5 & -> & HJc5 & HP5 & HSN5 & Hfds5 & Hfs5).
2: intros c' (regs5 & mem5 & md5 & -> & HJc5 & HP5 & HSN5 & Hfds5 & Hfs5 & Hheld).
all: assert (HJ5 : journal ubs0_msyms MR LIB_STACK sp0 [sink_token] L A mem md Lc Ac mem5 md5)
by (eapply (journal_sub ubs0_msyms MR); [exact HJ | exact HJc5 | rewrite Hsp; unfold UNLINK_STK; lia | rewrite Hsp; lia | intros a Ha; split; [exact Ha | pose proof (inFP_token a Ha); lia]]).
all: rewrite Hr1; apply realizes_via_SR; clear HJ.
all: cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
all: pose proof HJc5 as (_ & _ & Hhi5 & _); rewrite Hsp in Hhi5.
all: jafter_call_keep HS 42%nat regs5 mem5 HP5 [0%nat] HS2.
all: match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
1,3: constructor; [|constructor];
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi5 | lia | lia | lia | cbn; lia | cbn; lia].
all: clear HS; rename HS2 into HS.
all: jrun LAWS ubs0tbl_ok HS HJ5.
1,3: eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]; apply wr_ok_nil.
all: eapply (SR_ret_at ubs0segs ubs0tbl); [exact ubs0tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
1,4: exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5))).
1,3: exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ5)))).
all: apply HK; unfold leaf_post.
all: lazymatch type of HS with st_ok _ _ _ ?msf => exists Lc, Ac, (ms_regs msf), (ms_mem msf), md5 end.
all: split; [ cbn [ms_regs ms_mem mkst];
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
pose proof (st_ok_reg ubs0segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, HW32, Z_to_bv_bv_unsigned in Q1;
rewrite Q1, Hra0; reflexivity end |].
all: split; [exact HJ5|].
all: split; [rp_tac HS HE HW33 HW34 HW35 ltac:(rewrite HU2; replace (sp0 - 144 + 144) with sp0 by lia; subst sp0; unfold spZ; apply Z_to_bv_bv_unsigned)|].
all: split; [exact Hid|].
all: split; [reg_nowF HS ltac:(reflexivity)|].
all: split; [apply (sink_none_frame ubs0_msyms mem5); [| exact HSN5]; intros a Ha; pose proof (ubs0_env_addr_range a Ha) as Hea;
mem_back ltac:(rewrite ?HU2) ltac:(lia)|].
all: split; [exact Hbase|].
all: split; [exact Hfs5|].
all: eapply res_ok_mono; [exact HBLE | exact HRES].
Qed.
Lemma llvm_close_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (g : Z) (s : cgif_st) (N : Z) (rest : list (Z * Z))
(GPAL : list Z) (gs : YO07.gif_st) (bc : rbound),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [sink_token] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 -> spZ regs0 <= 2 ^ 47 ->
cgif_at memc g s -> cgif_wf s N -> Permutation (blocks Lc Ac) (cgif_blocks g s N ++ rest) ->
(forall b, In b (blocks L A) -> In b rest) ->
(exists b, In b (blocks L A) /\ 0 < snd b) ->
saved_ok memc (spZ regs0) regs0 ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> getr regs1 9 = Z_to_bv 64 g -> untouched_ok regs0 regs1 ->
cgif_rel memc mdc s N GPAL gs ->
Z.of_nat (length (concat (YO07.s_out gs))) + CLOSE_OUT N <= SINK_MAX ->
res_ok Ac bc -> close_room bc N -> rb_le (close_rb bc N (qcount gs)) (ff_delta plen b0) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_CLOSE) memc (seg_rom ubs0segs)) mdc)
(ff_unl K (Fs.fs_set (m_fs md) sink_path (bytes (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59])))).
Proof using CLOSE HK HSORT IMG LAWS UNLINK.
intros regs1 Lc Ac memc mdc g s N rest GPAL gs bc
HJ Hid Hra0 Htp0 Hal16 Hsp47 Hat Hwf HB Hbase Hpay HSV G2 G9 HUT HREL HLEN HRES HROOM HBLE.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27). apply realizes_via_SR.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity. assert (HCSv : CLOSE_STK = 9728) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HS : st_ok ubs0segs E ss_lclose (mkst regs1 (Z_to_bv 64 L_CLOSE) memc (seg_rom ubs0segs))).
{ unfold ss_lclose. subst E. eapply (saved_st_ok L_CLOSE regs0 regs1 memc sp0); [exact HJ | reflexivity | reflexivity | exact Hspm | exact HSV | exact G2]. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_CLOSE) memc (seg_rom ubs0segs))) in HJ.
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_close.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hr10. rewrite (HE 9%nat 9%bv eq_refl), G9 in Hr10.
jreg HS (2%bv:reg) as Hr2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hr4.
jreg HS (1%bv:reg) as Hr1.
eapply SR_bind.
{ eapply (jcall_tmp _ _ LAWS) with (STK1 := CLOSE_STK) (FP1 := cgif_fp g s N)
(K := fun L5 A5 (regs5 : bvmap 5 word) (mem5 : word -> option byte) (md5 : Model) =>
st_init_done A5 = true /\ Permutation (blocks L5 A5) rest /\ sink_none ubs0_msyms mem5 md5 /\
Fs.fs_lookup (m_fs md5) sink_path = Some (bytes (concat (YO07.close_gif (gcfg_of s GPAL) gs) ++ [59])) /\
res_ok A5 (close_rb bc N (qcount gs)));
[ exact HS | reflexivity | exact HJ | exact Hr1 | | apply ret_ok_even; vm_compute; reflexivity
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; exact Hspm | lia
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia
| unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | exact Hr4 | ].
- intros HPRE1. eapply SR_mono.
{ eapply (CLOSE _ _ _ _ _ g s N rest GPAL gs bc HPRE1 Hid HLEN);
[ unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | exact Hr10 | | exact Hwf | exact HB | | exact HRES | exact HROOM ].
- eapply (cgif_at_low API); [exact HH0 | exact HB | exact Hat |]. intros a Ha.
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity.
- eapply (cgif_rel_low API); [exact HH0 | exact HB | exact HREL |]. intros a Ha.
mb_frame_with HF ltac:(lia) ltac:(rewrite ?HU2; lia). reflexivity. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJc5 & HP5 & Hid5 & HSN5 & HB5 & HK5 & HR5).
exists L5, A5, regs5, mem5, md5. split; [rewrite Hr1; reflexivity|]. split; [exact HJc5|]. split; [exact HP5|].
split; [exact Hid5|]. split; [exact HB5|]. split; [exact HSN5|]. split; [exact HK5 | exact HR5].
- intros a (r & [<- | Hr] & Ha).
+ left. split; [exists sink_token; split; [left; reflexivity | exact Ha]|]. cbn in Ha. lia.
+ right. eapply (tmp_blocks_fp API); [exact HH0 | exact HB | exact Hbase | exists r; split; [exact Hr | exact Ha]]. }
cbv beta. intros c' (L5 & A5 & regs5 & mem5 & md5 & -> & HJ5 & HJc5 & HP5 & Hid5 & HB5 & HSN5 & HK5 & HR5). clear HJ.
cbn [ms_regs ms_mem mkst] in HJc5, HP5, HJ5.
pose proof HJc5 as (_ & _ & Hhi5 & _).
jafter_call_keep HS 42%nat regs5 mem5 HP5 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HKR : P); [|specialize (HS2 HKR); clear HKR] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi5 | lia | lia | unfold spZ; rewrite Hr2, unsigned_lit_small by lia; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun_to LAWS ubs0tbl_ok HS HJ5 L_UNLINK.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocF; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
apply SR_here. rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_unlink_x rg L5 A5 mm md5 _ (close_rb bc N (qcount gs))) end.
- exact HJ5.
- exact Hid5.
- exact Hra0.
- exact Htp0.
- exact Hal16.
- intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB5|]. apply Hbase. exact Hb.
- saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
- reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
- reg_nowF HS ltac:(reflexivity).
- ut_tac HS HE.
- apply (sink_none_frame ubs0_msyms mem5); [| exact HSN5]. intros a Ha. pose proof (ubs0_env_addr_range a Ha) as Hea.
mem_back ltac:(rewrite ?HU2) ltac:(lia).
- exact (journal_fs_set API _ _ _ _ _ _ _ _ _ _ _ _ HJ5 HSORT HK5).
- exact HR5.
- exact HBLE.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
