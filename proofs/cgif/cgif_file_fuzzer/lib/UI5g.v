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
UI1w UI4l UI21 UI5o UI5l YI6b YL0g
UI3m UI5m UN0d
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l
YI5a UI23 YI0a YL00 YI05 UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f UI5e UI5k UIZs UIZv.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Definition lits_tl : list (option Z) := [Some 0; Some 0; None; None; None; None; None; Some 0; Some 0; Some 0].
Definition ss_tl : sstate :=
mkSS L_TAIL sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 32 8 8 [mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 38 0))] ;
YP09.mkRegion (Some 2%nat) 64 144 64 72 (obj_chunks_gen (lay_shift 64 LAY_Config) 39 lits_tl ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4); (41%nat, mkAF 0 (2^32 - 1) 0); (45%nat, mkAF 0 65535 0) ] [] []).
Definition ss_tl_c : sstate := Eval vm_compute in ss_tl.
Lemma lits_tl_ok : forall attr gen W H ngp,
forall j z, nth_error lits_tl j = Some (Some z) -> nth_error [0; 0; attr; gen; W; H; ngp; 0; 0; 0] j = Some z.
Proof using.
intros attr gen W H ngp j z Hj. do 10 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
Lemma lh_wm_mod : forall m a v, word_mem ubs0segs m a v -> word_mem ubs0segs m a (v mod 2 ^ 64).
Proof using. intros m a v H k Hk. rewrite (H k Hk). f_equal. unfold le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma lh_mul3 : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 65536 -> sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof using.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Ltac tl_saved HS idx HU2 HW32 HW33 HW34 HW35 :=
unfold saved_ok; repeat match goal with |- _ /\ _ => split end;
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv - 144 + (144 - dd)) by lia;
let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw;
first [ eapply (st_chunk_word _ _ _ idx _ 2%nat (144 - dd) (SOff 32 0) _ _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW32, Z_to_bv_bv_unsigned; reflexivity | lia]
| eapply (st_chunk_word _ _ _ idx _ 2%nat (144 - dd) (SOff 33 0) _ _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW33, Z_to_bv_bv_unsigned; reflexivity | lia]
| eapply (st_chunk_word _ _ _ idx _ 2%nat (144 - dd) (SOff 34 0) _ _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW34, Z_to_bv_bv_unsigned; reflexivity | lia]
| eapply (st_chunk_word _ _ _ idx _ 2%nat (144 - dd) (SOff 35 0) _ _ HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HW35, Z_to_bv_bv_unsigned; reflexivity | lia] ]
end.
Ltac tl_untouched HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27 :=
unfold untouched_ok; repeat match goal with |- _ /\ _ => split end;
[ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 3%nat 3%bv eq_refl); exact G3)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 4%nat 4%bv eq_refl); exact G4)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 19%nat 19%bv eq_refl); exact G19)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 20%nat 20%bv eq_refl); exact G20)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 21%nat 21%bv eq_refl); exact G21)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 22%nat 22%bv eq_refl); exact G22)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 23%nat 23%bv eq_refl); exact G23)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 24%nat 24%bv eq_refl); exact G24)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 25%nat 25%bv eq_refl); exact G25)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 26%nat 26%bv eq_refl); exact G26)
| reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned, (HE 27%nat 27%bv eq_refl); exact G27) ].
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs0_msyms MR.
Hypothesis CLOSE : close_specX API.
Hypothesis ADDF : addframe_specX API.
Hypothesis UNLINK : unlink_x ubs0_msyms MR ubs0_A_unlink.
Hypothesis RFC : rfc_specX API.
Hypothesis NEWGIF : newgif_x API.
Variables (regs : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs L A mem md (ff_delta plen b0) fs' c' -> realizes ubs0segs c' (K (LL 0 fs' [])).
Hypothesis HROOM : ff_room b0 plen.
Hypothesis HFD : fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None.
Definition lh_case_x (C : Z -> Prop) : Prop :=
forall (p n : Z) (PAYLOAD : list Z),
C n ->
fn_pre ubs0_msyms MR LIB_STACK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 p -> getr regs 11 = Z_to_bv 64 n -> 0 < n -> In (p, n) (blocks L A) ->
sink_none ubs0_msyms mem md -> spZ regs <= 2 ^ 47 ->
garr8 ubs0segs mem p PAYLOAD -> Z.of_nat (length PAYLOAD) = n ->
res_ok A b0 ->
realizes ubs0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs)) md) (ff_tree K (m_fs md) PAYLOAD).
Lemma le_tail :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc (pdata nb cur attr gen W H ngp r1 r2 : Z) (PAYLOAD : list Z),
journal ubs0_msyms MR LIB_STACK (spZ regs) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs mod 16 = 0 ->
nb = 0 ->
Permutation (blocks Lc Ac) (blocks L A) ->
obj_at ubs0segs memc (spZ regs - 80) LAY_Config [0; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok memc (spZ regs) regs ->
word_mem ubs0segs memc (spZ regs - 136) pdata -> word_mem ubs0segs memc (spZ regs - 128) nb ->
word_mem ubs0segs memc (spZ regs - 120) cur -> 0 <= cur <= nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs - 144) -> getr regs1 8 = Z_to_bv 64 r1 -> getr regs1 10 = Z_to_bv 64 r2 ->
0 <= r1 < 2 ^ 64 -> 0 <= r2 < 2 ^ 64 ->
untouched_ok regs regs1 ->
sink_none ubs0_msyms mem md ->
garr8 ubs0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
(r1 = 0 -> r2 = 0 -> cur = 14 /\ hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD)) ->
(14 <= Z.of_nat (length PAYLOAD) -> r1 = 0 /\ r2 = 0) ->
res_ok Ac b0 ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs)) mdc) (ff_tree K (m_fs md) PAYLOAD).
Proof using HK HROOM IMG LAWS.
intros regs1 Lc Ac memc mdc pdata nb cur attr gen W H ngp r1 r2 PAYLOAD
HJ Hid Hra0 Htp0 Hal16 Hnb0 HB Hcfg HSV Wp Wn Wc Hcur G2 G8 G10 Rr1 Rr2 HUT HSN0 HPL HPLn HR12 H14 HRES.
apply realizes_via_SR.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HALv : ALLOC_STACK = 8192) by reflexivity. assert (HLSv : LIB_STACK = 16384) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
set (cvals := [0; 0; attr; gen; W; H; ngp; 0; 0; 0]) in *.
set (pd := pdata mod 2 ^ 64). pose proof (lh_wm_mod _ _ _ Wp) as Wp'. fold pd in Wp'. assert (Rpd : 0 <= pd < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs) ++ map (Z_to_bv 64) ([pd; nb; cur] ++ cvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pd; nb; cur] ++ cvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (saved_vals regs) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HX36 : ew E 36 = Z_to_bv 64 pd) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX41 : ew E 41 = Z_to_bv 64 attr) by (apply (HCV 2%nat); reflexivity).
assert (HX45 : ew E 45 = Z_to_bv 64 ngp) by (apply (HCV 6%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HW32 : ew E 32 = getr regs 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (Hst8 : (sp0 - 136) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 136) with ((2 * (sp0 / 16) - 17) * 8) by lia. apply Z_mod_mult. }
assert (HP0 : PAYLOAD = []) by (destruct PAYLOAD; [reflexivity | cbn in HPLn; lia]). subst PAYLOAD.
pose proof (Rcfg 2%nat attr eq_refl) as Rattr. pose proof (Rcfg 6%nat ngp eq_refl) as Rngp. cbn in Rattr, Rngp.
assert (HS : st_ok ubs0segs E ss_tl_c (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs))).
{ change ss_tl_c with ss_tl. unfold ss_tl. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pd); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; apply val_mem_word_mem; exact Wp']. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split.
* eapply (obj_chunks_gen_ok ubs0segs _ _ (sp0 - 144) _ cvals 39 lits_tl); [| reflexivity | | apply lits_tl_ok].
-- apply (proj1 (obj_at_shift _ _ (sp0 - 144) 64 LAY_Config cvals)). replace (sp0 - 144 + 64) with (sp0 - 80) by lia. exact Hcfg.
-- intros j v Hj. apply (HCV j v Hj).
* assert (CK : forall off j (w : Z), nth_error (saved_vals regs) j = Some w -> word_mem ubs0segs memc (sp0 - 144 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs) ++ map (Z_to_bv 64) ([pd; nb; cur] ++ cvals) ++ [])) memc (sp0 - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros off j w Hj Wm Rw. eapply (chunk_ok_val _ _ _ _ _ _ _ w); [| cbn; lia | cbn; lia | apply val_mem_word_mem; exact Wm].
cbn [sv_denot]. rewrite Z.add_0_r, (HSV' j w Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (RU : forall w : word, 0 <= bv_unsigned w < 2 ^ 64).
{ intros w. pose proof (bv_unsigned_in_range 64 w) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw. lia. }
unfold saved_chunks. cbn [Nat.add].
repeat (apply Forall_cons;
[ first [ apply (CK 136 0%nat _ eq_refl); [replace (sp0 - 144 + 136) with (sp0 - 8) by lia; exact W1 | apply RU]
| apply (CK 128 1%nat _ eq_refl); [replace (sp0 - 144 + 128) with (sp0 - 16) by lia; exact W8 | apply RU]
| apply (CK 120 2%nat _ eq_refl); [replace (sp0 - 144 + 120) with (sp0 - 24) by lia; exact W9 | apply RU]
| apply (CK 112 3%nat _ eq_refl); [replace (sp0 - 144 + 112) with (sp0 - 32) by lia; exact W18 | apply RU] ] | ]).
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HX41, HX45, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
assert (HNZ : r1 <> 0 \/ r2 <> 0).
{ destruct (Z.eq_dec r1 0) as [E1|E1]; [destruct (Z.eq_dec r2 0) as [E2|E2]; [exfalso | right; exact E2] | left; exact E1].
destruct (HR12 E1 E2) as [Hc14 _]. lia. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_TAIL) memc (seg_rom ubs0segs))) in HJ.
jrun LAWS ubs0tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch ubs0tbl HS; clear Hc.
-
jrun LAWS ubs0tbl_ok HS HJ.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch ubs0tbl HS.
+ clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ L_FREERET.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] => replace (ss_pc x) with L_FREERET by (vm_compute; reflexivity) end. apply SR_here.
unfold ff_tree. rewrite (ff_cfg_hdr_short [] (hdr5_short [] ltac:(cbn; lia))). unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (llvm_freeret_x API IMG regs L A mem md b0 plen K HK rg Lc Ac mm mdc 0 0 b0) end.
* exact HJ. * exact Hid. * exact Hra0. * exact Htp0. * exact Hal16.
* left. split; [reflexivity | intros b Hb; eapply Permutation_in; [apply Permutation_sym; exact HB | exact Hb]].
* fold sp0. tl_saved HS 1%nat HU2 HW32 HW33 HW34 HW35.
* fold sp0. reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* fold sp0. replace (sp0 - 80) with (sp0 - 144 + 64) by lia.
eapply (st_chunk_word _ _ _ 1%nat _ 2%nat 64 (SLit 0) _ 0 HS); [reflexivity | reflexivity | cbv; auto 20 | exact HU2 | reflexivity | lia].
* tl_untouched HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
* exact HSN0.
* exact HRES.
* exact (b0_fin b0 plen).
+ exfalso. rewrite branch_ne_U, YI04.U_lit in Hc by lia.
apply Bool.negb_false_iff, Z.eqb_eq in Hc. destruct (U_or_zero _ _ _ Hc) as [Z1 Z2].
rewrite (U_atom _ 8 r1) in Z1 by (first [rewrite (HE 8%nat 8%bv eq_refl); exact G8 | lia]).
rewrite (U_atom _ 10 r2) in Z2 by (first [rewrite (HE 10%nat 10%bv eq_refl); exact G10 | lia]).
destruct HNZ; contradiction.
-
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_malloc.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (2%bv:reg) as Hm2. jreg HS (4%bv:reg) as Hm4. jreg HS (1%bv:reg) as Hm1.
rewrite (HE 2%nat 2%bv eq_refl), G2 in Hm2. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hm4.
eapply SR_bind.
{ eapply (jmalloc_at_res API IMG) with (n := 3 * ngp) (spc := sp0 - 144);
[ exact HS | reflexivity | reflexivity | exact HJ | exact Hid
| rewrite (st_ok_reg ubs0segs _ _ _ 10%bv HS); eval_sr_get; exact (lh_mul3 _ 45 ngp HX45 ltac:(lia))
| exact HRES | apply (hdr_pal_room b0 plen HROOM); unfold PALMAX; lia
| exact Hm2 | lia | exact Hspm | lia | lia | exact Hm4 | exact Hm1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs3 & mem3 & md3 & res & -> & HJ3 & Hid3 & HP3 & Hres10 & (Hnz & Hres16 & (b1 & b2 & Hbl2 & Hblc) & Hwr) & Hkeep3 & Hhi3 & HR3).
change (ms_segs ubs0_msyms) with ubs0segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3, Hres10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
jafter_call_keep HS 49%nat regs3 mem3 HP3 [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor; [|constructor]];
(eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq. cbn [ms_regs mkst] in Hq. rewrite Hres10 in Hq. symmetry in Hq.
assert (Hpin : In (res, 3 * ngp) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L2 A2 mem3 md3 res (3 * ngp) HH3 Hpin) as [Hr0 Hr1].
assert (HB2 : Permutation (blocks L2 A2) ((res, 3 * ngp) :: blocks L A)).
{ rewrite Hbl2. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|]. apply perm_skip. rewrite <- Hblc. exact HB. }
assert (Hfresh : In (res, 3 * ngp) (blocks L A) -> 3 * ngp <= 0).
{ intros Hin. destruct (Z_lt_le_dec 0 (3 * ngp)) as [Hl|Hl]; [|exact Hl]. exfalso.
apply (fresh_not_in API L2 A2 mem3 md3 b1 b2 res (3 * ngp) HH3 Hbl2 Hl). rewrite <- Hblc. eapply Permutation_in; [apply Permutation_sym; exact HB|]. exact Hin. }
add_fact HS 53%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS ubs0tbl_ok HS HJ3 ubs0_A_readdata.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |].
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3'.
jreg HS (1%bv:reg) as Hn1.
eapply SR_bind.
{ eapply (jreaddata API IMG) with (st := sp0 - 136) (d := res) (n := 3 * ngp) (pdata := pd) (nb := nb) (cur := cur) (spc := sp0 - 144);
[ exact HS | reflexivity | reflexivity | exact HJ3
| rewrite (st_ok_reg ubs0segs _ _ _ 10%bv HS); eval_sr_get; cbn [sv_denot]; ew_havocA; rewrite HU2; f_equal; lia
| rewrite (st_ok_reg ubs0segs _ _ _ 11%bv HS); eval_sr_get; cbn [sv_denot]; rewrite Z.add_0_r, Hq, Z_to_bv_bv_unsigned; reflexivity
| rewrite (st_ok_reg ubs0segs _ _ _ 12%bv HS); eval_sr_get; apply lh_mul3; [ew_havocA; exact HX45 | lia]
| rewrite (st_ok_reg ubs0segs _ _ _ 2%bv HS); eval_sr_get; cbn [sv_denot]; ew_havocA; rewrite HU2; f_equal; lia
| exact Hspm | unfold RD_FRAME; lia | lia | lia | exact Hn1 | apply ret_ok_even; vm_compute; reflexivity
| lia | lia | exact Hst8
| replace (sp0 - 136) with (sp0 - 144 + 8) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 8 (SOff 36 0) _ pd HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | lia]
| replace (sp0 - 136 + 8) with (sp0 - 144 + 16) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 16 (SOff 37 0) _ nb HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | lia]
| replace (sp0 - 136 + 16) with (sp0 - 144 + 24) by lia;
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 24 (SOff 38 0) _ cur HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | lia]
| lia | lia | lia | lia | lia | intros _; exact Hnb0 | intros j Hj; lia
| lia | lia
| intros i Hi; exact (proj1 (heap_blocks _ _ LAWS L2 A2 _ md3 res (3 * ngp) i HH3' Hpin Hi))
| intros a Ha; replace a with (res + (a - res)) by lia; apply Hwr; [exact Hpin | lia]
| intros a Ha; left; lia
| right; lia | left; unfold RD_FRAME; lia | intros; lia | intros; lia | left; lia | intros; lia ]. }
intros c' (regs4 & mem4 & -> & HJ4 & HP4 & Hout4 & Hgr4 & Hrd).
jafter_call_keep HS 65%nat regs4 mem4 HP4 [1%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_rd _ _ _ _ (sp0 - 144) res (3 * ngp) (sp0 - 136)); [exact Hout4 | exact Hgr4 | ..];
cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite ?HU2; unfold RD_FRAME; lia. }
clear HS. rename HS2 into HS.
jrun LAWS ubs0tbl_ok HS HJ4.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jbranch ubs0tbl HS.
+ clear Hc.
jrun_to LAWS ubs0tbl_ok HS HJ4 L_FREERET.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). lazymatch goal with |- context [Z_to_bv 64 (ss_pc ?x)] => replace (ss_pc x) with L_FREERET by (vm_compute; reflexivity) end. apply SR_here.
unfold ff_tree. rewrite (ff_cfg_hdr_short [] (hdr5_short [] ltac:(cbn; lia))). unfold ff_leaf.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ => eapply (llvm_freeret_x API IMG regs L A mem md b0 plen K HK rg L2 A2 mm md3 res (3 * ngp) (rb_malloc b0 (3 * ngp))) end.
* exact HJ4. * exact Hid3. * exact Hra0. * exact Htp0. * exact Hal16.
* right. split; [exact HB2 | exact Hfresh].
* fold sp0. tl_saved HS 0%nat HU2 HW32 HW33 HW34 HW35.
* fold sp0. reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* fold sp0. replace (sp0 - 80) with (sp0 - 144 + 64) by lia.
eapply (st_chunk_word _ _ _ 0%nat _ 2%nat 64 (SOff 53 0) _ res HS); [reflexivity | reflexivity | cbv; auto 20 | ew_havocA; exact HU2 | cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, Hq, Z_to_bv_bv_unsigned; reflexivity | lia].
* tl_untouched HS HE G3 G4 G19 G20 G21 G22 G23 G24 G25 G26 G27.
* exact HSN0.
* exact HR3.
* apply (main_bud_fin b0 plen). apply (hdr_pal_bud b0). unfold PALMAX. lia.
+ exfalso. rewrite branch_ne_U, YI04.U_lit in Hc by lia.
apply Bool.negb_false_iff, Z.eqb_eq in Hc. destruct (U_or_zero _ _ _ Hc) as [_ Z0]. destruct (U_or_zero _ _ _ Z0) as [Z1 Z2].
rewrite (U_atom _ 8 r1) in Z1 by (first [ew_havocA; rewrite (HE 8%nat 8%bv eq_refl); exact G8 | lia]).
rewrite (U_atom _ 10 r2) in Z2 by (first [ew_havocA; rewrite (HE 10%nat 10%bv eq_refl); exact G10 | lia]).
destruct HNZ; contradiction.
Qed.
Lemma lh_case_any : forall C, lh_case_x C.
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK.
intros C p n PAYLOAD _ HPRE Hid G10 G11 Hn Hpn HSN0 Hsp47 HPL HPLn HRES0. apply realizes_via_SR.
pose proof HPRE as (HH & Hra & Hst & Htp & _). destruct Hst as (Hal16 & _).
destruct (blocks_range _ _ LAWS L A mem md p n HH Hpn) as [Hp0 Hp1].
pose proof (proj1 alloc_ceiling_val) as Hac.
eapply (lh_hdr API IMG regs L A mem md p n PAYLOAD); [exact HPRE | exact G10 | exact G11 | lia | lia | intros _; exact Hpn | exact HPL | exact HPLn |].
intros regs1 memc HJ1 Hcfg HSV Wp Wn Wc Hcur G2 G8 G10' R1 R2 HUT H1 H2.
apply SR_here.
exact (llvm_tail_x API IMG CLOSE ADDF UNLINK RFC NEWGIF regs L A mem md b0 plen K HSORT HK HROOM HFD regs1 L A memc md p n (lh_cur n)
(lh_attr PAYLOAD n) (lh_gen PAYLOAD n) (lh_W PAYLOAD n) (lh_H PAYLOAD n) (lh_ngp PAYLOAD n) (lh_r1 n) (lh_r2 n) PAYLOAD
HJ1 Hid Hra Htp Hal16 Hpn Hn (Permutation_refl _) Hcfg HSV Wp Wn Wc Hcur G2 G8 G10' R1 R2 HUT HSN0 Hsp47 HPL HPLn H1 H2 HRES0).
Qed.
Lemma lh_case_5 : lh_case_x (fun n => 14 <= n).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK. exact (lh_case_any _). Qed.
Lemma lh_case_4 : lh_case_x (fun n => 12 <= n < 14).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK. exact (lh_case_any _). Qed.
Lemma lh_case_3 : lh_case_x (fun n => 8 <= n < 12).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK. exact (lh_case_any _). Qed.
Lemma lh_case_2 : lh_case_x (fun n => 4 <= n < 8).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK. exact (lh_case_any _). Qed.
Lemma lh_case_1 : lh_case_x (fun n => 2 <= n < 4).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK. exact (lh_case_any _). Qed.
Lemma lh_case_0 : lh_case_x (fun n => n < 2).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG NEWGIF RFC UNLINK. exact (lh_case_any _). Qed.
Lemma lh_empty_x :
fn_pre ubs0_msyms MR LIB_STACK L A regs mem md -> st_init_done A = true ->
getr regs 11 = Z_to_bv 64 0 ->
sink_none ubs0_msyms mem md ->
res_ok A b0 ->
realizes ubs0segs (mkCfg (mkst regs (Z_to_bv 64 LLVM) mem (seg_rom ubs0segs)) md) (ff_tree K (m_fs md) []).
Proof using HK HROOM IMG LAWS.
intros HPRE Hid G11 HSN0 HRES0. apply realizes_via_SR.
set (p := bv_unsigned (getr regs 10)).
assert (G10 : getr regs 10 = Z_to_bv 64 p) by (subst p; symmetry; apply Z_to_bv_bv_unsigned).
assert (Rp : 0 <= p < 2 ^ 64) by (subst p; pose proof (bv_unsigned_in_range 64 (getr regs 10)) as R; change (bv_modulus 64) with (2 ^ 64) in R; lia).
assert (HPL : garr8 ubs0segs mem p []) by (intros j Hj; cbn in Hj; lia).
eapply (lh_hdr API IMG regs L A mem md p 0 []); [exact HPRE | exact G10 | exact G11 | exact Rp | lia | intros H0; lia | exact HPL | reflexivity |].
intros regs1 memc HJ1 Hcfg HSV Wp Wn Wc Hcur G2 G8 G10' R1 R2 HUT H1 H2.
apply SR_here.
pose proof HPRE as (_ & Hra & Hst & Htp & _). destruct Hst as (Hal16 & _).
exact (le_tail regs1 L A memc md p 0 (lh_cur 0) (lh_attr [] 0) (lh_gen [] 0) (lh_W [] 0) (lh_H [] 0) (lh_ngp [] 0) (lh_r1 0) (lh_r2 0) []
HJ1 Hid Hra Htp Hal16 eq_refl (Permutation_refl _) Hcfg HSV Wp Wn Wc Hcur G2 G8 G10' R1 R2 HUT HSN0 HPL eq_refl H1 H2 HRES0).
Qed.
End S.
End f.
