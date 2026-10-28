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
UI1w UI4l UI21 UI5o UI5l YI6b YL0g YI0o
YI16 YI17 YI14 YI18 YI1a UI5c YI00 UI3u UI22 UI2u UI0l UI5m
YI5a UI23 YI0a YL00 YI05 UI5n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI5f UI5e UI5h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition lits_Config0 : list (option Z) := [None; Some 0; None; None; None; None; None; Some 0; Some 0; Some 0].
Definition lits_Config1 : list (option Z) := [None; Some ubs0_D_str_tmp_out_gif; None; None; None; None; None; Some 0; Some 0; Some 0].
Definition ss_lmain : sstate :=
mkSS L_MAIN sr_atoms
[ YP09.mkRegion (Some 2%nat) 8 144 8 144
([mkChunk 8 (CVal 8 (SOff 36 0)); mkChunk 16 (CVal 8 (SOff 37 0)); mkChunk 24 (CVal 8 (SOff 38 0))]
++ obj_chunks_gen (lay_shift 64 LAY_Config) 39 lits_Config0 ++ saved_chunks 32) ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + LIB_STACK - 144) (2^63 - 144) 4);
(8%nat, mkAF 0 100000000 0);
(36%nat, mkAF 4096 CEIL_MAX 0); (37%nat, mkAF 1 CEIL_MAX 0); (38%nat, mkAF 0 CEIL_MAX 0) ] [] []).
Definition ss_lmain_c : sstate := Eval vm_compute in ss_lmain.
Lemma lits_Config0_ok : forall pal0 attr gen W H ngp,
forall j z, nth_error lits_Config0 j = Some (Some z) -> nth_error [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0] j = Some z.
Proof using.
intros pal0 attr gen W H ngp j z Hj. do 10 (destruct j as [|j]; [cbn in Hj; first [discriminate Hj | injection Hj as <-; reflexivity] |]).
destruct j; discriminate Hj.
Qed.
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
Variables (regs0 : bvmap 5 word) (L : layout) (A : astate) (mem : word -> option byte) (md : Model) (b0 : rbound) (plen : Z) (K : lleaf -> TSet).
Hypothesis HSORT : Fs.fs_sorted (m_fs md) = true.
Hypothesis HK : forall fs' c', leaf_post API regs0 L A mem md (ff_delta plen b0) fs' c' -> realizes ubs0segs c' (K (LL 0 fs' [])).
Hypothesis HROOM : ff_room b0 plen.
Hypothesis HFD : fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None.
Lemma llvm_main_x :
forall (regs1 : bvmap 5 word) Lc Ac memc mdc
(pdata nb cur pal0 attr gen W H ngp : Z) (PAYLOAD GPAL : list Z) (bc : rbound),
journal ubs0_msyms MR LIB_STACK (spZ regs0) [] L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs0 1) -> getr regs0 4 = Z_to_bv 64 (ms_tp ubs0_msyms) -> spZ regs0 mod 16 = 0 ->
In (pdata, nb) (blocks L A) -> 0 < nb ->
Permutation (blocks Lc Ac) ((if Z.land attr 4 =? 0 then [(pal0, 3 * ngp)] else []) ++ blocks L A) ->
(Z.land attr 4 <> 0 -> pal0 = 0) ->
(In (pal0, 3 * ngp) (blocks L A) -> 3 * ngp <= 0) ->
W * H <= 100000000 ->
obj_at ubs0segs memc (spZ regs0 - 80) LAY_Config [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0] ->
saved_ok memc (spZ regs0) regs0 ->
word_mem ubs0segs memc (spZ regs0 - 136) pdata -> word_mem ubs0segs memc (spZ regs0 - 128) nb ->
word_mem ubs0segs memc (spZ regs0 - 120) cur -> 0 <= cur <= nb ->
getr regs1 2 = Z_to_bv 64 (spZ regs0 - 144) -> getr regs1 8 = Z_to_bv 64 (W * H) ->
untouched_ok regs0 regs1 ->
sink_none ubs0_msyms mem md -> spZ regs0 <= 2 ^ 47 ->
garr8 ubs0segs mem pdata PAYLOAD -> Z.of_nat (length PAYLOAD) = nb ->
hdr5 PAYLOAD = (false, (W, H, attr, gen, ngp), skipn 14 PAYLOAD) ->
cur = 14 + (if Z.land attr 4 =? 0 then 3 * ngp else 0) -> 0 <= ngp ->
(Z.land attr 4 = 0 -> 14 + 3 * ngp <= Z.of_nat (length PAYLOAD) /\ GPAL = firstn (Z.to_nat (3 * ngp)) (skipn 14 PAYLOAD)) ->
(Z.land attr 4 <> 0 -> GPAL = []) ->
(Z.land attr 4 = 0 -> garr8 ubs0segs memc pal0 GPAL /\ Z.of_nat (length GPAL) = 3 * ngp) ->
res_ok Ac bc -> rb_le bc (main_bud b0) ->
realizes ubs0segs (mkCfg (mkst regs1 (Z_to_bv 64 L_MAIN) memc (seg_rom ubs0segs)) mdc)
(if g_opens (newgif_cfg W H attr gen ngp GPAL)
then openat_shape (m_fs md) (ff_unl K (m_fs md))
(ff_unl K (Fs.fs_set (m_fs md) sink_path (bytes (ff_content (newgif_cfg W H attr gen ngp GPAL) 0 (skipn (Z.to_nat cur) PAYLOAD)))))
else ff_unl K (m_fs md)).
Proof using ADDF CLOSE HFD HK HROOM HSORT IMG LAWS NEWGIF RFC UNLINK.
intros regs1 Lc Ac memc mdc pdata nb cur pal0 attr gen W H ngp PAYLOAD GPAL bc
HJ Hid Hra0 Htp0 Hal16 Hpd Hnb HB Hpal00 Hpalfresh HWH Hcfg HSV Wp Wn Wc Hcur G2 G8 HUT
HSN0 Hsp47 HPL HPLn HHDR HcurV Hngp0 HGPs HGPn HGP HRES HBLE.
set (G := newgif_cfg W H attr gen ngp GPAL). apply realizes_via_SR.
pose proof HUT as (G3 & G4 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HLSv : LIB_STACK = 16384) by reflexivity.
assert (HNSv : NEWGIF_STK = 9216) by reflexivity. assert (HRSv : RFC_STK = 8272) by reflexivity. assert (HALv : ALLOC_STACK = 8192) by reflexivity.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH0.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _).
set (sp0 := spZ regs0) in *.
assert (Hspm : (sp0 - 144) mod 16 = 0) by (replace (sp0 - 144) with (sp0 + (-9) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
assert (Hcf8 : (sp0 - 112) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 112) with ((2 * (sp0 / 16) - 14) * 8) by lia. apply Z_mod_mult. }
assert (Hcf8' : (sp0 - 136) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 136) with ((2 * (sp0 / 16) - 17) * 8) by lia. apply Z_mod_mult. }
assert (Hcg8 : (sp0 - 80) mod 8 = 0).
{ pose proof (proj2 (Z.div_exact sp0 16 ltac:(lia)) Hal16) as E16. replace (sp0 - 80) with ((2 * (sp0 / 16) - 10) * 8) by lia. apply Z_mod_mult. }
assert (Hpdc : In (pdata, nb) (blocks Lc Ac)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. exact Hpd. }
destruct (blocks_range _ _ LAWS Lc Ac memc mdc pdata nb HH0 Hpdc) as [Hp0 Hp1].
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
assert (HN0 : 0 <= W * H) by (pose proof (Rcfg 4%nat W eq_refl) as RW; pose proof (Rcfg 5%nat H eq_refl) as RH; cbn in RW, RH; nia).
set (cvals := [pal0; 0; attr; gen; W; H; ngp; 0; 0; 0]) in *.
set (E := Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs1 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HSV' : forall j v, nth_error (saved_vals regs0) j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HY : forall j v, nth_error ([pdata; nb; cur] ++ cvals) j = Some v -> ew E (36 + j) = Z_to_bv 64 v).
{ intros j v Hj. subst E. replace (36 + j)%nat with (32 + (length (saved_vals regs0) + j))%nat by reflexivity. apply Ereg_vals2. exact Hj. }
assert (HCV : forall j v, nth_error cvals j = Some v -> ew E (39 + j) = Z_to_bv 64 v).
{ intros j v Hj. replace (39 + j)%nat with (36 + (3 + j))%nat by lia. apply HY. exact Hj. }
assert (HW32 : ew E 32 = getr regs0 1) by (etransitivity; [apply (HSV' 0%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW33 : ew E 33 = getr regs0 8) by (etransitivity; [apply (HSV' 1%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW34 : ew E 34 = getr regs0 9) by (etransitivity; [apply (HSV' 2%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HW35 : ew E 35 = getr regs0 18) by (etransitivity; [apply (HSV' 3%nat); reflexivity | apply Z_to_bv_bv_unsigned]).
assert (HU2 : bv_unsigned (ew E 2) = sp0 - 144) by (rewrite (HE 2%nat 2%bv eq_refl), G2; apply unsigned_lit_small; lia).
assert (HU8 : bv_unsigned (ew E 8) = W * H) by (rewrite (HE 8%nat 8%bv eq_refl), G8; apply unsigned_lit_small; lia).
assert (HX36 : ew E 36 = Z_to_bv 64 pdata) by (apply (HY 0%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 nb) by (apply (HY 1%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 cur) by (apply (HY 2%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 pal0) by (apply (HCV 0%nat); reflexivity).
pose proof HSV as (W1 & W8 & W9 & W18).
assert (HS : st_ok ubs0segs E ss_lmain_c (mkst regs1 (Z_to_bv 64 L_MAIN) memc (seg_rom ubs0segs))).
{ change ss_lmain_c with ss_lmain. unfold ss_lmain. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia. }
apply Forall_app; split; [|apply Forall_app; split].
+ apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pdata); [cbn [sv_denot]; rewrite Z.add_0_r, HX36, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 8) with (sp0 - 136) by lia; apply val_mem_word_mem; exact Wp]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ nb); [cbn [sv_denot]; rewrite Z.add_0_r, HX37, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 16) with (sp0 - 128) by lia; apply val_mem_word_mem; exact Wn]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ cur); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | replace (sp0 - 144 + 24) with (sp0 - 120) by lia; apply val_mem_word_mem; exact Wc]. }
apply Forall_nil.
+ eapply (obj_chunks_gen_ok ubs0segs _ _ (sp0 - 144) _ cvals 39 lits_Config0); [| reflexivity | | apply lits_Config0_ok].
* apply (proj1 (obj_at_shift _ _ (sp0 - 144) 64 LAY_Config cvals)). replace (sp0 - 144 + 64) with (sp0 - 80) by lia. exact Hcfg.
* intros j v Hj. apply (HCV j v Hj).
+ assert (CK : forall off j (w : Z), nth_error (saved_vals regs0) j = Some w -> word_mem ubs0segs memc (sp0 - 144 + off) w -> 0 <= w < 2 ^ 64 ->
chunk_ok ubs0segs (Ereg regs1 (map (Z_to_bv 64) (saved_vals regs0) ++ map (Z_to_bv 64) ([pdata; nb; cur] ++ cvals) ++ [])) memc (sp0 - 144) (mkChunk off (CVal 8 (SOff (32 + j) 0)))).
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
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2, HU8, HX36, HX37, HX38, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
change memc with (ms_mem (mkst regs1 (Z_to_bv 64 L_MAIN) memc (seg_rom ubs0segs))) in HJ.
assert (Hbase : forall b, In b (blocks L A) -> In b (blocks Lc Ac)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB|]. apply in_app_iff. right. exact Hb. }
jrun_to LAWS ubs0tbl_ok HS HJ ubs0_A_cgif_newgif.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ha10. rewrite HU2 in Ha10.
jreg HS (2%bv:reg) as Ha2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Ha2.
jreg HS (4%bv:reg) as Ha4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Ha4.
jreg HS (1%bv:reg) as Ha1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp : spZ (ms_regs msx) = sp0 - 144) by (unfold spZ; rewrite Ha2; apply unsigned_lit_small; lia) end.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hcfg1 : obj_at ubs0segs (ms_mem msx) (sp0 - 80) LAY_Config [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; 0; 0; 0])
end.
{ replace (sp0 - 80) with (sp0 - 144 + 64) by lia. apply (proj2 (obj_at_shift _ _ (sp0 - 144) 64 LAY_Config _)).
eapply (st_obj_at ubs0segs _ _ _ 0%nat _ 2%nat (sp0 - 144) _ _ 39 lits_Config1 HS eq_refl eq_refl HU2);
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj.
assert (Hlj : (j < 10)%nat) by (destruct (Nat.lt_ge_cases j 10) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None [pal0; ubs0_D_str_tmp_out_gif; attr; gen; W; H; ngp; 0; 0; 0] j) Hl) in Hj; discriminate).
split.
{ destruct (Nat.eq_dec j 1) as [->|Hne].
- cbn in Hj. injection Hj as <-. cbn. unfold ubs0_D_str_tmp_out_gif. lia.
- replace (nth j (lay_shift 64 LAY_Config) (0, 8%N)).2 with (nth j LAY_Config (0, 8%N)).2 by (do 10 (destruct j as [|j]; [reflexivity|]); reflexivity).
apply (Rcfg j v). subst cvals. do 10 (destruct j as [|j]; [first [exact Hj | exfalso; lia] |]). exfalso; lia. }
do 10 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn [nth_error lits_Config1]; first [reflexivity | apply HCV; reflexivity] |]). exfalso; lia. }
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (HSNc : sink_none ubs0_msyms (ms_mem msx) mdc) by (exact (nil_sink_none API _ _ _ _ _ _ _ _ _ _ HJ HSN0)) end.
pose proof (nil_fs API _ _ _ _ _ _ _ _ _ _ HJ) as Hfs0.
assert (Hfd0 : m_fds mdc = m_fds md) by (pose proof HJ as (_ & Hos0 & _); exact (proj1 (os_step_shielded _ _ _ Hos0 ltac:(intros (r & [] & _))))).
apply (journal_nil_token API) in HJ.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
lazymatch type of Ha1 with getr _ _ = ?raw =>
assert (POST_CALL : forall L4 A4 (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) (res : Z) (T' : TSet),
journal ubs0_msyms MR LIB_STACK sp0 [sink_token] L A mem md L4 A4 mem4 md4 ->
journal ubs0_msyms MR NEWGIF_STK (sp0 - 144) [sink_token] Lc Ac mm mdc L4 A4 mem4 md4 ->
regs_preserved rg regs4 -> getr regs4 10 = Z_to_bv 64 res -> st_init_done A4 = true -> res_ok A4 (newgif_rb bc) ->
((res = 0 /\ Permutation (blocks L4 A4) (blocks Lc Ac) /\ sink_none ubs0_msyms mem4 md4 /\ m_fs md4 = m_fs md /\
T' = ff_unl K (m_fs md)) \/
(res = 0 /\ Permutation (blocks L4 A4) (blocks Lc Ac) /\ sink_none ubs0_msyms mem4 md4 /\
Fs.fs_lookup (m_fs md4) sink_path = Some (bytes []) /\ T' = ff_unl K (Fs.fs_set (m_fs md) sink_path (bytes []))) \/
(res <> 0 /\ exists s, cgif_at mem4 res s /\ cgif_wf s (W * H) /\
Permutation (blocks L4 A4) (cgif_blocks res s (W * H) ++ blocks Lc Ac) /\
cg_W s = W /\ cg_H s = H /\ cg_attr s = attr /\ cg_gen s = gen /\ cg_ngp s = ngp /\
cgif_rel mem4 md4 s (W * H) GPAL (gs0 G 0) /\
Z.of_nat (length (concat (YO07.s_out (gs0 G 0)))) <= HDR_OUT /\
T' = ff_unl K (Fs.fs_set (m_fs md) sink_path (bytes (ff_file G 0 (skipn (Z.to_nat cur) PAYLOAD)))))) ->
SR ubs0segs (mkCfg (mkst regs4 raw mem4 (seg_rom ubs0segs)) md4) (fun c1 => realizes ubs0segs c1 T'))
end end.
{ intros L4 A4 regs4 mem4 md4 res T' HJ4 HJc4 HP4 Hr10 Hid4' HR4 ALT.
pose proof HJc4 as (_ & _ & Hhi4 & _).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
jafter_call_keep HS 55%nat regs4 mem4 HP4 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [exact HU2 | exact Hhi4 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq59. cbn [ms_regs mkst] in Hq59. rewrite Hr10 in Hq59. symmetry in Hq59.
assert (HX : exists X, Permutation (blocks L4 A4) (X ++ blocks Lc Ac)).
{ destruct ALT as [(_ & Hl & _) | [(_ & Hl & _) | (_ & s & _ & _ & Hb & _)]]; [exists []; exact Hl | exists []; exact Hl | eexists; exact Hb]. }
destruct HX as [X HB4].
jrun_to LAWS ubs0tbl_ok HS HJ4 ubs0_A_free.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hc10. rewrite HX39 in Hc10.
jreg HS (2%bv:reg) as Hc2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hc2.
jreg HS (4%bv:reg) as Hc4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hc4.
jreg HS (1%bv:reg) as Hc1.
lazymatch goal with |- SR _ (mkCfg ?msq ?mdq) _ =>
eapply SR_bind with (R := fun c' => exists L6 A6 regs6 mem6 md6,
c' = mkCfg (mkst regs6 (Z_to_bv 64 (ubs0_A_LLVMFuzzerTestOneInput + 0x13c)) mem6 (seg_rom ubs0segs)) md6 /\
journal ubs0_msyms MR LIB_STACK sp0 [sink_token] L A mem md L6 A6 mem6 md6 /\
regs_preserved (ms_regs msq) regs6 /\ Permutation (blocks L6 A6) (X ++ blocks L A) /\
(forall b m i, In (b, m) (blocks L6 A6) -> 0 <= i < m -> mbyte ubs0segs mem6 (b + i) = mbyte ubs0segs (ms_mem msq) (b + i)) /\
(forall x, alloc_ceiling <= x < 2 ^ 64 -> ~ (sp0 - 144 - ALLOC_STACK <= x < sp0 - 144) ->
mbyte ubs0segs mem6 x = mbyte ubs0segs (ms_mem msq) x /\ (writable_at ubs0segs (ms_mem msq) x <-> writable_at ubs0segs mem6 x)) /\
(sink_none ubs0_msyms (ms_mem msq) md4 -> sink_none ubs0_msyms mem6 md6) /\ m_fs md6 = m_fs md4 /\
(forall f S, In (f, FILE_BLOCK) X -> sink_at ubs0_msyms (ms_mem msq) md4 f S -> sink_at ubs0_msyms mem6 md6 f S /\ In (f, FILE_BLOCK) (blocks L6 A6)) /\
res_ok A6 (main_bud2 b0))
end.
{ destruct (Z.eqb_spec (Z.land attr 4) 0) as [Hz|Hz].
-
cbn [app] in HB.
assert (Hpal4 : In (pal0, 3 * ngp) (blocks L4 A4)).
{ eapply Permutation_in; [apply Permutation_sym; exact HB4|]. apply in_or_app. right. eapply blocks_perm_in; [exact HB | left; reflexivity]. }
destruct (blocks_range _ _ LAWS L4 A4 mem4 md4 pal0 (3 * ngp) HH4 Hpal4) as [Hp40 Hp41].
eapply SR_mono.
{ eapply (jfree_tmp_tok_res API IMG) with (a := pal0) (n := 3 * ngp) (spc := sp0 - 144);
[ exact HS | reflexivity | reflexivity | exact HJ4 | exact Hid4' | exact Hpal4 | | exact HR4 | exact Hc10
| exact Hc2 | lia | exact Hspm | lia | lia | exact Hc4 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity ].
intros Hin i Hi. pose proof (Hpalfresh Hin). lia. }
intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HJl6 & Hid6 & HP6 & Hrm6 & Hkeep6 & Hhi6 & HR6).
exists L6, A6, regs6, mem6, md6. split; [reflexivity|]. split; [exact HJ6|]. split; [exact HP6|].
split.
{ eapply perm_after_rm1; [| exact Hrm6]. eapply Permutation_trans; [exact HB4|].
eapply Permutation_trans; [apply Permutation_app_head; exact HB|]. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
split; [exact Hkeep6|]. split; [exact Hhi6|].
assert (Hnl : ~ sink_open_fp [(pal0, pal0 + 3 * ngp)]) by (intros (r & [<- | []] & Hr); cbn [fst snd] in Hr; lia).
pose proof HJl6 as (_ & Hos6 & _). destruct (os_step_shielded _ _ _ Hos6 Hnl) as (Efd6 & Efs6 & _).
split; [intros HSNq; eapply (sink_none_kept ubs0_msyms MR); [exact HJl6 | exact Hnl | exact HSNq]|]. split; [exact Efs6|].
assert (HPm4 : Permutation (blocks L4 A4) ((pal0, 3 * ngp) :: X ++ blocks L A)).
{ eapply Permutation_trans; [exact HB4|]. eapply Permutation_trans; [apply Permutation_app_head; exact HB|]. cbn [app]. apply Permutation_sym. apply Permutation_middle. }
split.
{ intros f S Hf HSK. eapply (sink_kept ubs0_msyms MR); [exact HJl6 | exact Hnl | | | exact HSK].
+ eapply Permutation_in; [apply Permutation_sym; exact HB4 | apply in_or_app; left; exact Hf].
+ intros x Hx (r & [<- | []] & Hr). cbn [fst snd] in Hr.
destruct (heap_sep_perm _ _ LAWS L4 A4 mem4 md4 (pal0, 3 * ngp) _ (f, FILE_BLOCK) HH4 HPm4 ltac:(apply in_or_app; left; exact Hf)) as [H1|H1]; cbn [fst snd] in H1; lia. }
eapply res_ok_mono; [| exact HR6]. exact (main_to_bud2_free b0 bc (3 * ngp) HBLE).
-
rewrite (Hpal00 Hz) in Hc10. cbn [app] in HB.
destruct (heap_model _ _ LAWS _ _ _ _ (proj1 HJ4)) as (Hh4 & Hl4 & _).
eapply SR_mono; [eapply (jfree_null _ (aa_free_null API)); [exact HS | reflexivity | reflexivity | exact Hh4 | exact Hl4 | exact Hc10 | exact Hc1 | apply ret_ok_even; vm_compute; reflexivity] |].
intros c' ->. lazymatch goal with |- context [mkst (ms_regs ?m0) _ (ms_mem _) _] => exists L4, A4, (ms_regs m0), (ms_mem m0), md4 end.
split; [reflexivity|]. split; [exact HJ4|]. split; [intros rr _; reflexivity|].
split; [eapply Permutation_trans; [exact HB4|]; apply Permutation_app_head; exact HB|].
split; [intros; reflexivity|]. split; [intros x _ _; split; [reflexivity | tauto]|].
split; [intros H0; exact H0|]. split; [reflexivity|]. split.
{ intros f S Hf HSK. split; [exact HSK|]. eapply Permutation_in; [apply Permutation_sym; exact HB4 | apply in_or_app; left; exact Hf]. }
eapply res_ok_mono; [| exact HR4]. exact (main_to_bud2 b0 bc HBLE). }
cbv beta. intros c' (L6 & A6 & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HB6 & Hkeep6 & Hhi6 & HSNk & Hfs6 & HSKk & HR6'). clear HJ4.
cbn [ms_regs ms_mem mkst] in HSNk, HSKk.
cbn [ms_regs ms_mem mkst] in HP6, Hkeep6, Hhi6.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HH6.
jafter_call_keep HS 71%nat regs6 mem6 HP6 [0%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
eapply (region_kept_stack ubs0segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (9%bv:reg) as Hs1. cbn [ms_regs mkst] in Hs1.
destruct ALT as [(-> & HB4l & HSN4 & Hfs4 & ET) | [(-> & HB4l & HSN4 & HK4 & ET) | (Hres & s & Hat4 & Hwf & HB4' & HWs & HHs & Has & Hgs & Hns & HREL4 & HLEN4 & ET)]]; subst T'.
-
rewrite Hq59 in Hs1. pin_reg HS (9%bv:reg) 0 Hs1.
jrun_to LAWS ubs0tbl_ok HS HJ6 L_UNLINK.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_unlink_x API IMG UNLINK regs0 L A mem md b0 plen K HK rg L6 A6 mm md6 _ (main_bud2 b0)) end.
+ exact HJ6.
+ assert (Hp6 : In (pdata, nb) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6 | apply in_or_app; right; exact Hpd]).
apply blocks_In in Hp6 as (q & _ & Hq).
exact (init_done_of_block A6 (q, nb) (proj1 (proj2 HH6)) Hq).
+ exact Hra0. + exact Htp0. + exact Hal16.
+ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB6|]. apply in_or_app. right. exact Hb.
+ saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(reflexivity).
+ ut_tac HS HE.
+ apply (sink_none_frame ubs0_msyms mem6); [intros a Ha; pose proof (ubs0_env_addr_range a Ha) as Hea; mem_back ltac:(rewrite ?HU2) ltac:(lia) |].
apply HSNk. apply (sink_none_frame ubs0_msyms mem4); [intros a Ha; pose proof (ubs0_env_addr_range a Ha) as Hea; mem_back ltac:(rewrite ?HU2) ltac:(lia) | exact HSN4].
+ rewrite Hfs6. exact Hfs4.
+ exact HR6'.
+ apply (main_bud2_fin b0 plen). apply rb_le_refl.
-
rewrite Hq59 in Hs1. pin_reg HS (9%bv:reg) 0 Hs1.
jrun_to LAWS ubs0tbl_ok HS HJ6 L_UNLINK.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_unlink_x API IMG UNLINK regs0 L A mem md b0 plen K HK rg L6 A6 mm md6 _ (main_bud2 b0)) end.
+ exact HJ6.
+ assert (Hp6 : In (pdata, nb) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6 | apply in_or_app; right; exact Hpd]).
apply blocks_In in Hp6 as (q & _ & Hq).
exact (init_done_of_block A6 (q, nb) (proj1 (proj2 HH6)) Hq).
+ exact Hra0. + exact Htp0. + exact Hal16.
+ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HB6|]. apply in_or_app. right. exact Hb.
+ saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(reflexivity).
+ ut_tac HS HE.
+ apply (sink_none_frame ubs0_msyms mem6); [intros a Ha; pose proof (ubs0_env_addr_range a Ha) as Hea; mem_back ltac:(rewrite ?HU2) ltac:(lia) |].
apply HSNk. apply (sink_none_frame ubs0_msyms mem4); [intros a Ha; pose proof (ubs0_env_addr_range a Ha) as Hea; mem_back ltac:(rewrite ?HU2) ltac:(lia) | exact HSN4].
+ eapply (journal_fs_set API); [exact HJ6 | exact HSORT | rewrite Hfs6; exact HK4].
+ exact HR6'.
+ apply (main_bud2_fin b0 plen). apply rb_le_refl.
-
rename res into g.
assert (HXc : Permutation X (cgif_blocks g s (W * H))).
{ apply (Permutation_app_inv_r (blocks Lc Ac)). eapply Permutation_trans; [apply Permutation_sym; exact HB4 | exact HB4']. }
assert (HB6' : Permutation (blocks L6 A6) (cgif_blocks g s (W * H) ++ blocks L A)).
{ eapply Permutation_trans; [exact HB6|]. apply Permutation_app_tail. exact HXc. }
assert (Hg6 : In (g, CGIF_SIZE) (blocks L6 A6)) by (eapply blocks_perm_in; [exact HB6' | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L6 A6 mem6 md6 g CGIF_SIZE HH6 Hg6 ltac:(unfold CGIF_SIZE; lia)) as (Hg0 & Hg1 & Hg16). unfold CGIF_SIZE in Hg1.
pose proof Hwf as (Hlen3 & HW1 & HH1 & HN & HNle & Hngp & Hih & Hfwf).
assert (HN1 : 1 <= W * H) by nia. assert (HNr : 1 <= W * H <= 100000000) by (clear - HN1 HWH; lia).
rewrite Hq59 in Hs1.
assert (Hq59' : bv_unsigned (ew (havoc E 55 (map (getr regs4) CLOB)) 59) = g) by (rewrite Hq59; apply unsigned_lit_small; lia).
add_fact HS 59%nat (mkAF 4096 (CEIL_MAX - 96) 4).
2:{ ew_havocA. rewrite Hq59'. change (2 ^ 4) with 16. lia. }
assert (Hat6 : cgif_at mem6 g s).
{ eapply (cgif_at_kept _ _ g s (W * H) (blocks L6 A6) (blocks L A) HB6'); [| exact Hkeep6].
eapply (cgif_at_low API); [exact HH4 | exact HB4' | exact Hat4 |]. intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
assert (HGOF : gcfg_of s GPAL = G) by (subst G; unfold gcfg_of, newgif_cfg; rewrite HWs, HHs, Has, Hgs, Hns; reflexivity).
assert (HREL6 : cgif_rel mem6 md6 s (W * H) GPAL (gs0 G 0)).
{ lazymatch type of HSKk with (forall f S, _ -> sink_at _ ?mq _ _ _ -> _) =>
assert (HRELq0 : cgif_rel mq md4 s (W * H) GPAL (gs0 G 0))
by (eapply (cgif_rel_low API); [exact HH4 | exact HB4' | exact HREL4 |]; intros a Ha; mem_back ltac:(rewrite ?HU2) ltac:(lia)) end.
eapply (cgif_rel_resink _ mem6 md4 md6 g s (W * H) GPAL (gs0 G 0) (blocks L6 A6)); [exact HB6' | exact Hkeep6 | exact HRELq0 |].
apply (HSKk (cg_file s) (concat (YO07.s_out (gs0 G 0)))); [| exact (proj1 (proj2 HRELq0))].
eapply Permutation_in; [apply Permutation_sym; exact HXc | exact (proj1 (cgif_ghost_blocks g s (W * H)))]. }
jrun_to LAWS ubs0tbl_ok HS HJ6 ubs0_A_read_frameconfig.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Hd10. rewrite HU2 in Hd10. jreg HS (11%bv:reg) as Hd11. rewrite HU2 in Hd11.
jreg HS (12%bv:reg) as Hd12. rewrite (HE 8%nat 8%bv eq_refl), G8 in Hd12.
jreg HS (2%bv:reg) as Hd2. rewrite (HE 2%nat 2%bv eq_refl), G2 in Hd2.
jreg HS (4%bv:reg) as Hd4. rewrite (HE 4%nat 4%bv eq_refl), G4, Htp0 in Hd4. jreg HS (1%bv:reg) as Hd1.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hsp' : spZ (ms_regs msx) = sp0 - 144) by (unfold spZ; rewrite Hd2; apply unsigned_lit_small; lia) end.
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc].
assert (Hp6 : In (pdata, nb) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6' | apply in_or_app; right; exact Hpd]).
assert (Hid6 : st_init_done A6 = true).
{ pose proof Hp6 as Hp6'. apply blocks_In in Hp6' as (q & _ & Hq). exact (init_done_of_block A6 (q, nb) (proj1 (proj2 HH6)) Hq). }
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (HRELq : cgif_rel mm md6 s (W * H) GPAL (gs0 G 0))
by (eapply (cgif_rel_low API); [exact HH6 | exact HB6' | exact HREL6 |]; intros a Ha; mem_back ltac:(rewrite ?HU2) ltac:(lia));
assert (Hfin6' : In (cg_file s, FILE_BLOCK) (blocks L6 A6)) by (eapply Permutation_in; [apply Permutation_sym; exact HB6' | apply in_or_app; left; exact (proj1 (cgif_ghost_blocks g s (W * H)))]);
assert (HPLq : garr8 ubs0segs mm pdata PAYLOAD)
by (eapply (payload_kept API); [exact HJ6 | rewrite HPLn; exact Hpd | rewrite HPLn; exact Hp6 | exact inFP_token | exact HPL]);
pose proof (journal_restart ubs0_msyms MR _ _ _ _ _ _ _ _ _ _ _ [] HJ6) as HJr end.
eapply SR_bind.
{ lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (RFC LIB_STACK sp0 [] L6 A6 mm md6 L6 A6 mm md6 rg (cgif_blocks g s (W * H) ++ blocks L A) (sp0 - 136) (sp0 - 112) (W * H) pdata nb cur PAYLOAD (main_bud2 b0)) end.
+ exact HJr.
+ exact Hid6.
+ intros b Hb. eapply Permutation_in; [exact HB6' | exact Hb].
+ exact HB6'.
+ apply in_or_app. right. exact Hpd.
+ rewrite Hd1. apply ret_ok_even. vm_compute. reflexivity.
+ exact Hd4.
+ rewrite Hd10. f_equal. lia. + rewrite Hd11. f_equal. lia. + exact Hd12.
+ rewrite Hsp'. exact Hspm. + rewrite Hsp'. lia. + rewrite Hsp'. lia. + lia. + rewrite Hsp'. lia. + lia. + lia.
+ exact Hcf8'. + exact Hcf8. + lia. + lia. + exact Hcur. + exact Hnb.
+ stack_word HS HU2 36%nat HX36. lia.
+ replace (sp0 - 136 + 8) with (sp0 - 128) by lia. stack_word HS HU2 37%nat HX37. lia.
+ replace (sp0 - 136 + 16) with (sp0 - 120) by lia. stack_word HS HU2 38%nat HX38. lia.
+ exact HPLq. + exact HPLn. + exact HR6'.
+ eapply (main_rfc_room b0 plen HROOM (W * H) HNr). apply rb_le_refl. }
cbv beta. intros c' (L7 & A7 & regs7 & mem7 & md7 & res & cur2 & -> & HJ7r & Hid7 & HP7 & Hr10' & Hfr7 & Hbb7 & Wp7 & Wn7 & Wc7 & Hcur7 & ALT).
cbn [ms_regs ms_mem mkst] in HP7, Hfr7, Hbb7, Hr10', HJ7r.
assert (HJ7 : journal ubs0_msyms MR LIB_STACK sp0 [sink_token] L A mem md L7 A7 mem7 md7).
{ eapply (journal_sub_gen ubs0_msyms MR LAWS); [exact HJ6 | exact HJ7r | lia | lia | intros a0 (r & [] & _)]. }
assert (HSK7 : sink_at ubs0_msyms mem7 md7 (cg_file s) (concat (YO07.s_out (gs0 G 0))) /\ In (cg_file s, FILE_BLOCK) (blocks L7 A7)).
{ eapply (sink_kept ubs0_msyms MR); [exact HJ7r | intros (r & [] & _) | exact Hfin6' | intros x Hx (r & [] & _) | exact (proj1 (proj2 HRELq))]. }
assert (HREL7 : cgif_rel mem7 md7 s (W * H) GPAL (gs0 G 0)).
{ eapply (cgif_rel_resink _ mem7 md6 md7 g s (W * H) GPAL (gs0 G 0) (cgif_blocks g s (W * H) ++ blocks L A) (blocks L A) (Permutation_refl _)); [exact Hbb7 | exact HRELq | exact (proj1 HSK7)]. }
clear HJ6 HJr HRELq.
rewrite Hsp' in Hfr7. rewrite Hd1.
lazymatch type of HS with st_ok _ ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_after_call ubs0segs 100 E1 ss1 ms1 regs7 mem7
[YP09.mkRegion (Some 2%nat) 64 144 64 144 (saved_chunks 32)] (ubs0_A_LLVMFuzzerTestOneInput + 0x150) HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(apply submem_keep; [| apply submem_nil]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|]; split; [cbn; lia|];
apply incl_chunks_sound; vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) HP7) as HS2;
let ss2 := eval vm_compute in (ss_after_call ss1 [YP09.mkRegion (Some 2%nat) 64 144 64 144 (saved_chunks 32)] 100 (ubs0_A_LLVMFuzzerTestOneInput + 0x150)) in
change (ss_after_call ss1 _ 100 _) with ss2 in HS2 end.
match type of HS2 with ?P -> _ => assert (HK2 : P); [|specialize (HS2 HK2); clear HK2] end.
{ constructor; [|constructor].
split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite HU2; intros a Ha.
- apply Hfr7; lia.
- intros _. apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7). lia. }
clear HS. rename HS2 into HS.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ7) as HH7.
assert (Hat7 : cgif_at mem7 g s).
{ eapply (cgif_at_kept _ _ g s (W * H) (cgif_blocks g s (W * H) ++ blocks L A) (blocks L A) (Permutation_refl _)); [| exact Hbb7].
eapply (cgif_at_low API); [exact HH6 | exact HB6' | exact Hat6 |]. intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia). }
destruct ALT as [(-> & HPFf & (leak & HB7) & HR7) | (-> & lpal' & lpa' & img' & fattr' & fgen' & delay' & nlp' & tidx' & LPALV' & IMGV' & Hfc7 & Hlp07 & Hlpa7 & HB7 & HPFN & HGI7 & HGIn7 & HGL7 & HR7)].
+
pin_reg HS (10%bv:reg) 0 Hr10'.
jrun_to LAWS ubs0tbl_ok HS HJ7 L_CLOSE.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
assert (HPFf' : fst (fst (parse_frame G (skipn (Z.to_nat cur) PAYLOAD))) = false) by (subst G; unfold parse_frame, newgif_cfg; cbn [YO07.g_w YO07.g_h]; exact HPFf).
rewrite ff_file_loop, (loop_file_stop G 16 (gs0 G 0) _ HPFf').
change (loop_file G 0 (gs0 G 0) (skipn (Z.to_nat cur) PAYLOAD)) with (concat (YO07.close_gif G (gs0 G 0)) ++ [59]).
replace (YO07.close_gif G (gs0 G 0)) with (YO07.close_gif (gcfg_of s GPAL) (gs0 G 0)) by (rewrite HGOF; reflexivity).
destruct (main_rfc_fail b0 plen HROOM (W * H) HNr (main_bud2 b0) (rb_le_refl _)) as [HCR7 HCF7].
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_close_x API IMG CLOSE UNLINK regs0 L A mem md b0 plen K HSORT HK rg L7 A7 mm md7 g s (W * H) (leak ++ blocks L A) GPAL (gs0 G 0) _) end.
* exact HJ7. * exact Hid7. * exact Hra0. * exact Htp0. * exact Hal16. * exact Hsp47.
* eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |].
{ eapply Permutation_trans; [exact HB7 | apply Permutation_app_swap_app]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* exact Hwf.
* eapply Permutation_trans; [exact HB7 | apply Permutation_app_swap_app].
* intros b Hb. apply in_app_iff. right. exact Hb.
* exists (pdata, nb). split; [exact Hpd | cbn; lia].
* saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite Hq59'; reflexivity).
* ut_tac HS HE.
* eapply (cgif_rel_low API); [exact HH7 | | exact HREL7 |].
{ eapply Permutation_trans; [exact HB7 | apply Permutation_app_swap_app]. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* clear - HLEN4 HN1 HNle. unfold CLOSE_OUT, HDR_OUT, FRAME_OUT, SINK_MAX in *. lia.
* exact HR7. * exact HCR7. * exact HCF7.
+
assert (HPF7 : parse_frame G (skipn (Z.to_nat cur) PAYLOAD) = (true, (fattr', fgen', delay', tidx', nlp', LPALV', IMGV'), skipn (Z.to_nat cur2) PAYLOAD)).
{ subst G. unfold parse_frame, newgif_cfg. cbn [YO07.g_w YO07.g_h]. exact HPFN. }
assert (Himg7 : In (img', W * H) (blocks L7 A7)) by (eapply blocks_perm_in; [exact HB7 | left; reflexivity]).
destruct (blocks_range _ _ LAWS L7 A7 mem7 md7 img' (W * H) HH7 Himg7) as [Hi0' Hi1'].
assert (Hlpr' : Z.land fattr' 1 <> 0 -> 4096 <= lpa' /\ lpa' + 3 * nlp' <= alloc_ceiling).
{ intros Hf1. eapply (blocks_range _ _ LAWS); [exact HH7|]. eapply blocks_perm_in; [exact HB7|].
right. apply in_or_app. left. destruct (Z.eqb_spec (Z.land fattr' 1) 0) as [E0|E0]; [exfalso; exact (Hf1 E0)|]. left. reflexivity. }
pin_reg HS (10%bv:reg) 1 Hr10'.
jrun_to LAWS ubs0tbl_ok HS HJ7 L_LH.
{ eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_nil. }
rewrite (st_ok_mkst ubs0segs _ _ _ HS eq_refl). cbn [ss_pc]. apply SR_here.
rewrite ff_file_loop, (loop_file_step G 15 (gs0 G 0) _ _ _ _ _ _ _ _ _ HPF7). change (loop_file G 15) with (loop_file G (Nat.pred 16)).
pose proof (obj_at_range _ _ _ _ _ Hfc7 5%nat nlp' eq_refl) as Hnlp'. cbn in Hnlp'.
lazymatch goal with |- realizes _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (llvm_loop_x API IMG CLOSE ADDF UNLINK RFC regs0 L A mem md b0 plen K HSORT HK HROOM 16 rg L7 A7 mm md7 g s (W * H) (blocks L A) pdata nb cur2 lpal' lpa' img' fattr' fgen' delay' nlp' tidx'
PAYLOAD GPAL IMGV' LPALV' G (gs0 G 0) (rfc_rb_ok (main_bud2 b0) fattr' nlp' (W * H))) end.
* lia. * exact HJ7. * exact Hid7. * exact Hra0. * exact Htp0. * exact Hal16. * exact Hsp47.
* eapply (cgif_at_low API); [exact HH7 | | exact Hat7 |].
{ eapply Permutation_trans; [exact HB7|].
change ((img', W * H) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')]) ++ cgif_blocks g s (W * H) ++ blocks L A)
with (((img', W * H) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')])) ++ (cgif_blocks g s (W * H) ++ blocks L A)).
apply Permutation_app_swap_app. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* exact Hwf.
* eapply Permutation_trans; [exact HB7|].
change ((img', W * H) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')]) ++ cgif_blocks g s (W * H) ++ blocks L A)
with (((img', W * H) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')])) ++ (cgif_blocks g s (W * H) ++ blocks L A)).
apply Permutation_app_swap_app.
* intros b Hb. exact Hb. * exact Hpd. * exact Hnb.
* saved_ok_tac HS HU2 HW32 HW33 HW34 HW35.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF2 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). apply Wp7. exact Hkk.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF2 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 128 + Z.of_nat kk) with (sp0 - 136 + 8 + Z.of_nat kk) by lia. apply Wn7. exact Hkk.
* intros kk Hkk. fold sp0. cbn [ms_mem mkst] in *. mb_frame_with HF2 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). replace (sp0 - 120 + Z.of_nat kk) with (sp0 - 136 + 16 + Z.of_nat kk) by lia. apply Wc7. exact Hkk.
* lia.
* fold sp0. eapply (obj_at_transport_range _ _ _ _ _ _ 32); [exact Hfc7 | reflexivity |]. intros i Hi. cbn [ms_mem mkst] in *.
mb_frame_with HF2 ltac:(lia) ltac:(ew_havocA; rewrite ?HU2; lia). reflexivity.
* exact Hlp07. * exact Hlpa7.
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite HU8; reflexivity).
* reg_nowF HS ltac:(rewrite Hq59'; reflexivity).
* reg_nowF HS ltac:(reflexivity).
* ut_tac HS HE.
* exact HPL. * exact HPLn.
* eapply (cgif_rel_low API); [exact HH7 | | exact HREL7 |].
{ eapply Permutation_trans; [exact HB7|].
change ((img', W * H) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')]) ++ cgif_blocks g s (W * H) ++ blocks L A)
with (((img', W * H) :: (if Z.land fattr' 1 =? 0 then [] else [(lpa', 3 * nlp')])) ++ (cgif_blocks g s (W * H) ++ blocks L A)).
apply Permutation_app_swap_app. }
intros a Ha. mem_back ltac:(rewrite ?HU2) ltac:(lia).
* clear - HLEN4 HN1. unfold HDR_OUT, FRAME_OUT in *. lia.
* exact HGOF.
* eapply garr8_frame; [exact HGI7|]. intros a Ha. rewrite HGIn7 in Ha. cbn [ms_mem mkst] in *.
mb_frame_with HF2 ltac:(clear - Ha Hi0' Hi1' Hac; lia) ltac:(ew_havocA; rewrite ?HU2; clear - Ha Hi0' Hi1' Hac Hsp0al Hstk0 Hceil Hsp063 HLSv; lia). reflexivity.
* exact HGIn7.
* intros Hf1. destruct (HGL7 Hf1) as [HGL HGLn]. destruct (Hlpr' Hf1) as [Hl0' Hl1']. split; [|exact HGLn].
eapply garr8_frame; [exact HGL|]. intros a Ha. rewrite HGLn in Ha. cbn [ms_mem mkst] in *.
mb_frame_with HF2 ltac:(clear - Ha Hl0' Hl1' Hac; lia) ltac:(ew_havocA; rewrite ?HU2; clear - Ha Hl0' Hl1' Hac Hsp0al Hstk0 Hceil Hsp063 HLSv; lia). reflexivity.
* exact HR7.
* eapply (main_rfc_ok b0 (W * H) HNr); [apply rb_le_refl | clear - Hnlp'; lia]. }
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
assert (HPRE1 : fn_pre ubs0_msyms MR NEWGIF_STK Lc Ac rg mm mdc)
by (eapply (fn_pre_of_journal ubs0_msyms MR); [exact HJ | rewrite Ha1; apply ret_ok_even; vm_compute; reflexivity | rewrite Hsp; exact Hspm | lia | rewrite Hsp; lia | rewrite Hsp; lia | exact Ha4]) end.
apply SR_here.
set (TA := ff_unl K (m_fs md)). set (TB := ff_unl K (Fs.fs_set (m_fs md) sink_path (bytes (ff_content G 0 (skipn (Z.to_nat cur) PAYLOAD))))).
rewrite <- Hfs0.
eapply (NEWGIF Lc Ac _ _ mdc (sp0 - 80) pal0 pal0 attr gen W H ngp 0 (blocks L A) GPAL bc TA TB HPRE1 Hid);
[ rewrite Ha10; f_equal; lia | exact Hcg8 | rewrite Hsp; lia | lia | exact Hcfg1 | exact HSNc | rewrite Hsp; lia | exact HWH | reflexivity | exact HB
| | rewrite Hfd0; exact HFD | exact HRES | exact (main_newgif_room b0 plen HROOM bc HBLE) | | | ].
- intros Hz. destruct (HGP Hz) as [HG0 HGl]. split; [|exact HGl].
eapply garr8_frame; [exact HG0|]. intros a Ha. rewrite HGl in Ha.
assert (Hpr : 4096 <= pal0 /\ pal0 + 3 * ngp <= alloc_ceiling).
{ eapply (blocks_range _ _ LAWS); [exact HH0|]. eapply Permutation_in; [apply Permutation_sym; exact HB|]. rewrite (proj2 (Z.eqb_eq _ _) Hz). left. reflexivity. }
mem_back ltac:(rewrite ?HU2) ltac:(lia).
-
intros c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJc4 & HP4 & Hid4' & Hr10 & HB4l & HSN4 & Hfs4 & HR4). apply realizes_via_SR. rewrite Ha1.
cbn [ms_regs ms_mem mkst spZ] in HJc4, HP4. rewrite Hsp in HJc4 || (unfold spZ in HJc4; rewrite Ha2, unsigned_lit_small in HJc4 by lia).
eapply (POST_CALL L4 A4 regs4 mem4 md4 0 TA); [ | exact HJc4 | exact HP4 | exact Hr10 | exact Hid4' | exact HR4 | ].
+ eapply (journal_sub ubs0_msyms MR); [exact HJ | exact HJc4 | lia | lia | intros a Ha; split; [exact Ha | pose proof (inFP_token a Ha); lia]].
+ left. split; [reflexivity|]. split; [exact HB4l|]. split; [exact HSN4|]. split; [rewrite Hfs4; exact Hfs0 | reflexivity].
-
intros HSG c' (L4 & A4 & regs4 & mem4 & md4 & -> & HJc4 & HP4 & Hid4' & Hr10 & HB4l & HSN4 & HK4 & HR4). apply realizes_via_SR. rewrite Ha1.
cbn [ms_regs ms_mem mkst spZ] in HJc4, HP4. rewrite Hsp in HJc4 || (unfold spZ in HJc4; rewrite Ha2, unsigned_lit_small in HJc4 by lia).
eapply (POST_CALL L4 A4 regs4 mem4 md4 0 TB); [ | exact HJc4 | exact HP4 | exact Hr10 | exact Hid4' | exact HR4 | ].
+ eapply (journal_sub ubs0_msyms MR); [exact HJ | exact HJc4 | lia | lia | intros a Ha; split; [exact Ha | pose proof (inFP_token a Ha); lia]].
+ right. left. split; [reflexivity|]. split; [exact HB4l|]. split; [exact HSN4|]. split; [exact HK4|].
subst TB G. unfold ff_content. rewrite HSG. reflexivity.
-
intros HSG c' (L4 & A4 & regs4 & mem4 & md4 & res & s & -> & HJc4 & HP4 & Hid4' & Hr10 & Hres & Hat & Hwf & Hfr3 & HWs & HHs & Has & Hcur4 & Hih4 & Hgs & Hns & HB4 & HREL4 & HLEN4 & HR4).
apply realizes_via_SR. rewrite Ha1.
cbn [ms_regs ms_mem mkst spZ] in HJc4, HP4. rewrite Hsp in HJc4 || (unfold spZ in HJc4; rewrite Ha2, unsigned_lit_small in HJc4 by lia).
eapply (POST_CALL L4 A4 regs4 mem4 md4 res TB); [ | exact HJc4 | exact HP4 | exact Hr10 | exact Hid4' | exact HR4 | ].
+ eapply (journal_sub ubs0_msyms MR); [exact HJ | exact HJc4 | lia | lia | intros a Ha; split; [exact Ha | pose proof (inFP_token a Ha); lia]].
+ right. right. split; [exact Hres|]. exists s. subst TB G. unfold newgif_cfg in HSG |- *. rewrite gs0_gs_new. unfold ff_content. rewrite HSG.
cbn [YO07.g_w YO07.g_h YO07.g_attr YO07.g_ngp YO07.g_gpal].
repeat (split; [assumption|]). reflexivity.
Qed.
End S.
End c.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
