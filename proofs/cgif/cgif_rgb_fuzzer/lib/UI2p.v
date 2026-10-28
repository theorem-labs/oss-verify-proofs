(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c YP0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m YI00 YI02 YI01 YI03
UI1e UI39 UI1i UI59 UI56 YI0x UI2q UO3n UO0e.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition NG_WTEST : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0x2c).
Definition NG_M96RET : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0x84).
Definition NG_CPY : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0xc4).
Definition NG_PALRET : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0xe0).
Definition NG_PALCPY : Z := Eval vm_compute in (ubs2_A_cgif_newgif + 0xfc).
End c.
Ltac jafter_stretch_keep HS k regs2 mem2 clob newpc idxs HS2 :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss ?ms =>
let rs := eval vm_compute in (pick (ss_mem ss) idxs) in
pose proof (st_ok_after_stretch segs k E ss ms regs2 mem2 rs newpc clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
ltac:(vm_compute; reflexivity) ltac:(submem_tac) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as HS2;
let ss2 := eval vm_compute in (ss_after_stretch ss rs k clob newpc) in
change (ss_after_stretch ss rs k clob newpc) with ss2 in HS2
end.
Ltac add_region HS r :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
apply (st_ok_add_region segs E1 ss1 ms1 r) in HS;
[ match type of HS with st_ok _ _ ?ss2 _ => let v2 := eval vm_compute in ss2 in change ss2 with v2 in HS end
| vm_compute; reflexivity | | ]
end.
Ltac ew_havocA :=
repeat match goal with
| |- context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) by nat_lt_lit
end.
Ltac ew_havocA_in H :=
repeat match type of H with
| context [ew (havoc ?E0 ?k ?ws) ?n] => rewrite (ew_havoc_old E0 k ws n) in H by nat_lt_lit
end.
Ltac mem_back1 bases slv :=
match goal with
| HF : frame_of ?E ?rs ?m ?m' |- mbyte _ ?m' ?a = _ =>
mb_frame_with HF slv ltac:(ew_havocA; bases; slv)
| Hout : (forall x : word, bv_unsigned x < ?d \/ ?d + ?n <= bv_unsigned x -> ?m' x = ?m x) |- mbyte ?sg ?m' ?a = _ =>
unfold mbyte at 1; rewrite (Hout (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by slv; slv); fold (mbyte sg m a)
| Hhi : (forall x : Z, alloc_ceiling <= x < 2 ^ 64 -> ~ _ -> mbyte _ ?m' x = mbyte _ ?m x /\ _) |- mbyte _ ?m' ?a = _ =>
rewrite (proj1 (Hhi a ltac:(slv) ltac:(slv)))
end.
Ltac mem_back bases slv := cbn [ms_mem mkst] in *; repeat (reflexivity || mem_back1 bases slv).
Ltac frame_wordI HS idx HU2 HE n rr :=
lazymatch goal with |- word_mem _ _ (?spv - ?dd) (bv_unsigned ?w) =>
replace (spv - dd) with (spv + (- dd)) by lia;
eapply (st_chunk_word _ _ _ idx _ 2%nat (- dd) (SOff n 0) spv (bv_unsigned w) HS);
[ reflexivity | reflexivity | cbv; auto 20
| ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, (HE n rr eq_refl), Z_to_bv_bv_unsigned; reflexivity
| let Rw := fresh "Rw" in pose proof (bv_unsigned_in_range 64 w) as Rw; change (bv_modulus 64) with (2 ^ 64) in Rw; clear - Rw; lia ]
end.
Ltac cfg_field_atom Hj HX :=
cbn in Hj; injection Hj as <-; cbn [snd nth tl lits_Config nth_error lay_shift map fst Z.of_N];
split; [cbn; lia | ew_havocA; apply HX; reflexivity].
Ltac cfg_field_lit Hj :=
cbn in Hj; injection Hj as <-; cbn [snd nth tl lits_Config nth_error lay_shift map fst Z.of_N];
split; [first [lit_range | cbn; lia] | reflexivity].
Ltac cfg_fields_tac Hj HX :=
let j := lazymatch type of Hj with nth_error _ ?j = _ => j end in
destruct j as [|j]; [cfg_field_lit Hj|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_atom Hj HX|];
destruct j as [|j]; [cfg_field_lit Hj|];
destruct j as [|j]; [cfg_field_lit Hj|];
destruct j; discriminate Hj.
Ltac cgif_obj_tac HS Hg palE HpalE HX :=
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N)] ++ [(24, 8%N)] ++
lay_shift 24 [(8, 8%N); (16, 4%N); (20, 4%N); (24, 2%N); (26, 2%N); (28, 2%N); (30, 2%N); (32, 8%N); (40, 8%N)] ++
[(72, 8%N); (80, 8%N); (88, 4%N); (92, 4%N)]);
lazymatch goal with |- obj_at _ _ _ _ [0; 0; 0; ?pal'; 0; ?attr; ?gen; ?W; ?H; ?ngp; ?loops; ?wcb; 0; 0; 0; 0; 1] =>
change [0; 0; 0; pal'; 0; attr; gen; W; H; ngp; loops; wcb; 0; 0; 0; 0; 1]
with ([0; 0; 0] ++ [pal'] ++ [0; attr; gen; W; H; ngp; loops; wcb; 0] ++ [0; 0; 0; 1])
end;
rewrite obj_at_app by reflexivity; split;
[
cbn [obj_at]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
repeat split;
first [ eapply (st_chunk_zero_val _ _ _ _ 0%nat _ 53%nat 0 24 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | lia | cbn; lia]
| lit_range | lia ]
| rewrite obj_at_app by reflexivity; split;
[
cbn [obj_at]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
split; [split; [ eapply (st_chunk_val _ _ _ _ 0%nat _ 53%nat 24 8%N palE _ _ HS);
[reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HpalE, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia ]
| cbn; lia ] | exact I]
| rewrite obj_at_app by reflexivity; split;
[
eapply (st_obj_at _ _ _ _ 0%nat _ 53%nat _ _ _ 33 (tl lits_Config) HS eq_refl eq_refl ltac:(ew_havocA; exact Hg));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity
| let j := fresh "j" in let v := fresh "v" in let Hj := fresh "Hj" in
intros j v Hj; cfg_fields_tac Hj HX ]
|
cbn [obj_at]; unfold field_ok; cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N];
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 53%nat 72 8 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | lia | cbn; lia] | lit_range ] |];
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 53%nat 80 8%N (SLit 0) _ 0 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | reflexivity | lit_range | cbn; lia] | lit_range ] |];
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 53%nat 88 4 _ _ 4%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | lia | cbn; lia] | lit_range ] |];
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 53%nat 92 4%N (SLit 1) _ 1 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hg | reflexivity | lit_range | cbn; lia] | lit_range ] |];
exact I ] ] ].
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma denot_mul3 : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 1)) (SOff n 0)) = Z_to_bv 64 (3 * x).
Proof.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), U_SLit by lia. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (x * 2)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma denot_mul3' : forall E n x,
ew E n = Z_to_bv 64 x -> 0 <= x < 65536 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * x).
Proof.
intros E n x Hn Hx. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n x Hn), U_SLit by lia.
change (zcanon 3) with 3. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma land4_mod32 : forall x, Z.land x 4 = Z.land (x mod 2 ^ 32) 4.
Proof. intros x. rewrite <- (Z.land_ones x 32) by lia. rewrite <- Z.land_assoc. reflexivity. Qed.
Definition ss_newgif : sstate :=
mkSS ubs2_A_cgif_newgif sr_atoms
[ YQ0b.mkRegion (Some 2%nat) (-40) 0 (-40) 0 [];
YQ0b.mkRegion (Some 10%nat) 0 48 0 0 cfg_chunks ]
None
(mkFacts [ (2%nat, mkAF (CEIL_MIN + NEWGIF_STK) (2^63) 4);
(10%nat, mkAF CEIL_MIN (2^63 - 48) 3);
(34%nat, mkAF 0 (2^32 - 1) 0); (36%nat, mkAF 0 65535 0); (37%nat, mkAF 0 65535 0);
(38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0); (42%nat, mkAF 0 (2^32 - 1) 0) ] [] []).
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Ltac ret_regs HS HE :=
apply regs_preserved_intro; cbn [ms_regs mkst]; reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Ltac ret_pc HS HE Hra :=
cbn [ms_regs ms_mem mkst];
lazymatch type of HS with st_ok _ ?Ef ?ssf ?msf =>
let Q1 := fresh "Q1" in
pose proof (st_ok_reg ubs2segs Ef ssf msf 1%bv HS) as Q1; eval_sr_get_in Q1; cbn [sv_denot] in Q1;
repeat (rewrite ew_havoc_old in Q1; [|nat_lt_lit]); rewrite ?Z.add_0_r, Z_to_bv_bv_unsigned, (HE 1%nat (1%bv:reg) eq_refl) in Q1;
rewrite Q1, Hra; reflexivity end.
Ltac wr_tac3 HU2 :=
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
eapply wr_ok_cons_win; [reflexivity | ew_havocA; exact HU2 | cbn [r_wlo r_whi]; intros _; lia |];
apply wr_ok_cons_ro; [cbn; lia|]; apply wr_ok_nil.
Theorem ubs2_cgif_newgif :
forall L A (regs : bvmap 5 word) mem md (cfgp pal0 pala attr gen W H ngp loops : Z) (rest : list (Z * Z)),
fn_pre ubs2_msyms MR NEWGIF_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + 48 <= 2 ^ 63 ->
obj_at ubs2segs mem cfgp LAY_Config [pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] ->
W * H <= 100000000 ->
Z_to_bv 64 pala = Z_to_bv 64 pal0 ->
Permutation (blocks L A) ((if Z.land attr 4 =? 0 then [(pala, 3 * ngp)] else []) ++ rest) ->
SR ubs2segs (mkCfg (mkst regs (Z_to_bv 64 ubs2_A_cgif_newgif) mem (seg_rom ubs2segs)) md)
(newgif_post API regs L A mem md W H attr).
Proof.
intros L A regs mem md cfgp pal0 pala attr gen W H ngp loops rest HPRE Hid Ha0 Hcal Hclo Hchi Hcfg HWH Hpala HB.
pose proof HPRE as (HH & Hra & Hst & Htp & Herr).
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HASv : ALLOC_STACK = 8192) by reflexivity.
assert (HSTKv : NEWGIF_STK = 9216) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
destruct Hst as (Hal16 & Hstk0 & Hceil & H63 & Hstw).
set (sp0 := spZ regs) in *.
pose proof (obj_at_range _ _ _ _ _ Hcfg) as Rcfg.
pose proof (Rcfg 0%nat pal0 eq_refl) as Rpal0. pose proof (Rcfg 2%nat attr eq_refl) as Rattr. pose proof (Rcfg 3%nat gen eq_refl) as Rgen.
pose proof (Rcfg 4%nat W eq_refl) as RW. pose proof (Rcfg 5%nat H eq_refl) as RH. pose proof (Rcfg 6%nat ngp eq_refl) as Rngp.
pose proof (Rcfg 7%nat loops eq_refl) as Rloops.
cbn in Rpal0, Rattr, Rgen, RW, RH, Rngp, Rloops.
set (cvals := [pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0]) in *.
set (E := Ereg regs (map (Z_to_bv 64) cvals ++ map (Z_to_bv 64) [W + 65536 * H] ++ [])).
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (HX : forall j v, nth_error cvals j = Some v -> ew E (32 + j) = Z_to_bv 64 v) by (intros j v Hj; subst E; apply Ereg_vals; exact Hj).
assert (HX42 : ew E 42 = Z_to_bv 64 (W + 65536 * H)) by (subst E; apply (Ereg_vals2 regs cvals [W + 65536 * H] [] 0); reflexivity).
assert (HX32 : ew E 32 = Z_to_bv 64 pal0) by (apply (HX 0%nat); reflexivity).
assert (HX34 : ew E 34 = Z_to_bv 64 attr) by (apply (HX 2%nat); reflexivity).
assert (HX35 : ew E 35 = Z_to_bv 64 gen) by (apply (HX 3%nat); reflexivity).
assert (HX36 : ew E 36 = Z_to_bv 64 W) by (apply (HX 4%nat); reflexivity).
assert (HX37 : ew E 37 = Z_to_bv 64 H) by (apply (HX 5%nat); reflexivity).
assert (HX38 : ew E 38 = Z_to_bv 64 ngp) by (apply (HX 6%nat); reflexivity).
assert (HX39 : ew E 39 = Z_to_bv 64 loops) by (apply (HX 7%nat); reflexivity).
assert (HU2 : bv_unsigned (ew E 2) = sp0) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (HU10 : bv_unsigned (ew E 10) = cfgp) by (rewrite (HE 10%nat 10%bv eq_refl), Ha0; apply unsigned_lit_small; lia).
pose proof Hcfg as Hc. cbn [obj_at LAY_Config] in Hc. unfold field_ok in Hc. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N] in Hc.
destruct Hc as ((F0 & _) & (F1 & _) & (F2 & _) & (F3 & _) & (F4 & _) & (F5 & _) & (F6 & _) & (F7 & _) & (F8 & _) & (F9 & _) & _).
assert (HS : st_ok ubs2segs E ss_newgif (mkst regs (Z_to_bv 64 ubs2_A_cgif_newgif) mem (seg_rom ubs2segs))).
{ unfold ss_newgif. subst E. apply entry_st_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]].
+ apply (region_ok_stack ubs2segs _ mem 2 sp0); [exact HU2 | lia | lia | intros a Ha; apply Hstw; lia].
+ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. rewrite HU10.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
unfold cfg_chunks.
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ pal0); [cbn [sv_denot]; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F0]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lit_range | cbn; lia | exact F1]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ attr); [cbn [sv_denot]; rewrite Z.add_0_r, HX34, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F2]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ gen); [cbn [sv_denot]; rewrite Z.add_0_r, HX35, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F3]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ (W + 65536 * H)); [cbn [sv_denot]; rewrite Z.add_0_r, HX42, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | apply val_mem_wh_join; [exact F4 | replace (cfgp + 24 + 2) with (cfgp + 26) by lia; exact F5 | lia | lia]]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ngp); [cbn [sv_denot]; rewrite Z.add_0_r, HX38, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F6]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ loops); [cbn [sv_denot]; rewrite Z.add_0_r, HX39, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact F7]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ ubs2_A_writecb); [reflexivity | unfold ubs2_A_writecb; lit_range | cbn; lia | exact F8]. }
apply Forall_cons. { eapply (chunk_ok_val _ _ _ _ _ _ _ 0); [reflexivity | lit_range | cbn; lia | exact F9]. }
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val].
rewrite HU2, HU10. repeat split; lia.
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite HU2, HU10, HX34, HX36, HX37, HX38, HX39, HX42, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; assumption. }
pose proof (journal_init ubs2_msyms MR NEWGIF_STK [] L A regs mem md HPRE) as HJ.
change mem with (ms_mem (mkst regs (Z_to_bv 64 ubs2_A_cgif_newgif) mem (seg_rom ubs2segs))) in HJ.
fold sp0 in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ ubs2_A_memset.
{ eapply wr_ok_cons_win; [reflexivity | exact HU2 | cbn [r_wlo r_whi]; intros _; lia |]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil. }
jreg HS (10%bv:reg) as Ma0. rewrite HU2 in Ma0.
jreg HS (11%bv:reg) as Ma1. jreg HS (12%bv:reg) as Ma2. jreg HS (1%bv:reg) as Mra.
eapply SR_bind.
{ eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset E _ _ NEWGIF_STK sp0 [] L A mem md L A _ (sp0 - 80) 0 40);
[ exact HS | reflexivity | reflexivity | exact HJ | replace (sp0 - 80) with (sp0 + -80) by lia; exact Ma0 | exact Ma1 | exact Ma2 | exact Mra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply writable_off_img_present; [lia | unfold in_img1; lia | apply Hstw; lia].
- intros a Ha. left. lia. }
cbv beta. intros c' (regs2 & mem2 & -> & HJ2 & Hd10 & Hfr2 & Hout2 & Hgr2 & Hzero2). clear HJ.
jafter_stretch_keep HS 43%nat regs2 mem2 MEMSET_CLOB NG_WTEST [0%nat; 1%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr2. exact Hrr. }
{ constructor; [|constructor; [|constructor]].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU2; lia | cbn [r_base r_hi base_val]; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout2 | exact Hgr2 | cbn [r_base r_lo base_val]; rewrite HU10; lia | cbn [r_base r_hi base_val]; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
add_region HS (YQ0b.mkRegion (Some 2%nat) (-80) (-40) (-80) (-40) [mkChunk (-80) (CZero 40)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite HU2.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (writable_at_grows ubs2segs (ms_mem ms) mem2); [exact Hgr2|]. cbn [ms_mem mkst] in HG. apply (writable_at_grows ubs2segs mem (ms_mem ms)); [exact HG|]. apply Hstw. lia. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off]. intros i Hi.
replace (sp0 + -80 + i) with (sp0 - 80 + i) by lia. apply Hzero2. exact Hi. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite HU2, HU10. repeat split; lia. }
jrun LAWS ubs2tbl_ok HS HJ2. { wr_tac3 HU2. }
jbranch ubs2tbl HS.
{
jrun LAWS ubs2tbl_ok HS HJ2. { wr_tac3 HU2. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
unfold newgif_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L, A, (ms_regs msf), (ms_mem msf), md, 0 end.
split; [ret_pc HS HE Hra|]. split; [exact HJ2|]. split; [ret_regs HS HE|].
split; [reg_nowF HS ltac:(reflexivity)|]. left. split; [reflexivity|]. exists []. apply Permutation_refl. }
rewrite branch_eq_U, U_zext, U_lit, (U_atom _ 42 (W + 65536 * H)) in Hc by first [lia | ew_havocA; exact HX42].
change (2 ^ Z.of_N 16) with 65536 in Hc.
assert (HW1 : 1 <= W).
{ destruct (Z.eqb_spec ((W + 65536 * H) mod 65536) 0) as [Hz|Hz]; [discriminate Hc|].
rewrite Z.mul_comm, Z_mod_plus_full, Z.mod_small in Hz by lia. lia. }
clear Hc.
jrun LAWS ubs2tbl_ok HS HJ2. { wr_tac3 HU2. }
jbranch ubs2tbl HS.
{
jrun LAWS ubs2tbl_ok HS HJ2. { wr_tac3 HU2. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ2)))). }
unfold newgif_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L, A, (ms_regs msf), (ms_mem msf), md, 0 end.
split; [ret_pc HS HE Hra|]. split; [exact HJ2|]. split; [ret_regs HS HE|].
split; [reg_nowF HS ltac:(reflexivity)|]. left. split; [reflexivity|]. exists []. apply Permutation_refl. }
rewrite branch_eq_U, U_SAlu, U_lit, (U_atom _ 42 (W + 65536 * H)) in Hc by first [lia | ew_havocA; exact HX42].
cbn [zalu_raw] in Hc. rewrite ?U_SLit in Hc. change (Z.land 16 63) with 16 in Hc. change (zcanon 0) with 0 in Hc.
rewrite Z.shiftr_div_pow2 in Hc by lia. change (2 ^ 16) with 65536 in Hc.
replace ((W + 65536 * H) / 65536) with H in Hc by (rewrite Z.mul_comm, Z.div_add, Z.div_small by lia; lia).
rewrite zcanon_id in Hc by (unfold M64; lia).
assert (HH1 : 1 <= H) by (destruct (Z.eqb_spec H 0); [discriminate Hc | lia]). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ2 ubs2_A_malloc. { wr_tac3 HU2. }
jreg HS (10%bv:reg) as Hr10. jreg HS (2%bv:reg) as Hr2. rewrite HU2 in Hr2.
jreg HS (4%bv:reg) as Hr4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hr4. jreg HS (1%bv:reg) as Hr1.
assert (Hspm : (sp0 - 80) mod 16 = 0) by (replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 96) (spc := sp0 - 80);
[ exact HS | reflexivity | reflexivity | exact HJ2 | exact Hid | exact Hr10 | lia
| rewrite Hr2; f_equal; lia | lia | exact Hspm | lia | lia | exact Hr4 | exact Hr1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L2 & A2 & regs3 & mem3 & md3 & g & -> & HJ3 & Hid3 & HP3 & Hg10 & Hres & Hkeep3 & Hhi3). clear HJ2.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep3, Hhi3. cbn [ms_regs ms_mem mkst] in HP3, Hkeep3, Hhi3, HJ3.
jafter_call_keep HS 49%nat regs3 mem3 HP3 [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi3 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq53. cbn [ms_regs mkst] in Hq53. rewrite Hg10 in Hq53. symmetry in Hq53.
destruct Hres as [[-> Hbl] | (Hgnz & Hg16 & (b1 & b2 & Hbl2 & Hblc) & Hwr)].
{
pin_reg HS (10%bv:reg) 0 Hg10.
jrun LAWS ubs2tbl_ok HS HJ3. { wr_tac3 HU2. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ3)))). }
unfold newgif_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L2, A2, (ms_regs msf), (ms_mem msf), md3, 0 end.
split; [ret_pc HS HE Hra|]. split; [exact HJ3|]. split; [ret_regs HS HE|].
split; [reg_nowF HS ltac:(reflexivity)|]. left. split; [reflexivity|]. exists []. rewrite Hbl. apply Permutation_refl. }
assert (Hgin2 : In (g, CGIF_SIZE) (blocks L2 A2)) by (rewrite Hbl2; apply in_app_iff; right; left; reflexivity).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HH3.
destruct (heap_blocks_range _ _ LAWS L2 A2 mem3 md3 g CGIF_SIZE HH3 Hgin2 ltac:(lia)) as (Hg0 & Hg1 & _).
assert (Hgfresh : ~ In (g, CGIF_SIZE) (blocks L A)).
{ rewrite Hblc. apply (fresh_not_in API L2 A2 mem3 md3 b1 b2 g CGIF_SIZE HH3 Hbl2). lia. }
assert (Hbase2 : forall b, In b (blocks L A) -> In b (blocks L2 A2)).
{ intros b Hb. rewrite Hbl2. rewrite Hblc in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
add_fact HS 53%nat (mkAF 4096 (CEIL_MAX - CGIF_SIZE) 4).
2:{ rewrite Hq53, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
assert (Hq53' : bv_unsigned (ew (havoc (havoc E 43 (map (getr regs2) MEMSET_CLOB)) 49 (map (getr regs3) CLOB)) 53) = g) by (rewrite Hq53; apply unsigned_lit_small; lia).
jrun_to LAWS ubs2tbl_ok HS HJ3 ubs2_A_memset. { wr_tac3 HU2. }
jreg HS (10%bv:reg) as Mb0. rewrite Hq53 in Mb0. jreg HS (11%bv:reg) as Mb1. jreg HS (12%bv:reg) as Mb2. jreg HS (1%bv:reg) as Mbra.
eapply SR_bind.
{ lazymatch type of HS with st_ok _ ?E1 _ _ =>
eapply (jmemset ubs2_msyms MR LAWS IMG ubs2_A_memset ubs2_memset E1 _ _ NEWGIF_STK sp0 [] L A mem md L2 A2 _ g 0 96);
[ exact HS | reflexivity | reflexivity | exact HJ3 | exact Mb0 | exact Mb1 | exact Mb2 | exact Mbra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | | ] end.
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem3 md3 g CGIF_SIZE i HH3 Hgin2 ltac:(lia))).
- intros a Ha. right. right. exists g, CGIF_SIZE. split; [exact Hgin2|]. split; [exact Hgfresh | lia]. }
cbv beta. intros c' (regs4 & mem4 & -> & HJ4 & Hd10' & Hfr4 & Hout4 & Hgr4 & Hzero4). clear HJ3.
jafter_stretch_keep HS 65%nat regs4 mem4 MEMSET_CLOB (ubs2_A_cgif_newgif + 0x9c) [0%nat; 1%nat; 2%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr4. exact Hrr. }
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply region_kept_out; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU2; lia | cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU2; intros a Ha; lia | cbn; lia | cbn; lia].
- eapply region_kept_out; [exact Hout4 | exact Hgr4 | cbn [r_base r_lo base_val]; ew_havocA; rewrite HU10; lia | cbn [r_base r_hi base_val]; ew_havocA; rewrite HU10; lia | cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite HU10; intros a Ha; lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HH4.
add_region HS (YQ0b.mkRegion (Some 53%nat) 0 72 0 0 [mkChunk 0 (CZero 72)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq53, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off ms_mem mkst]. intros i Hi. rewrite Z.add_0_r. apply Hzero4. lia. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia. repeat split; lia. }
add_region HS (YQ0b.mkRegion (Some 53%nat) 72 96 72 96 [mkChunk 72 (CZero 24)]).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq53, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem4 md3 g CGIF_SIZE o HH4 Hgin2 ltac:(lia))). }
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. cbn [c_off ms_mem mkst]. intros i Hi. replace (g + 72 + i) with (g + (72 + i)) by lia. apply Hzero4. lia. }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia. repeat split; lia. }
jrun_to LAWS ubs2tbl_ok HS HJ4 ubs2_A_memcpy.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
wr_tac3 HU2. }
jreg HS (10%bv:reg) as Mc0. rewrite Hq53, unsigned_lit_small in Mc0 by lia. jreg HS (11%bv:reg) as Mc1. rewrite (HE 10%nat 10%bv eq_refl), Ha0 in Mc1.
jreg HS (12%bv:reg) as Mc2. jreg HS (1%bv:reg) as Mcra.
lazymatch goal with |- SR _ (mkCfg ?msx _) _ =>
assert (Hcfg1 : obj_at ubs2segs (ms_mem msx) cfgp LAY_Config cvals)
end.
{ eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg | reflexivity |]. intros i Hi.
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia) ltac:(lia). }
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs2_memcpy) with (d := g + 24) (src := cfgp) (n := 48);
[ exact HS | reflexivity | reflexivity | exact HJ4 | exact Mc0 | exact Mc1 | exact Mc2 | exact Mcra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | lia | lia | lia | | | lia | ].
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
replace (g + 24 + i) with (g + (24 + i)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem4 md3 g CGIF_SIZE (24 + i) HH4 Hgin2 ltac:(lia))).
- apply (obj_at_readable _ _ _ _ _ 48 Hcfg1). reflexivity.
- intros a Ha. right. right. exists g, CGIF_SIZE. split; [exact Hgin2|]. split; [exact Hgfresh | lia]. }
cbv beta. intros c' (regs5 & mem5 & -> & HJ5 & Hd10'' & Hfr5 & Hout5 & Hgr5 & Hcp5). clear HJ4.
jafter_stretch_keep HS 71%nat regs5 mem5 MEMCPY_CLOB NG_CPY [0%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr5. exact Hrr. }
{ repeat apply Forall_cons; try apply Forall_nil;
(eapply region_kept_out; [exact Hout5 | exact Hgr5 | cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia; intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Hcfg2 : obj_at ubs2segs (ms_mem msx) cfgp LAY_Config cvals);
[ eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg1 | reflexivity |]; intros i Hi;
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia) ltac:(lia) |]
end.
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (heap_present_now : forall o, 0 <= o < CGIF_SIZE -> present (ms_mem msx) (g + 24 + (o - 24)))
end.
{ intros o Ho. replace (g + 24 + (o - 24)) with (g + o) by lia. cbn [ms_mem mkst] in *. eapply (present_grows _ _ _ Hgr5).
match goal with HGx : mem_grows mem4 ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end.
apply (proj1 (heap_blocks _ _ LAWS L2 A2 mem4 md3 g CGIF_SIZE o HH4 Hgin2 Ho)). }
lazymatch type of HS with st_ok _ _ _ ?msx =>
assert (Hcopy : obj_at ubs2segs (ms_mem msx) g (lay_shift 24 LAY_Config) cvals)
end.
{ apply obj_at_shift. cbn [ms_mem mkst]. eapply (obj_at_copy ubs2segs _ mem5 cfgp (g + 24) LAY_Config cvals 48); [exact Hcfg1 | reflexivity | exact Hcp5]. }
add_region HS (YQ0b.mkRegion (Some 53%nat) 0 72 0 72 (mkChunk 0 (CZero 24) :: obj_chunks_gen (lay_shift 24 LAY_Config) 32 lits_Config)).
2:{ unfold region_ok. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val]. ew_havocA. rewrite Hq53, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (present_writable ubs2_msyms). cbn [ms_mem mkst] in *.
replace (g + o) with (g + 24 + (o - 24)) by lia. apply (heap_present_now o). lia. }
apply Forall_cons.
{ apply chunk_ok_zero. cbn [c_off]. intros i Hi. rewrite Z.add_0_r.
transitivity (mbyte ubs2segs mem4 (g + i)); [| apply Hzero4; lia].
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia) ltac:(lia). }
eapply (obj_chunks_gen_ok ubs2segs _ _ g _ cvals 32 lits_Config); [exact Hcopy | reflexivity | | apply lits_Config_ok].
intros j v Hj. assert (Hlj : (j < 10)%nat) by (destruct (Nat.lt_ge_cases j 10) as [Hl|Hl]; [exact Hl|]; rewrite (proj2 (nth_error_None cvals j) Hl) in Hj; discriminate).
rewrite !ew_havoc_old by lia. exact (HX j v Hj). }
2:{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val]. ew_havocA. rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia. repeat split; lia. }
jrun LAWS ubs2tbl_ok HS HJ5.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
assert (HBc : Permutation (blocks L2 A2) ((g, CGIF_SIZE) :: [] ++ blocks L A)).
{ rewrite Hbl2, Hblc. apply Permutation_sym. cbn [app]. apply Permutation_middle. }
jbranch ubs2tbl HS.
-
rewrite branch_ne_U, U_and_lit, (U_atom _ 34 attr), U_lit in Hc by first [lia | ew_havocA; exact HX34].
assert (Hattr4 : Z.land attr 4 <> 0) by (intros Hz; rewrite Hz in Hc; discriminate Hc). clear Hc.
jrun_to LAWS ubs2tbl_ok HS HJ5 NG_TAIL.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (newgif_tail API IMG L A mem md regs rg L2 A2 mm md3 cfgp pal0 attr gen W H ngp loops g pal0 0 []) end.
+ exact HJ5. + exact Hid3. + exact Hra. + exact Htp. + exact Hal16. + exact Hcal. + exact Hclo. + exact Hchi.
+ eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg2 | reflexivity |]; intros i Hi.
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia) ltac:(lia).
+ exact HW1. + exact HH1. + exact HWH.
+
change LAY_CGIF with ([(0, 8%N); (8, 8%N); (16, 8%N)] ++ [(24, 8%N)] ++
lay_shift 24 [(8, 8%N); (16, 4%N); (20, 4%N); (24, 2%N); (26, 2%N); (28, 2%N); (30, 2%N); (32, 8%N); (40, 8%N)] ++
[(72, 8%N); (80, 8%N); (88, 4%N); (92, 4%N)]).
change [0; 0; 0; pal0; 0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0; 0; 0; 0; 1]
with ([0; 0; 0] ++ [pal0] ++ [0; attr; gen; W; H; ngp; loops; ubs2_A_writecb; 0] ++ [0; 0; 0; 1]).
rewrite obj_at_app by reflexivity. split.
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
repeat split;
first [ eapply (st_chunk_zero_val _ _ _ _ 0%nat _ 53%nat 0 24 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq53' | lia | cbn; lia]
| lia ]. }
rewrite obj_at_app by reflexivity. split.
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_val _ _ _ _ 0%nat _ 53%nat 24 8%N (SOff 32 0) _ _ HS);
[reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq53'
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia ]
| cbn; lia ] | exact I]. }
rewrite obj_at_app by reflexivity. split.
{ eapply (st_obj_at _ _ _ _ 0%nat _ 53%nat _ _ _ 33 (tl lits_Config) HS eq_refl eq_refl ltac:(ew_havocA; exact Hq53'));
[ apply incl_chunks_sound; vm_compute; reflexivity | reflexivity | reflexivity | ].
intros j v Hj.
cfg_fields_tac Hj HX. }
{ cbn [obj_at]. unfold field_ok. cbn [fst snd N.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_N].
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 53%nat 72 8 _ _ 8%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq53' | lia | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 53%nat 80 8%N (SLit 0) _ 0 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq53' | reflexivity | lit_range | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_zero_val _ _ _ _ 1%nat _ 53%nat 88 4 _ _ 4%nat HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq53' | lia | cbn; lia] | lit_range ] |].
split; [split; [ eapply (st_chunk_val _ _ _ _ 1%nat _ 53%nat 92 4%N (SLit 1) _ 1 HS); [reflexivity | reflexivity | cbv; auto 40 | ew_havocA; exact Hq53' | reflexivity | lit_range | cbn; lia] | lit_range ] |].
exact I. }
+ exact HBc.
+ destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity].
+ exact Hgfresh.
+ intros b Hb. destruct Hb.
+ destruct (Z.eqb_spec (Z.land attr 4) 0); [contradiction | reflexivity].
+
intros i Hi Hn16. fold sp0. destruct (Z_lt_le_dec i 16) as [Hi16|Hi16].
{ replace (sp0 - 80 + i) with (sp0 + (-80) + i) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-80) 16 sp0 i HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
{ replace (sp0 - 80 + i) with (sp0 + (-56) + (i - 24)) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-56) 16 sp0 (i - 24) HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
+ fold sp0. replace (sp0 - 64) with (sp0 + (-64)) by lia.
eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-64) (SOff 32 0) sp0 pal0 HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
+ frame_wordI HS 3%nat HU2 HE 1%nat (1%bv:reg).
+ frame_wordI HS 3%nat HU2 HE 8%nat (8%bv:reg).
+ frame_wordI HS 3%nat HU2 HE 9%nat (9%bv:reg).
+ frame_wordI HS 3%nat HU2 HE 18%nat (18%bv:reg).
+ frame_wordI HS 3%nat HU2 HE 19%nat (19%bv:reg).
+ reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
+ reg_nowF HS ltac:(rewrite Hq53, unsigned_lit_small by lia; reflexivity).
+ reg_nowF HS ltac:(rewrite HU10; reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
+ reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
-
rewrite branch_ne_U, U_and_lit, (U_atom _ 34 attr), U_lit in Hc by first [lia | ew_havocA; exact HX34].
assert (Hattr4 : Z.land attr 4 = 0) by (destruct (Z.eqb_spec (Z.land attr 4) 0); [assumption | discriminate Hc]). clear Hc.
rewrite Hattr4 in HB. cbn [Z.eqb app] in HB.
assert (Hpalin : In (pala, 3 * ngp) (blocks L A)) by (eapply blocks_perm_in; [exact HB | left; reflexivity]).
jrun_to LAWS ubs2tbl_ok HS HJ5 ubs2_A_malloc.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hgin2 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs2segs Ec ssc msc 10%bv HS) as Hn10; eval_sr_get_in Hn10;
rewrite (denot_mul3' _ 38 ngp) in Hn10 by first [lia | ew_havocA; exact HX38] end.
jreg HS (2%bv:reg) as Hn2. rewrite HU2 in Hn2. jreg HS (4%bv:reg) as Hn4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hn4. jreg HS (1%bv:reg) as Hn1.
eapply SR_bind.
{ eapply (jmalloc_at _ _ LAWS ubs2_errno_low IMG (aa_malloc API)) with (n := 3 * ngp) (spc := sp0 - 80);
[ exact HS | reflexivity | reflexivity | exact HJ5 | exact Hid3 | exact Hn10 | lia
| rewrite Hn2; f_equal; lia | lia | exact Hspm | lia | lia | exact Hn4 | exact Hn1 | apply ret_ok_even; vm_compute; reflexivity ]. }
intros c' (L3 & A3 & regs6 & mem6 & md6 & pal & -> & HJ6 & Hid6 & HP6 & Hp10 & Hres1 & Hkeep6 & Hhi6). clear HJ5.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep6, Hhi6. cbn [ms_regs ms_mem mkst] in HP6, Hkeep6, Hhi6, HJ6, Hp10.
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ6) as HH6.
assert (Hg3 : In (g, CGIF_SIZE) (blocks L3 A3)).
{ destruct Hres1 as [[_ Hbl]|(_ & _ & (b1' & b2' & Hbl6 & Hblc6) & _)]; [rewrite Hbl; exact Hgin2|].
rewrite Hbl6. rewrite Hblc6 in Hgin2. apply in_app_iff in Hgin2. apply in_app_iff. destruct Hgin2 as [H0|H0]; [left; exact H0 | right; right; exact H0]. }
jafter_call_keep HS 82%nat regs6 mem6 HP6 [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite Hq53'; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hkeep6 g CGIF_SIZE (a - g) Hgin2). lia.
+ intros _. apply (present_writable ubs2_msyms). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem6 md6 g CGIF_SIZE (a - g) HH6 Hg3 ltac:(lia))).
- split; cbn [r_base r_lo r_hi r_wlo r_whi base_val]; ew_havocA; rewrite Hq53'; intros a Ha.
+ replace a with (g + (a - g)) by lia. apply (Hkeep6 g CGIF_SIZE (a - g) Hgin2). lia.
+ intros _. apply (present_writable ubs2_msyms). replace a with (g + (a - g)) by lia.
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem6 md6 g CGIF_SIZE (a - g) HH6 Hg3 ltac:(lia))).
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi6 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jreg HS (10%bv:reg) as Hq86. cbn [ms_regs mkst] in Hq86. rewrite Hp10 in Hq86. symmetry in Hq86.
destruct Hres1 as [[-> Hbl6] | (Hpnz & Hp16 & (b1' & b2' & Hbl6 & Hblc6) & Hwr6)].
+
pin_reg HS (10%bv:reg) 0 Hp10.
jrun_to LAWS ubs2tbl_ok HS HJ6 ubs2_A_free.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
jreg HS (10%bv:reg) as Hf10. rewrite Hq53 in Hf10.
jreg HS (2%bv:reg) as Hf2. rewrite HU2 in Hf2. jreg HS (4%bv:reg) as Hf4. rewrite (HE 4%nat 4%bv eq_refl), Htp in Hf4. jreg HS (1%bv:reg) as Hf1.
eapply SR_bind.
{ eapply (jfree_at _ _ LAWS ubs2_errno_low IMG (aa_free API)) with (a := g) (n := CGIF_SIZE) (spc := sp0 - 80);
[ exact HS | reflexivity | reflexivity | exact HJ6 | exact Hg3 | exact Hf10
| rewrite Hf2; f_equal; lia | lia | exact Hspm | lia | lia | exact Hf4 | exact Hf1 | apply ret_ok_even; vm_compute; reflexivity
| intros Hin; exfalso; exact (Hgfresh Hin) ]. }
intros c' (L4 & A4 & regs7 & mem7 & md7 & -> & HJ7 & HP7 & Hrm7 & Hkeep7 & Hhi7 & Hid7). clear HJ6.
change (ms_segs ubs2_msyms) with ubs2segs in Hkeep7, Hhi7. cbn [ms_regs ms_mem mkst] in HP7, Hkeep7, Hhi7, HJ7.
jafter_call_keep HS 98%nat regs7 mem7 HP7 [2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> _ => assert (HK : P); [|specialize (HS2 HK); clear HK] end.
{ constructor; [|constructor; [|constructor; [|constructor]]].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 2); [ew_havocA; exact HU2 | exact Hhi7 | lia | lia | lia | cbn; lia | cbn; lia].
- eapply (region_kept_stack ubs2segs _ _ _ 10); [ew_havocA; exact HU10 | exact Hhi7 | lia | lia | lia | cbn; lia | cbn; lia]. }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ7. { wr_tac3 HU2. }
eapply (SR_ret_at ubs2segs ubs2tbl); [exact ubs2tbl_ok | | | exact HS | reflexivity | vm_compute; reflexivity |].
{ exact (proj1 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ7))). }
{ exact (proj1 (proj2 (heap_model _ _ LAWS _ _ _ _ (proj1 HJ7)))). }
unfold newgif_post.
lazymatch type of HS with st_ok _ _ _ ?msf => exists L4, A4, (ms_regs msf), (ms_mem msf), md7, 0 end.
split; [ret_pc HS HE Hra|]. split; [exact HJ7|]. split; [ret_regs HS HE|].
split; [reg_nowF HS ltac:(reflexivity)|]. left. split; [reflexivity|]. exists [].
eapply perm_after_rm1; [| exact Hrm7]. rewrite Hbl6. exact HBc.
+
assert (Hpin : In (pal, 3 * ngp) (blocks L3 A3)) by (rewrite Hbl6; apply in_app_iff; right; left; reflexivity).
destruct (blocks_range _ _ LAWS L3 A3 mem6 md6 pal (3 * ngp) HH6 Hpin) as [Hp0 Hp1].
assert (Hbase3 : forall b, In b (blocks L2 A2) -> In b (blocks L3 A3)).
{ intros b Hb. rewrite Hbl6. rewrite Hblc6 in Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; exact Hb]. }
assert (Hpala3 : In (pala, 3 * ngp) (blocks L3 A3)) by (apply Hbase3; apply Hbase2; exact Hpalin).
assert (Hsep_gp : g + CGIF_SIZE <= pal \/ pal + 3 * ngp <= g).
{ destruct (heap_sep _ _ LAWS L3 A3 mem6 md6 b1' (pal, 3 * ngp) b2' (g, CGIF_SIZE) HH6 Hbl6 ltac:(rewrite <- Hblc6; exact Hgin2)) as [H0|H0]; cbn [fst snd] in H0; lia. }
assert (Hsep_pp : pal + 3 * ngp <= pala \/ pala + 3 * ngp <= pal).
{ destruct (heap_sep _ _ LAWS L3 A3 mem6 md6 b1' (pal, 3 * ngp) b2' (pala, 3 * ngp) HH6 Hbl6 ltac:(rewrite <- Hblc6; apply Hbase2; exact Hpalin)) as [H0|H0]; cbn [fst snd] in H0; lia. }
add_fact HS 86%nat (mkAF 4096 CEIL_MAX 4).
2:{ rewrite Hq86, unsigned_lit_small by lia. change (2 ^ 4) with 16. lia. }
jrun_to LAWS ubs2tbl_ok HS HJ6 ubs2_A_memcpy.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
jreg HS (10%bv:reg) as Mp0. rewrite Hq86 in Mp0.
jreg HS (11%bv:reg) as Mp1. rewrite HX32, <- Hpala in Mp1.
lazymatch type of HS with st_ok _ ?Ec ?ssc ?msc =>
pose proof (st_ok_reg ubs2segs Ec ssc msc 12%bv HS) as Mp2; eval_sr_get_in Mp2;
first [ rewrite (denot_mul3' _ 38 ngp) in Mp2 by first [lia | ew_havocA; exact HX38]
| rewrite (denot_mul3 _ 38 ngp) in Mp2 by first [lia | ew_havocA; exact HX38] ] end.
jreg HS (1%bv:reg) as Mpra.
eapply SR_bind.
{ eapply (jmemcpy_rd API IMG _ ubs2_memcpy) with (d := pal) (src := pala) (n := 3 * ngp);
[ exact HS | reflexivity | reflexivity | exact HJ6 | exact Mp0 | exact Mp1 | exact Mp2 | exact Mpra
| apply ret_ok_even; vm_compute; reflexivity | lia | lia | | lia | | | | exact Hsep_pp | ].
- destruct (blocks_range _ _ LAWS L3 A3 mem6 md6 pala (3 * ngp) HH6 Hpala3); lia.
- destruct (blocks_range _ _ LAWS L3 A3 mem6 md6 pala (3 * ngp) HH6 Hpala3); lia.
- intros i Hi. match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem6 md6 pal (3 * ngp) i HH6 Hpin Hi)).
- intros i Hi. apply (present_mbyte ubs2_msyms). match goal with HGx : mem_grows _ ?m |- present ?m _ => eapply (present_grows _ _ _ HGx) end. cbn [ms_mem mkst].
apply (proj1 (heap_blocks _ _ LAWS L3 A3 mem6 md6 pala (3 * ngp) i HH6 Hpala3 Hi)).
- intros a Ha. replace a with (pal + (a - pal)) by lia. apply (Hwr6 (blocks L3 A3)); [exact Hpin | lia]. }
cbv beta. intros c' (regs8 & mem8 & -> & HJ8 & Hd10''' & Hfr8 & Hout8 & Hgr8 & Hcp8). clear HJ6.
jafter_stretch_keep HS 98%nat regs8 mem8 MEMCPY_CLOB NG_PALCPY [0%nat; 1%nat; 2%nat; 3%nat; 4%nat] HS2.
match type of HS2 with ?P -> ?Q -> _ => assert (HKr : P); [| assert (HKm : Q); [| specialize (HS2 HKr HKm); clear HKr HKm]] end.
{ intros rr Hrr. apply Hfr8. exact Hrr. }
{ repeat apply Forall_cons; try apply Forall_nil;
(eapply region_kept_out; [exact Hout8 | exact Hgr8 | cbn [r_base r_lo base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq53'; lia
| cbn [r_base r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq53'; lia
| cbn [r_base r_lo r_hi base_val]; ew_havocA; rewrite ?HU2, ?HU10, ?Hq53'; intros a Ha; lia | cbn; lia | cbn; lia]). }
clear HS. rename HS2 into HS.
jrun LAWS ubs2tbl_ok HS HJ8.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
jbranch ubs2tbl HS.
{ exfalso. rewrite branch_ne_U, U_and_lit, U_lit in Hc by lia.
rewrite land4_mod32, U_SExt, (U_atom _ 34 attr) in Hc by first [lia | ew_havocA; exact HX34].
change (2 ^ Z.of_N 32) with (2 ^ 32) in Hc. rewrite sext32_low in Hc by lia. rewrite Hattr4 in Hc. discriminate Hc. }
jrun_to LAWS ubs2tbl_ok HS HJ8 NG_TAIL.
{ eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
eapply wr_ok_cons_tmp; [reflexivity | ew_havocA; rewrite Hq53; apply unsigned_lit_small; lia | exact Hg3 | exact Hgfresh | cbn; lia | cbn; lia |].
wr_tac3 HU2. }
rewrite (st_ok_mkst ubs2segs _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SR _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
eapply (newgif_tail API IMG L A mem md regs rg L3 A3 mm md6 cfgp pal0 attr gen W H ngp loops g pal ngp [(pal, 3 * ngp)]) end.
* exact HJ8. * exact Hid6. * exact Hra. * exact Htp. * exact Hal16. * exact Hcal. * exact Hclo. * exact Hchi.
* eapply (obj_at_transport_range _ _ _ _ _ _ 48); [exact Hcfg2 | reflexivity |]; intros i Hi.
mem_back ltac:(rewrite ?HU2, ?HU10, ?Hq53, ?unsigned_lit_small by lia) ltac:(lia).
* exact HW1. * exact HH1. * exact HWH.
* cgif_obj_tac HS Hq53' (SOff 86 0) Hq86 HX.
* rewrite Hbl6. eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
cbn [app]. eapply Permutation_trans; [| apply perm_swap]. apply perm_skip. rewrite <- Hblc6. exact HBc.
* rewrite Hattr4. reflexivity.
* exact Hgfresh.
* intros b [<- | []] Hin. cbn [snd]. destruct (Z_lt_le_dec 0 (3 * ngp)) as [Hl|Hl]; [|exact Hl].
exfalso. apply (fresh_not_in API L3 A3 mem6 md6 b1' b2' pal (3 * ngp) HH6 Hbl6 Hl). rewrite <- Hblc6. apply Hbase2. exact Hin.
* rewrite Hattr4. reflexivity.
*
intros i Hi Hn16. fold sp0. destruct (Z_lt_le_dec i 16) as [Hi16|Hi16].
{ replace (sp0 - 80 + i) with (sp0 + (-80) + i) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-80) 16 sp0 i HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
{ replace (sp0 - 80 + i) with (sp0 + (-56) + (i - 24)) by lia.
eapply (st_chunk_zero _ _ _ 2%nat _ 2%nat (-56) 16 sp0 (i - 24) HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2 | lia]. }
* fold sp0. replace (sp0 - 64) with (sp0 + (-64)) by lia.
eapply (st_chunk_word _ _ _ 2%nat _ 2%nat (-64) (SOff 32 0) sp0 pal0 HS); [reflexivity | reflexivity | cbv; auto 30 | ew_havocA; exact HU2
| cbn [sv_denot]; ew_havocA; rewrite Z.add_0_r, HX32, Z_to_bv_bv_unsigned; reflexivity | lia].
* frame_wordI HS 3%nat HU2 HE 1%nat (1%bv:reg).
* frame_wordI HS 3%nat HU2 HE 8%nat (8%bv:reg).
* frame_wordI HS 3%nat HU2 HE 9%nat (9%bv:reg).
* frame_wordI HS 3%nat HU2 HE 18%nat (18%bv:reg).
* frame_wordI HS 3%nat HU2 HE 19%nat (19%bv:reg).
* reg_nowF HS ltac:(rewrite HU2; f_equal; lia).
* reg_nowF HS ltac:(rewrite Hq53, unsigned_lit_small by lia; reflexivity).
* reg_nowF HS ltac:(rewrite HU10; reflexivity).
* reg_nowF HS ltac:(reflexivity).
* reg_nowF HS ltac:(rewrite HX38, Z_to_bv_bv_unsigned; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
* reg_nowF HS ltac:(rewrite Z_to_bv_bv_unsigned; apply HE; reflexivity).
Qed.
Theorem ubs2_newgif_spec : newgif_spec API.
Proof. exact ubs2_cgif_newgif. Qed.
End S.
End e.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
