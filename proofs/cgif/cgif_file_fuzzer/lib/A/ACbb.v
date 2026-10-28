(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8j ACbc ACbf ACbd.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YE00 YE01 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbg.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC5d YC7z YC85 YC88 YC7k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACb6 ACba.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Definition WDBX_STK : Z := WCBF_STK.
Definition WDB_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 20; 22; 23; 24; 25; 26; 27]%bv.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg lib_asan3_1_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_1_listing PI) (@pa_relro_lo _ lib_asan3_1_listing PI) (@pa_relro_hi _ lib_asan3_1_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_1_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_1_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_1_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_1_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Ltac psrr_branch_pi RUNP BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_step_pi tpi ss) in
lazymatch r with
| PStop (SR_branch ?c ?a ?b) => apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
| _ => fail "psrr_branch_pi: state is not stuck at a branch:" r
end end
end.
Definition wdb_regionsX : smem :=
[ YP09.mkRegion (Some 25%nat) 0 CGIF_SIZE 0 0
[YP09.mkChunk 56 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 80 (CVal 8 (SOff 34 0))] ].
Definition ss_wdbX : sstate := mkSS 0x38c (sr_set sr_atoms 21%bv (SLit 0)) wdb_regionsX None wdb_facts.
Ltac xro_stretch HFr HSINK Vpd HRApd :=
lazymatch goal with |- SRr _ _ (mkCfg ?msn ?mdn) _ =>
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict (w_H ?Wv) ?mo) (mrestrict _ ?mn) =>
lazymatch type of HSINK with asink_at ?sg ?Kv _ ?mdo ?pf ?SG =>
let UN := fresh "UN" in let H2 := fresh "HSINK" in let V2 := fresh "Vpd" in let R2 := fresh "HRApd" in
pose proof (kept_of_frame (segs:=sg) Ef rs (w_H Wv) mo mn (fun _ => False) HFr
ltac:(let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in intros ? ? ? ? Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [[= <- <- <-] | Hin]; [cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN;
let AIL := lazymatch goal with H : asink_img_laws _ _ _ |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ /\ _) |- _ => H end in
assert (H2 : asink_at sg Kv (mrestrict (w_H Wv) mn) mdn pf SG)
by (apply (asink_at_model sg Kv _ mdo); [reflexivity | reflexivity |]; apply (asink_at_frame sg Kv (mrestrict (w_H Wv) mo)); [|exact HSINK];
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; apply (mbyte_of_aview sg); apply UN; [|intros []];
destruct Ha as [Ha | Ha]; [clear - XF Ha; unfold xfacts in XF; unfold FILE_BLOCK in Ha; pose proof asan_consts; lia | pose proof (pa_img_range a (proj1 (ail_env _ _ _ AIL a Ha))); lia]);
lazymatch type of Vpd with val_mem _ _ ?pd _ _ =>
assert (V2 : val_mem sg (mrestrict (w_H Wv) mn) pd 1 0)
by (apply (val_mem_aview_kept_x sg (w_H Wv) (w_H Wv) mo mn pd 1%nat 0); [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply UN; [clear - XF Hx; unfold xfacts in XF; pose proof asan_consts; lia | intros []] | exact Vpd]);
assert (R2 : range_addressable (aview sg (w_H Wv) mn) SHADOW_OFF pd 1)
by (apply (range_addressable_agree (aview sg (w_H Wv) mo)); [|exact HRApd]; let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply UN; [|intros []];
unfold shadow_of_addr; clear - XF Hx; unfold xfacts in XF; pose proof asan_consts; unfold SHADOW_OFF;
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_lt_upper_bound x 8 (2 ^ 50) ltac:(lia) ltac:(lia)); lia);
clear UN HSINK Vpd HRApd; rename H2 into HSINK; rename V2 into Vpd; rename R2 into HRApd end end end end.
Ltac xcall_keep_pd HJc Vpd HRApd :=
lazymatch type of HJc with ajournal ?sg ?Bv _ _ _ ?lyc ?Sc ?W ?memc _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of Vpd with val_mem _ _ ?pd _ _ =>
let Hfin := lazymatch goal with H : In (2, ?fp) (frames Sc) |- _ => H end in
let XF := lazymatch goal with H : xfacts (_ /\ _) |- _ => H end in
let K4 := fresh "K4" in let V2 := fresh "Vpd" in let R2 := fresh "HRApd" in
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K4 & _);
lazymatch type of Hfin with In (2, ?fpos) _ =>
assert (V2 : val_mem sg (mrestrict (w_H W2) mem2) pd 1 0)
by (apply (val_mem_aview_kept_x sg (w_H W) (w_H W2) memc mem2 pd 1%nat 0); [|exact Vpd];
intros x Hx; apply (K4 2 fpos x Hfin); [left; unfold in_zr, frame_rng; cbn [fst snd]; change (fs_frame_bytes 2) with 256; clear - XF Hx; unfold xfacts in XF; lia | xFP]);
assert (R2 : range_addressable (aview sg (w_H W2) mem2) SHADOW_OFF pd 1)
by (apply (range_addressable_agree (aview sg (w_H W) memc)); [|exact HRApd];
let x := fresh "x" in let Hx := fresh "Hx" in
intros x Hx; apply (K4 2 fpos (shadow_of_addr SHADOW_OFF x) Hfin);
[ right; unfold in_zr, shadow_addr, shadow_of_addr; cbn [fst snd]; change (fs_frame_bytes 2 / 8) with 32;
clear - XF Hx; unfold xfacts in XF;
let Fv := fresh "F" in let HFq := fresh "HFq" in let HS8 := fresh "HS8" in
set (Fv := frame_addr lyc 2 fpos) in *;
assert (HFq : Fv = 32 * (Fv / 32)) by (pose proof (Z.div_mod Fv 32 ltac:(lia)); lia);
assert (HS8 : x / 8 = 4 * (Fv / 32) + (x - Fv) / 8)
by (rewrite HFq at 2; replace (x - 32 * (Fv / 32)) with (x - Fv + 0) by lia; rewrite Z.add_0_r;
replace x with ((x - Fv) + (4 * (Fv / 32)) * 8) at 1 by lia; rewrite Z.div_add by lia; lia);
assert (Fv / 8 = 4 * (Fv / 32)) by (rewrite HFq at 1; replace (32 * (Fv / 32)) with (4 * (Fv / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity);
pose proof (Z.div_pos (x - Fv) 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_lt_upper_bound (x - Fv) 8 32 ltac:(lia) ltac:(lia)); lia
| let HFP := fresh "HFP" in let HC := fresh "HC" in intros HFP; apply in_asink_fp in HFP; unfold shadow_of_addr, FILE_BLOCK in HFP;
lazymatch goal with Hia : xfacts (in_app ?pfv 1264) |- _ =>
unfold xfacts, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hia; pose proof asan_consts as HC; clear - XF Hx HFP Hia HC; unfold xfacts in XF;
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SHADOW_OFF in *; lia end ]);
clear K4 Vpd HRApd; rename V2 into Vpd; rename R2 into HRApd end end end.
Section L.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TLF : PALibF B.
Variables wfn hw : Z.
Hypothesis Rwfn : 0 <= wfn < 2 ^ 64 /\ wfn mod 2 = 0.
Hypothesis Rhw : 0 <= hw < 2 ^ 64 /\ hw mod 2 = 0.
Variable K : asink_syms.
Hypothesis AIL : asink_img_laws SEGS B K.
Hypothesis WFNX : twcbF_spec SEGS K B wfn.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Lemma rn_wdbX : forall (m : nat) (n : Z) W (regs : bvmap 5 word) memc mdc sp1 lyc Sc g ctx ch1 (pf pd fpos : Z) (SG : list Z),
Z.of_nat m = n ->
ajournal SEGS B WDBX_STK sp1 (asink_fp pf) lyc Sc W memc mdc [] lyc Sc W memc mdc 0 ->
getr regs 2 = Z_to_bv 64 sp1 -> sp1 mod 16 = 0 ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
achain lyc (aview SEGS (w_H W) memc) sp1 (s0Z regs) ch1 ->
getr regs 19 = Z_to_bv 64 n -> 1 <= n <= 765 ->
getr regs 21 = Z_to_bv 64 0 -> getr regs 22 = Z_to_bv 64 wfn -> getr regs 25 = Z_to_bv 64 g ->
In (g, CGIF_SIZE) (ablocks B lyc Sc) ->
val_mem SEGS (mrestrict (w_H W) memc) (g + 56) 8 hw -> val_mem SEGS (mrestrict (w_H W) memc) (g + 80) 8 pf ->
val_mem SEGS (mrestrict (w_H W) memc) (g + 64) 8 ctx -> 0 <= ctx < 2 ^ 64 ->
getr regs 23 = Z_to_bv 64 pd -> val_mem SEGS (mrestrict (w_H W) memc) pd 1 0 ->
In (2, fpos) (frames Sc) -> In (pf, FILE_BLOCK) (ablocks B lyc Sc) ->
xfacts (in_app pf 1264) ->
xfacts ((pf + 1264 <= g \/ g + 96 <= pf) /\ 4096 <= g /\ (pd + 1 <= pf \/ pf + 1264 <= pd) /\ 4096 <= pf /\ pf + 1264 <= alloc_ceiling /\
alloc_ceiling + WDBX_STK <= sp1 /\ frame_addr lyc 2 fpos <= pd /\ pd + 1 <= frame_addr lyc 2 fpos + 256 /\
frame_addr lyc 2 fpos + 256 <= alloc_ceiling /\ 4096 <= frame_addr lyc 2 fpos /\ frame_addr lyc 2 fpos mod 32 = 0) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pd 1 ->
asink_at SEGS K (mrestrict (w_H W) memc) mdc pf SG -> Z.of_nat (length SG) + n <= SINK_MAX ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x38c)) memc (seg_rom SEGS)) mdc)
(fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x3a8)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B WDBX_STK sp1 (asink_fp pf) lyc Sc W memc mdc [] ly' S' W' mem' md' 0 /\
(ly' = lyc /\ S' = Sc) /\
getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 21 = Z_to_bv 64 0 /\
asink_at SEGS K (mrestrict (w_H W') mem') md' pf (SG ++ repeat 0 m) /\
(forall r : bv 5, reg_in r WDB_CLOB = false -> getr regs' r = getr regs r)).
Proof.
induction m as [|m IH]; intros n W regs memc mdc sp1 lyc Sc g ctx ch1 pf pd fpos SG
Hm HJ H2 Hal16 Hgp Htp Hch1 H18 Hn H19 H21 H25 Hing M56 M80 M64 Hctx H23 Vpd Hfin Hinf Hp_ia XF HRApd HSINK HSmax; [lia|].
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 2 fpos (proj1 HJ) Hfin) as (HF4096 & HFceil & HFhigh). change (fs_frame_bytes 2) with 256 in HFceil, HFhigh.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (proj1 HJ) as HAR. pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & (Hal16' & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ g CGIF_SIZE HAR Hing) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hing) as Hgh_img.
change (req_size CGIF_SIZE) with 96 in Hgceil, Hgpres, Hgh_img.
remember (Eimg (Ereg regs [Z_to_bv 64 hw; Z_to_bv 64 ctx; Z_to_bv 64 pf])) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact H2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr regs 8) by (subst E; eimg_low; exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
assert (E18 : ew E 19 = Z_to_bv 64 n) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H18).
assert (E21 : ew E 22 = Z_to_bv 64 wfn) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H21).
assert (E25 : ew E 25 = Z_to_bv 64 g) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact H25).
assert (E32 : ew E 32 = Z_to_bv 64 hw) by (subst E; eimg_low; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ctx) by (subst E; eimg_low; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 pf) by (subst E; eimg_low; exact (ew_Ereg_extra regs _ 2)).
assert (E23 : ew E 23 = Z_to_bv 64 pd) by (subst E; eimg_low; rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact H23).
assert (HAE : env_agree 32 (Ereg regs []) E).
{ subst E. split; [|reflexivity]. intros nn Hnn. rewrite Eimg_low by (unfold A_TEXT; lia). unfold Ereg. cbn [ew]. destruct (nn <? 32)%nat eqn:Q; [reflexivity|]. apply Nat.ltb_ge in Q. lia. }
assert (HS1 : st_ok_pi SEGS VAL E (mkSS 0x38c sr_atoms wdb_regionsX None wdb_facts) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x38c)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
subst E. apply (rn_st_ok_any (Eimg (Ereg regs [Z_to_bv 64 hw; Z_to_bv 64 ctx; Z_to_bv 64 pf])) (BASE + 0x38c) sr_atoms regs wdb_regionsX wdb_facts (mrestrict (w_H W) memc) (regs_ok_Eimg_Ereg regs _) eq_refl).
- unfold wdb_regionsX.
apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E25, unsigned_lit_small by lia. unfold CGIF_SIZE. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS _ _ g 56 8 _ hw); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M56]|].
apply Forall_cons; [apply (chunk_ok_val SEGS _ _ g 64 8 _ ctx); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact M64]|].
apply Forall_cons; [apply (chunk_ok_val SEGS _ _ g 80 8 _ pf); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - XF; unfold xfacts in XF; pose proof asan_consts; cbn; lia | zside | exact M80]|].
apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. exact (conj I I).
- split; [|split; exact I]. cbn [wdb_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E2, E18, E21, E25, E32, E33, !unsigned_lit_small by lia. change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; lia. }
pose proof (st_ok_pi_pin_reg' _ _ _ (21%bv : bv 5) 0 HS1 ltac:(cbn [ms_regs restrict mkst]; exact H19) eq_refl) as HS. clear HS1.
change (mkSS _ _ _ _ _) with ss_wdbX in HS.
clear HEdef. pose proof HS as HS0.
paj_run_to_sh RUNTOP HS HJ 0x398; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. xro_stretch HFr HSINK Vpd HRApd. clear HF HFr HG.
prreg HS (2%bv : bv 5) P2. prreg HS (22%bv : bv 5) P22. prreg HS (8%bv : bv 5) P8.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H W) msX) 0 _ HS eq_refl) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 56 8%N (SOff 32 0) hw HRr ltac:(cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vhw;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 64 8%N (SOff 33 0) ctx HRr ltac:(cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vctx;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 80 8%N (SOff 34 0) pf HRr ltac:(cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite E34, unsigned_lit_small, Z.add_0_r by (clear - XF; unfold xfacts in XF; pose proof asan_consts; lia); reflexivity) ltac:(clear - XF; unfold xfacts in XF; pose proof asan_consts; cbn; lia) ltac:(cbn; lia)) as Vpf end;
clear HRr;
let pcj := eval vm_compute in (ss_pc ssx) in
let wj := eval vm_compute in (match plookup asan3_1_tpi pcj with Some (PW x) => x | _ => 0 end) in
eapply (SRr_jalr_call_pi (PL:=PL_asan3_1) W Ex ssx _ _ _ wj (1%bv : bv 5) (22%bv : bv 5) wfn HEI HS eq_refl);
[ vm_compute; reflexivity | vm_refl_bv | reflexivity | cbn [ss_pc]; lia | rewrite P22; exact E21 | exact (proj1 Rwfn) | exact (proj2 Rwfn) |] end.
clear HS. intros mat1 ms1 Ems1 HS1.
prreg HS1 (1%bv : bv 5) P1. prreg HS1 (3%bv : bv 5) P3. prreg HS1 (4%bv : bv 5) P4. prreg HS1 (8%bv : bv 5) P8c. prreg HS1 (10%bv : bv 5) P10. prreg HS1 (2%bv : bv 5) P2c.
prreg HS1 (11%bv : bv 5) P11. prreg HS1 (12%bv : bv 5) P12.
lazymatch type of Vpd with val_mem _ ?m _ _ _ => assert (HGA : garr8 SEGS m pd [0]) by (apply garr8_cons_x; [exact Vpd | lia | intros j Hj; cbn in Hj; lia]) end.
lazymatch type of HS1 with st_ok _ ?Ex _ _ =>
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
lazymatch type of Vpd with val_mem _ (mrestrict _ ?mX) _ _ _ =>
assert (HJm : ajournal SEGS B WDBX_STK sp1 (asink_fp pf) lyc Sc W memc mdc [] lyc Sc W mX mdq 0) by (apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ);
assert (Qsp : spZ (ms_regs msq) = sp1 + 0) by (unfold spZ; rewrite P2c, E2; rewrite unsigned_lit_small by lia; lia);
rewrite Ems1 at 1; rewrite Ems1 in Qsp, P1, P3, P4, P8c, P10, P2c, P11, P12; cbn [ms_regs mkst] in Qsp, P1, P3, P4, P8c, P10, P2c, P11, P12;
eapply SRr_bind;
[ eapply (cl_callS B LAWS W _ mX _ WDBX_STK sp1 (asink_fp pf) lyc Sc W memc mdc [] lyc Sc mdq 0
WCBF_STK (asink_fp pf) 0 0 _ ch1
(fun ly2 S2 W2 regs2 mem2 md2 => ly2 = lyc /\ S2 = Sc /\ getr regs2 10 = w64 0 /\ asink_at SEGS K (mrestrict (w_H W2) mem2) md2 pf (SG ++ [0])) HJm Qsp);
[ reflexivity | lia | unfold WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia | unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK; lia
| rewrite P3, E3; exact Hgp
| rewrite P4, E4; exact Htp
| exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite unsigned_lit_small by lia; lia
| unfold s0Z; rewrite P8c, E8; fold (s0Z regs); replace (sp1 + 0) with sp1 by lia;
apply (achain_kept lyc _ _ sp1 _ ch1 sp1 Hch1 ltac:(lia) ltac:(lia) (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ))
| intros HPRE1; eapply SRr_mono;
[ pose proof (WFNX W lyc Sc _ _ _ ch1 g pd 1 pf SG [0] HPRE1) as HC; unfold cfg_at in HC;
lazymatch type of HS1 with st_ok _ _ ?sse _ => replace (w64 wfn) with (Z_to_bv 64 (ss_pc sse)) in HC by reflexivity end;
eapply HC;
[ rewrite P10, E25; reflexivity | rewrite P11, E23; reflexivity | rewrite P12; reflexivity
| exact Hing | exact Vpf | exact Hinf | exact HSINK | exact HGA | reflexivity | lia | clear - HSmax Hn Hm; cbn [length] in *; lia
| clear - XF; unfold xfacts in XF; unfold FILE_BLOCK; lia
| left; rewrite Qsp; clear - XF; unfold xfacts in XF; unfold WDBX_STK, WCBF_STK, YC20.WCB_STK, AFWRITE_STK in *; lia
| clear - XF; unfold xfacts in XF; lia
| apply (amem_range_sub_app _ _ _ _ HFhigh HFceil); clear - XF; unfold xfacts in XF; lia
| exact HRApd
| eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc _ _ _ 2 fpos pd 1 (proj1 HJm) Hfin); [clear - XF; unfold xfacts in XF; lia | change (fs_frame_bytes 2) with 256; clear - XF; unfold xfacts in XF; lia | lia] ]
| cbv beta; intros W2 c2 _ (regs2 & mem2 & md2 & -> & HJ1 & HP & Ha0 & HSINK2);
exists lyc, Sc, regs2, mem2, md2; split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | ]]];
split; [reflexivity | split; [reflexivity | split; [exact Ha0 | exact HSINK2]]] ]
| intros a Ha; left; exact Ha ]
| ] end end end.
clear HJm Qsp HGA.
clear P3 P4 P10 P11 P12 Vhw Vctx Vpf P22.
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc & HP4 & (Ely4 & ES4 & Ha04 & HSINK4)). subst ly4 S4.
pose proof (proj1 HJ4) as HAR4. pose proof Hing as Hing4. pose proof (Permutation_refl (ablocks B lyc Sc)) as HPb4.
assert (HP4' : aregs_preserved (ms_regs (restrict (w_H W) ms1)) regs4) by (rewrite Ems1; cbn [ms_regs restrict mkst]; exact HP4). clear HP4. rename HP4' into HP4.
let K := run_K_hi HS1 in
jafter_call_keep_hi HS1 K regs4 (mrestrict (w_H W4) mem4) HP4 [0%nat] HS2.
rewrite Ems1 in HS2. cbn [ms_mem ms_regs restrict mkst] in HS2, HJc.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ apply Forall_cons; [|apply Forall_nil].
eapply (region_kept_block_sub SEGS B); [exact HJc | cbn [sv_denot]; rewrite E25; apply unsigned_lit_small; lia | exact Hing | exact Hing4 | lia
| change (req_size CGIF_SIZE) with 96; unfold CGIF_SIZE; lia | lia | xFP ]. }
xcall_keep_pd HJc Vpd HRApd. clear HSINK. rename HSINK4 into HSINK.
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2.
lazymatch type of HS2 with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
assert (HEIv : img_env VAL A_LIM (havoc Eo K ws)) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]) end.
pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS2 ltac:(cbn [ms_regs mkst restrict]; exact Ha04) eq_refl) as HS. clear HS2. norm_ss HS.
paj_run_sh RUNP HS HJ4; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. xro_stretch HFr HSINK Vpd HRApd. clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite ?ew_havoc_old in Hc by (cbv; lia). rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia). rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [discriminate Hc|]. clear Hc.
paj_run_to_sh RUNTOP HS HJ4 0x38c; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. xro_stretch HFr HSINK Vpd HRApd. clear HF HFr HG.
prreg HS (2%bv : bv 5) Q2. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (23%bv : bv 5) Q23.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_pi_region_nth Ex ssx (restrict _ msX) 0 _ HS eq_refl) as HRr; cbn [ms_mem restrict mkst] in HRr;
lazymatch type of HRr with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 56 8%N (SOff 32 0) hw HRr ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E32, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as N56;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 64 8%N (SOff 33 0) ctx HRr ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as N64;
pose proof (field_of_region Ex _ 25 g cs lo hi wlo whi 80 8%N (SOff 34 0) pf HRr ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E25; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E34, unsigned_lit_small, Z.add_0_r by (clear - XF; unfold xfacts in XF; pose proof asan_consts; lia); reflexivity)
ltac:(clear - XF; unfold xfacts in XF; pose proof asan_consts; cbn; lia) ltac:(cbn; lia)) as N80 end;
clear HRr end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply SRr_mono;
[ eapply (IH (n - 1) W4 (ms_regs msX) (ms_mem msX) mdX sp1 lyc Sc g ctx ch1 pf pd fpos (SG ++ [0]) ltac:(lia));
[ eapply (ajournal_sub_init SEGS B WDBX_STK sp1 (asink_fp pf) lyc Sc W memc mdc [] lyc Sc W4 _ _ 0 WDBX_STK sp1 (asink_fp pf) 0); [exact HJ4 | lia | reflexivity | lia | lia | lia]
| rewrite Q2; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E2
| exact Hal16
| rewrite Q3; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E3; exact Hgp
| rewrite Q4; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E4; exact Htp
| unfold s0Z; rewrite Q8; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E8; fold (s0Z regs);
apply (achain_kept lyc _ _ sp1 _ ch1 sp1 Hch1 ltac:(lia) ltac:(lia) (aview_above_of_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4))
| rewrite Q19; cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E18, unsigned_lit_small by lia; f_equal; lia
| lia
| exact Q21
| rewrite Q22; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E21
| rewrite Q25; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E25
| exact Hing4 | exact N56 | exact N80 | exact N64 | exact Hctx
| rewrite Q23; cbn [ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); exact E23
| exact Vpd | exact Hfin | exact Hinf | exact Hp_ia | exact XF | exact HRApd | exact HSINK
| clear - HSmax Hn Hm; rewrite length_app; cbn [length]; lia ]
| ] end.
cbv beta. intros W' c' _ (ly'' & S'' & regs'' & mem'' & md'' & -> & HJ'' & (Ely'' & ES'') & HK18 & HK19 & HSINK'' & Hrg).
exists ly'', S'', regs'', mem'', md''. split; [reflexivity|].
split.
{ pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HJ'' ltac:(lia) ltac:(lia)
ltac:(intros aa Haa; left; exact Haa)) as HJ6.
cbn [app] in HJ6. replace (0 + 0) with 0 in HJ6 by lia. exact HJ6. }
split; [split; [exact Ely'' | exact ES'']|].
split; [exact HK18|]. split; [exact HK19|].
split; [cbn [repeat]; rewrite <- app_assoc in HSINK''; exact HSINK''|].
intros r Hr. rewrite (Hrg r Hr).
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
assert (HAEv : env_agree 32 (Ereg regs []) (havoc Eo K ws)) by (apply (env_agree_havoc_ge 32 K); [cbv; lia | exact HAE]) end.
destruct (wdb_clob_kept r Hr) as [-> | Hin].
+ rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok_pi _ _ _ regs [] WDB_KEPT HS HAEv ltac:(vm_compute; reflexivity) r Hin).
-
unfold branch_taken in Hc. rewrite bv_eqb_unsigned in Hc. cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub negb] in Hc.
rewrite E18 in Hc. replace (bv_unsigned (Z_to_bv 64 n)) with n in Hc by (symmetry; apply unsigned_lit_small; lia). rewrite !unsigned_lit_small in Hc by lia.
destruct (Z.eqb_spec (n + -1) 0) as [Hz | Hnz]; [|discriminate Hc]. clear Hc.
paj_run_to_sh RUNTOP HS HJ4 0x3a8; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]|]. xro_stretch HFr HSINK Vpd HRApd. clear HF HFr HG.
prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?K ?ws) _ _ =>
assert (HAEv : env_agree 32 (Ereg regs []) (havoc Eo K ws)) by (apply (env_agree_havoc_ge 32 K); [cbv; lia | exact HAE]) end.
pmkst HS. apply SRr_ret.
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX] => exists lyc, Sc, (ms_regs msX), (ms_mem msX), mdX end.
split; [reflexivity|]. split; [exact HJ4|]. split; [split; reflexivity|].
split; [rewrite Q19; cbn [sv_denot ew havoc Nat.ltb Nat.leb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E18, unsigned_lit_small by lia; f_equal; lia|].
split; [exact Q21|].
split; [replace m with 0%nat by lia; cbn [repeat]; exact HSINK|].
intros r Hr. destruct (wdb_clob_kept r Hr) as [-> | Hin].
+ rewrite (st_ok_reg SEGS _ _ _ 0%bv HS), (st_ok_reg SEGS _ _ _ 0%bv HS0). reflexivity.
+ exact (regs_kept_of_st_ok_pi _ _ _ regs [] WDB_KEPT HS HAEv ltac:(vm_compute; reflexivity) r Hin).
Qed.
End L.
End e.
End d.
