(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACjf.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section d.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_0 PI.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YP03.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section e.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd a176 a184 : Z) (sv2 sv4 : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HRES : 0 <= a176 < 2 ^ 64 /\ 0 <= a184 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 144) 8 a176 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 a184.
Hypothesis HSAV2 : 0 <= sv2 < 2 ^ 64 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 96) 8 sv2.
Let BDp := BD W memc fimg bimg.
Let CALL := bcmp_callW B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112); pose proof HRES as (R176 & R184 & V176 & V184).
Ltac wprelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (HFB : FBAND = 8192) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Definition F1_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25]%bv.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition f1_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 240 248 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 34 0))] ].
Definition f1_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (34%nat, mkAF SB SB 0); (18%nat, mkAF 1 65535 0); (27%nat, mkAF 0 65534 0); (32%nat, mkAF 1 65535 0);
(23%nat, HPTR 0); (26%nat, HPTR 0); (25%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3);
(33%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_f1 : sstate := mkSS 0x1d68 sr_atoms f1_mem None f1_facts.
Definition f1_postX (i : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
((pc' = (BASE + 0x25a4) /\ exists top c0, 0 <= top < Hd /\ 0 <= c0 < Wd /\ BDp (top * Wd + c0) /\
getr regs' 27 = Z_to_bv 64 top /\ getr regs' 20 = Z_to_bv 64 sv4 /\ getr regs' 25 = Z_to_bv 64 bimg /\ getr regs' 18 = Z_to_bv 64 Wd /\
(forall p, i * Wd <= p < top * Wd -> ~ BDp p)) \/
(pc' = (BASE + 0x1f8c) /\ getr regs' 27 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 1 /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 1 /\
getr regs' 10 = Z_to_bv 64 a176 /\ getr regs' 11 = Z_to_bv 64 a184 /\ getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4 /\
getr regs' 6 = Z_to_bv 64 SB /\
(forall p, i * Wd <= p < Wd * Hd -> ~ BDp p))).
Definition f1i_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 96 104 96 96 [YP09.mkChunk 96 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 160 168 160 168 [];
YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 240 248 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 35 0))] ].
Definition f1i_facts : facts := mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_f1i : sstate := mkSS 0x1d9c sr_atoms f1i_mem None f1i_facts.
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia; rewrite ?ew_ewset_other in Hw by lia;
rewrite ?E9, ?unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac awrW E9 FFS :=
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
Ltac run_wkeptF HFr HG HARx WK WKn E9 :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG ltac:(wscr_windows E9) ltac:(lia) ltac:(lia)
ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Lemma fl_f1i : forall (i : Z) (regsF : bvmap 5 word) memF mdF,
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp -> getr regsF 20 = Z_to_bv 64 sv4 ->
(forall p, i * Wd <= p < Wd * Hd -> ~ BDp p) ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x1d9c)) memF (seg_rom SEGS)) mdF) (f1_postX i).
Proof.
intros i regsF memF mdF HJF WK HKF E21r E22r E20r XN.
wctx_names. wprelude HJF. pose proof HJF as HJF0. pose proof HSAV2 as (Rsv2 & V96).
assert (HSpresF : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbF.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 96 sv2 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V96) as V96F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 144 a176 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 176 a184 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V184) as V184F.
remember (Eimg (Ereg regsF [Z_to_bv 64 sv2; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 sv2; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
assert (E32 : ew E 32 = Z_to_bv 64 sv2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 a176) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 a184) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 3)).
assert (HS : st_ok_pi SEGS VAL E ss_f1i (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 0x1d9c)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f1i. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1d9c) _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold f1i_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresF; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 96 8 _ sv2); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V96F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176F]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbF]|]. apply Forall_nil.
- unfold f1i_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f1i_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E9, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT-I" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 35 0) E (mrestrict (w_H W) memF).
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x1f8c.
1: { unfold f1i_mem. awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SLit 1) 1 HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160 end; clear HR1 | st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 2 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SLit 1) 1 HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160 end; clear HR1  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V160.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (20%bv :: 21%bv :: 22%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (27%bv : bv 5) R27. prreg HS (23%bv : bv 5) R23. prreg HS (26%bv : bv 5) R26. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (18%bv : bv 5) R18. prreg HS (6%bv : bv 5) R6.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x1f8c) end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK1|].
split; [intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]|].
split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
right. split; [reflexivity|].
split; [exact R27|]. split; [exact R23|]. split; [exact R26|]. split; [exact V160|].
split; [rewrite R10; evE; exact E33|]. split; [rewrite R11; evE; exact E34|]. split; [rewrite R18; evE; exact E32|].
split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r|]. split; [rewrite R6; evE; exact E35 | exact XN].
Qed.
Definition f1_stmtX (m : nat) : Prop :=
forall (i : Z) (regsE : bvmap 5 word) memE mdE,
Hd - i <= Z.of_nat m -> 0 <= i < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp ->
getr regsE 23 = Z_to_bv 64 (fimg + i * Wd) -> getr regsE 26 = Z_to_bv 64 (bimg + i * Wd) -> getr regsE 18 = Z_to_bv 64 Wd ->
getr regsE 27 = Z_to_bv 64 i -> getr regsE 20 = Z_to_bv 64 sv4 -> getr regsE 25 = Z_to_bv 64 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1d68)) memE (seg_rom SEGS)) mdE) (f1_postX i).
Lemma fl_f1_stepX : forall m, f1_stmtX m -> f1_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold f1_stmtX.
intros i regsE memE mdE Hm Hi HJE WK HKE E21r E22r E23r E26r E19r E24r E20r E25r.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
pose proof (proj1 (proj2 HJE)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_imgP _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi RW RH; nia).
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 208 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V112) as V208E.
remember (Eimg (Ereg regsE [Z_to_bv 64 Hd; Z_to_bv 64 a184; Z_to_bv 64 SB])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 Hd; Z_to_bv 64 a184; Z_to_bv 64 SB]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 18%nat 18%bv eq_refl) as E19. rewrite E19r in E19. pose proof (EE 27%nat 27%bv eq_refl) as E24. rewrite E24r in E24.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 Hd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 a184) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (HS : st_ok_pi SEGS VAL E ss_f1 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1d68)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f1. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1d68) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold f1_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ Hd); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208E]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|]. apply Forall_nil.
- unfold f1_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f1_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E34, E19, E24, E32, E23, E26, E25, E21, E22, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 34 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { unfold f1_mem. awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX (i * Wd) Wd (Z_to_bv 64 (BASE + 0x1d78)) HJE WK1) end.
- lia. - lia. - lia.
- unfold spZ. rewrite Qsp; evE. rewrite (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp; evE. rewrite (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp; evE. rewrite (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- rewrite Qa0; evE. rewrite E23; f_equal; lia. - rewrite Qa1; evE. rewrite E26; f_equal; lia. - rewrite Qa2; evE. exact E19.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WK2 & Kc & Lc).
clear Qa0 Qa1 Qa2 Qra Qsp Qgp Qtp.
assert (HSpres2 : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 34 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2 | st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 34 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2  end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil | specialize (HS2 HQ); clear HQ ] end.
1-2: eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia].
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 34%nat.
pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR4 WK2 WK5 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (Hwit : exists c0, 0 <= c0 < Wd /\ BDp (i * Wd + c0)).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
destruct (Classical_Prop.classic (exists c0, 0 <= c0 < Wd /\ BDp (i * Wd + c0))) as [Y | Y]; [exact Y | exfalso; apply Hc];
lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
evE; unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros j Hj D; apply Y; exists j; split; [exact Hj | exact D] end. }
reshok_bx HS 34%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x25a4.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK5 WK6 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F1_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (27%bv : bv 5) R24f.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x25a4) end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F1_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
left. split; [reflexivity|]. destruct Hwit as (c0 & Hc0 & HBD). exists i, c0.
split; [exact Hi|]. split; [exact Hc0|]. split; [exact HBD|].
split; [rewrite R24f; evE; exact E24|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E19r|].
intros p Hp; exfalso; clear - Hp; lia.
-
assert (XNI : forall j, 0 <= j < Wd -> ~ BDp (i * Wd + j)).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
enough (Hvz : ew Ex n = getr regs2 10) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hc, U_SOff, Hvz, Z.add_0_r; symmetry; apply zcanon_id;
pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia);
evE; unfold CLOB; cbn [map nth]; reflexivity end. }
assert (XROW : forall p, i * Wd <= p < (i + 1) * Wd -> ~ BDp p).
{ intros p Hp. replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp. lia. }
reshok_bx HS 34%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK5 WK6 E9. clear HF HFr HG.
clear Hc. psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HLTU end;
rewrite branch_ltu_U in HLTU; rewrite (U_atom_off _ 27 i 1) in HLTU by (first [evE; exact E24 | lia]); rewrite (U_atom _ 32 Hd) in HLTU by (first [evE; exact E32 | lia]);
[apply Z.ltb_lt in HLTU | apply Z.ltb_ge in HLTU]; reshok_bx HS 34%nat; pose proof (proj1 HJ2) as HAR6.
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1d68.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR6 WK6 WK7 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F1_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (27%bv : bv 5) R24.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (Wd + (fimg + i * Wd))) (denot_add_atoms Ev 18 23 Wd (fimg + i * Wd) ltac:(evE; exact E19) ltac:(evE; exact E23) ltac:(lia) ltac:(lia) ltac:(lia)) R23;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (Wd + (bimg + i * Wd))) (denot_add_atoms Ev 18 26 Wd (bimg + i * Wd) ltac:(evE; exact E19) ltac:(evE; exact E26) ltac:(lia) ltac:(lia) ltac:(lia)) R26 | st_ok _ ?Ev _ _ =>
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (Wd + (fimg + i * Wd))) (denot_add_atoms Ev 18 23 Wd (fimg + i * Wd) ltac:(evE; exact E19) ltac:(evE; exact E23) ltac:(lia) ltac:(lia) ltac:(lia)) R23;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (Wd + (bimg + i * Wd))) (denot_add_atoms Ev 18 26 Wd (bimg + i * Wd) ltac:(evE; exact E19) ltac:(evE; exact E26) ltac:(lia) ltac:(lia) ltac:(lia)) R26  end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i + 1)); [ lia | lia | exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F1_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| rewrite R23; f_equal; lia | rewrite R26; f_equal; lia
| rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E19r
| rewrite R24; evE; rewrite E24, unsigned_lit_small by lia; reflexivity
| rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r ]. }
cbv beta. intros W9 c9 _ (-> & regs9 & mem9 & md9 & pc9 & -> & HJ9 & WK9 & HK9 & H21 & H22 & Hex9).
split; [reflexivity|]. exists regs9, mem9, md9, pc9. split; [reflexivity|]. split; [exact HJ9|]. split; [exact WK9|].
split; [exact HK9|]. split; [exact H21|]. split; [exact H22|].
destruct Hex9 as [(-> & top & c0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & XN9) | (-> & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & XN9)].
* left. split; [reflexivity|]. exists top, c0. split; [clear - Y1 Hi; lia|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [exact Y5|].
split; [exact Y6|]. split; [exact Y7|].
intros p Hp. destruct (Z_lt_le_dec p ((i + 1) * Wd)) as [Hlo | Hhi]; [apply XROW; clear - Hp Hlo; lia | apply XN9; clear - Hp Hhi; lia].
* right. split; [reflexivity|]. split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
split; [exact Y5|]. split; [exact Y6|]. split; [exact Y7|]. split; [exact Y8|]. split; [exact Y9|].
intros p Hp. destruct (Z_lt_le_dec p ((i + 1) * Wd)) as [Hlo | Hhi]; [apply XROW; clear - Hp Hlo; lia | apply XN9; clear - Hp Hhi; lia].
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1d9c.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR6 WK6 WK7 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F1_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
pmkst HS.
eapply (fl_f1i i); [ exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F1_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r
| intros p Hp; apply XROW; clear - Hp HLTU RW Hi; nia ].
Qed.
Lemma fl_f1X : forall m, f1_stmtX m.
Proof. induction m as [|m IH]; [unfold f1_stmtX; intros; exfalso; lia | exact (fl_f1_stepX m IH)]. Qed.
End e.
End d.
End c.
End b.
