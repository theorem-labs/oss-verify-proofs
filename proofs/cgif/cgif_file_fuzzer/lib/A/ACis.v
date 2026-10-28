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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACir.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_asan3_0_listing}.
Context {RO : YC20.ro_below_ofl (@pa_segs _ lib_asan3_0_listing PI) (@pa_relro_lo _ lib_asan3_0_listing PI) (@pa_relro_hi _ lib_asan3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_asan3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_asan3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_asan3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_asan3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TCMP : tcmp_spec B.
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
Section j.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd a176 a184 : Z) (sv2 sv4 : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HRES : 0 <= a176 < 2 ^ 64 /\ 0 <= a184 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 144) 8 a176 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 a184.
Hypothesis HSAV : 0 <= sv2 < 2 ^ 64 /\ 0 <= sv4 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 96) 8 sv2 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 104) 8 sv4.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112); pose proof HRES as (R176 & R184 & V176 & V184); pose proof HSAV as (Rsv2 & Rsv4 & V96 & V104).
Ltac wprelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia; rewrite ?ew_ewset_other in Hw by lia;
rewrite ?E9, ?unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac efact HS n En G :=
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end end.
Ltac rget R En :=
rewrite R; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition s1o_regs := sr_set (sr_set sr_atoms 19%bv (SOff 21 0)) 18%bv (SOff 20 0).
Definition s1o_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 168 176 168 176 [];
YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 35 0))];
YP09.mkRegion (Some 9%nat) 184 192 184 192 [];
YP09.mkRegion (Some 9%nat) 200 208 200 200 [YP09.mkChunk 200 (CVal 8 (SOff 10 0))];
YP09.mkRegion (Some 9%nat) 192 200 192 192 [YP09.mkChunk 192 (CVal 8 (SOff 12 0))];
YP09.mkRegion (Some 9%nat) 240 256 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SOff 34 0))] ].
Definition s1o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (10%nat, mkAF 1 65535 0); (12%nat, mkAF 0 65534 0);
(21%nat, HPTR 0); (20%nat, HPTR 0); (25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, mkAF 1 65535 0); (33%nat, HPTR 3) ] [] [].
Definition ss_s1o : sstate := mkSS 0x1ad4 s1o_regs s1o_mem None s1o_facts.
Definition s1t_regs := sr_set sr_atoms 20%bv (SOff 18 0).
Definition s1t_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 208 216 208 208 [YP09.mkChunk 208 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 19 0))];
YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 36 0))];
YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 200 208 200 200 [YP09.mkChunk 200 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 192 200 192 200 [YP09.mkChunk 192 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 240 256 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 37 0))];
YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SOff 35 0))];
YP09.mkRegion (Some 9%nat) 96 112 96 96 [YP09.mkChunk 96 (CVal 8 (SOff 38 0)); YP09.mkChunk 104 (CVal 8 (SOff 39 0))];
YP09.mkRegion (Some 9%nat) 160 168 160 168 [] ].
Definition s1t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (19%nat, HPTR 0); (18%nat, HPTR 0); (25%nat, HPTR 4); (24%nat, HPTR 3);
(32%nat, mkAF 1 65535 0); (33%nat, mkAF 0 65534 0); (34%nat, mkAF 1 65535 0); (35%nat, mkAF 0 18446744073709551615 0);
(36%nat, mkAF 0 18446744073709551615 0); (37%nat, HPTR 3) ] [] [].
Definition ss_s1t : sstate := mkSS 0x1b64 s1t_regs s1t_mem None s1t_facts.
Definition s1o_postX (i : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 216) 8 bimg /\
((pc' = (BASE + 0x1c1c) /\ exists top c0, 0 <= top < Hd /\ 0 <= c0 < Wd /\ PDp (top * Wd + c0) /\
getr regs' 19 = Z_to_bv 64 top /\ getr regs' 10 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 Hd /\ getr regs' 24 = Z_to_bv 64 cfp /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 184) 8 top /\
(forall p, i * Wd <= p < top * Wd -> ~ PDp p)) \/
(pc' = (BASE + 0x1f8c) /\ getr regs' 27 = Z_to_bv 64 0 /\ getr regs' 23 = Z_to_bv 64 0 /\ getr regs' 26 = Z_to_bv 64 1 /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 1 /\
getr regs' 10 = Z_to_bv 64 a176 /\ getr regs' 11 = Z_to_bv 64 a184 /\ getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4 /\
(forall p, i * Wd <= p < Wd * Hd -> ~ PDp p))).
Definition s1o_stmtX (m : nat) : Prop :=
forall (i : Z) (regsE : bvmap 5 word) memE mdE,
Hd - i <= Z.of_nat m -> 0 <= i < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 25 = Z_to_bv 64 g -> getr regsE 24 = Z_to_bv 64 cfp ->
getr regsE 12 = Z_to_bv 64 i -> getr regsE 21 = Z_to_bv 64 (fimg + i * Wd) -> getr regsE 19 = Z_to_bv 64 (fimg + i * Wd) ->
getr regsE 20 = Z_to_bv 64 (bimg + i * Wd) -> getr regsE 18 = Z_to_bv 64 (bimg + i * Wd) -> getr regsE 10 = Z_to_bv 64 Wd ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 192) 8 i -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1ad4)) memE (seg_rom SEGS)) mdE) (s1o_postX i).
Lemma fl_s1o_stepX : forall m, s1o_stmtX m -> s1o_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold s1o_stmtX.
intros i regsE memE mdE Hm Hi HJE WK HKE E6 E25r E18r E12r E21r E19r E20r E24r E10r V208 V224.
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
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bfp FRAME_SIZE HAR Hbf) as (Hp16 & Hp4096 & Hpceil & Hpfh_ia & _ & _). pose proof (proj1 Hpfh_ia) as Hpfh.
pose proof (blk_off_imgP _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hpfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi RW RH; nia).
assert (HSpresE : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 248 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 208 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V112) as V112E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 144 a176 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 a184 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V184) as V184E.
remember (Eimg (Ereg regsE [Z_to_bv 64 Hd; Z_to_bv 64 bfp; Z_to_bv 64 a176; Z_to_bv 64 a184])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 Hd; Z_to_bv 64 bfp; Z_to_bv 64 a176; Z_to_bv 64 a184]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite E10r in E10. pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25. pose proof (EE 24%nat 24%bv eq_refl) as E18. rewrite E18r in E18.
assert (E32 : ew E 32 = Z_to_bv 64 Hd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 a176) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 a184) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (HS : st_ok_pi SEGS VAL E ss_s1o (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1ad4)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s1o, s1o_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1ad4) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E19r; cbn [sv_denot]; rewrite (ew_Eimg_Ereg_nat regsE _ 21 21%bv eq_refl), E21r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity] | intros X; discriminate X |].
rewrite E24r. cbn [sv_denot]. rewrite (ew_Eimg_Ereg_nat regsE _ 20 20%bv eq_refl), E20r, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- reflexivity.
- unfold s1o_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpres; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ Hd); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V112E]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184E]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200E]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ i); [cbn [sv_denot]; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite F6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|]. apply Forall_nil.
- unfold s1o_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s1o_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E10, E12, E21, E20, E25, E18, E32, E33, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1af0.
1: { unfold s1o_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr1. rename HG into HG1. clear HF.
assert (W1 : forall a, in_wrange E (ss_mem ss_s1o) a -> wscr sp1 a) by (unfold ss_s1o, s1o_mem; wscr_windows E9).
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 W1 ltac:(lia) ltac:(lia) HSpresE)) as WK1.
assert (O1 : forall kk, sp1 + 216 <= kk < sp1 + 224 -> ~ in_wrange E (ss_mem ss_s1o) kk).
{ unfold ss_s1o, s1o_mem; cbn [ss_mem]. intros kk Hk (r & Hr & Hw); cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [(cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia) |]); destruct Hr. }
pose proof (val_mem_run_out E _ W memE _ (sp1 + 216) 8 bimg HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V224) as V224a.
cbn [ms_mem restrict mkst] in V224a.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r5 := eval vm_compute in (nth 5 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 5 r5 HS ltac:(vm_compute; reflexivity)) as HR5; cbn [ms_mem restrict mkst] in HR5;
lazymatch type of HR5 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 192 8%N (SOff 12 0) i HR5
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V208a end; clear HR5 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V208a.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ (24%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr1. cbn [ms_regs restrict] in HKr1.
prreg HS (6%bv : bv 5) R6. prreg HS (23%bv : bv 5) R23. prreg HS (21%bv : bv 5) R21. prreg HS (26%bv : bv 5) R26. prreg HS (22%bv : bv 5) R22. prreg HS (27%bv : bv 5) R27.
pmkst HS.
eapply SRr_bind.
{ pose proof (fl_s1iX B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd sv2 sv4 HC HGEO HSAV (Z.to_nat Wd)) as S1I. unfold s1i_stmtX in S1I.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (S1I 0 (ms_regs msX) (ms_mem msX) mdX i) end;
[ rewrite Z2Nat.id by lia; lia | lia | exact Hi | exact HJE | exact WK1
| intros r Hr; transitivity (getr regsE r); [apply HKr1; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite R6, ?ew_ewset_other by lia; exact F6
| rewrite (HKr1 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr1 24%bv ltac:(cbv; tauto)); exact E18r
| rewrite R23, ?ew_ewset_other by lia; rewrite E21; f_equal; lia
| rewrite R21, ?ew_ewset_other by lia; rewrite E21; f_equal; lia
| rewrite R26, ?ew_ewset_other by lia; rewrite E20; f_equal; lia
| rewrite R22, ?ew_ewset_other by lia; rewrite E20; f_equal; lia
| rewrite R27, ?ew_ewset_other by lia; rewrite E10; f_equal; lia
| exact V208a ]. }
cbv beta. intros W2 c2 _ (-> & regsI & memI & mdI & pcI & -> & HJI & WKI & LI & HKI & H6I & HexI).
clear R6 R23 R21 R26 R22 R27.
assert (HSpresI : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memI a).
{ intros a Ha. pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
assert (HK5I : forall r : bv 5, In r WKEPT5 -> getr regsI r = getr regs r).
{ intros r Hr. rewrite (HKI r) by (cbv [WKEPT5 In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr).
transitivity (getr regsE r); [apply HKr1; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]. }
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 216) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V224a) as V224b.
destruct HexI as [[-> (H20I & H18I & H19I & XNI)] | (-> & Hwit & H11I & H10I & H20I & H21I & H22I)].
2: {
apply SRr_ret. split; [reflexivity|]. exists regsI, memI, mdI, (BASE + 0x1c1c). split; [reflexivity|]. split; [exact HJI|]. split; [exact WKI|].
split; [exact HK5I|]. split; [exact H6I|]. split; [exact H21I|]. split; [exact H22I|]. split; [exact V224b|].
left. split; [reflexivity|]. destruct Hwit as (c0 & Hc0 & HPc0). exists i, c0.
split; [exact Hi|]. split; [exact Hc0|]. split; [exact HPc0|]. split; [exact H11I|]. split; [exact H10I|]. split; [exact H20I|].
split; [rewrite (HKI 24%bv eq_refl), (HKr1 24%bv ltac:(cbv; tauto)); exact E18r|].
split.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 184 8%N (SOff 12 0) i HR3
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V192f end; clear HR3 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V192f.
exact (val_mem_lkept W sp1 _ _ (sp1 + 184) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V192f).
intros p Hp; exfalso; clear - Hp; lia.     }
assert (I9 : getr regsI 9 = Z_to_bv 64 sp1) by (rewrite (HKI 9%bv eq_refl), (HKr1 9%bv ltac:(cbv; tauto)); exact (eq_trans (HKE 9%bv ltac:(cbv; tauto)) H9)).
prreg HS (19%bv : bv 5) R19h. prreg HS (18%bv : bv 5) R24h. prreg HS (20%bv : bv 5) R20h.
assert (I19 : getr regsI 19 = Z_to_bv 64 (fimg + i * Wd)) by (rewrite H19I, R19h, ?ew_ewset_other by lia; exact E21).
assert (I24 : getr regsI 18 = Z_to_bv 64 (bimg + i * Wd)) by (rewrite H18I, R24h, ?ew_ewset_other by lia; exact E20).
assert (I20 : getr regsI 20 = Z_to_bv 64 (bimg + i * Wd)) by (rewrite H20I, R20h, ?ew_ewset_other by lia; exact E20).
assert (I25 : getr regsI 25 = Z_to_bv 64 g) by (rewrite (HKI 25%bv eq_refl), (HKr1 25%bv ltac:(cbv; tauto)); exact E25r).
assert (I18 : getr regsI 24 = Z_to_bv 64 cfp) by (rewrite (HKI 24%bv eq_refl), (HKr1 24%bv ltac:(cbv; tauto)); exact E18r).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 168 8%N (SOff 21 0) (fimg + i * Wd) HR1
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160a end; clear HR1;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 184 8%N (SOff 12 0) i HR3
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V192a end; clear HR3 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V160a, V192a.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 168) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V160a) as V160b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 184) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V192a) as V192b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 192) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V208a) as V208b.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 240 SB WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 248 bfp WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 208 Hd WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V112) as V112I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 200 Wd WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 144 a176 WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 176 a184 WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V184) as V184I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 96 sv2 WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V96) as V96I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 104 sv4 WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V104) as V104I.
clear HS HS0 SHOK.
remember (Eimg (Ereg regsI [Z_to_bv 64 Hd; Z_to_bv 64 i; Z_to_bv 64 Wd; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 bfp; Z_to_bv 64 sv2; Z_to_bv 64 sv4])) as Et eqn:HEt. assert (HEIt : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 Hd; Z_to_bv 64 i; Z_to_bv 64 Wd; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 bfp; Z_to_bv 64 sv2; Z_to_bv 64 sv4]) Et) by (rewrite HEt; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9. pose proof (EEt 6%nat 6%bv eq_refl) as T6. rewrite H6I in T6.
pose proof (EEt 19%nat 19%bv eq_refl) as T19. rewrite I19 in T19. pose proof (EEt 18%nat 18%bv eq_refl) as T24. rewrite I24 in T24.
pose proof (EEt 25%nat 25%bv eq_refl) as T25. rewrite I25 in T25. pose proof (EEt 24%nat 24%bv eq_refl) as T18. rewrite I18 in T18.
assert (T32 : ew Et 32 = Z_to_bv 64 Hd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 i) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 Wd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 a176) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 3)).
assert (T36 : ew Et 36 = Z_to_bv 64 a184) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 4)).
assert (T37 : ew Et 37 = Z_to_bv 64 bfp) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 5)).
assert (T38 : ew Et 38 = Z_to_bv 64 sv2) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 6)).
assert (T39 : ew Et 39 = Z_to_bv 64 sv4) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 7)).
assert (HS : st_ok_pi SEGS VAL Et ss_s1t (restrict (w_H W) (mkst regsI (Z_to_bv 64 (BASE + 0x1b64)) memI (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s1t, s1t_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any Et (BASE + 0x1b64) _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite I20; cbn [sv_denot]; rewrite (ew_Eimg_Ereg_nat regsI _ 18 18%bv eq_refl), I24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
- reflexivity.
- unfold s1t_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite T9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresI; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 208 8 _ Hd); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V112I]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 168 8 _ (fimg + i * Wd)); [cbn [sv_denot]; rewrite T19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite T36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184I]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 184 8 _ i); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V192b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200I]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 192 8 _ i); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite T6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbI]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite T37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpI]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176I]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 96 8 _ sv2); [cbn [sv_denot]; rewrite T38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V96I]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 104 8 _ sv4); [cbn [sv_denot]; rewrite T39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V104I]|]. apply Forall_nil.
+ apply Forall_nil.
- unfold s1t_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite T9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s1t_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite T9, T6, T19, T24, T25, T18, T32, T33, T34, T35, T36, T37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT2" g end]. }
clear HEt. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) Et (mrestrict (w_H W) memI).
pose proof (proj1 HJI) as HARI.
hei_havoc HS; paj_run_tok RUN HS HJI SHOK FLBspan.
1: { unfold s1t_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr2. rename HG into HG2. clear HF.
assert (W2 : forall a, in_wrange Et (ss_mem ss_s1t) a -> wscr sp1 a) by (unfold ss_s1t, s1t_mem; wscr_windows T9).
pose proof (wkept_trans B _ _ _ _ _ _ _ WKI (wkept_of_run B LAWS Et _ lyc Sc W memI _ mdI sp1 HARI HFr2 HG2 W2 ltac:(lia) ltac:(lia) HSpresI)) as WK2.
assert (O2 : forall kk, sp1 + 216 <= kk < sp1 + 224 -> ~ in_wrange Et (ss_mem ss_s1t) kk).
{ unfold ss_s1t, s1t_mem; cbn [ss_mem]. intros kk Hk (r & Hr & Hw); cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [(cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite T9, unsigned_lit_small in Hw by lia; lia) |]); destruct Hr. }
pose proof (val_mem_run_out Et _ W memI _ (sp1 + 216) 8 bimg HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O2; cbn [Z.of_nat] in Hk; lia) V224b) as V224c.
cbn [ms_mem restrict mkst] in V224c.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 33 i 1) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | lia]).
rewrite (U_atom _ 32 Hd) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T32 | lia]).
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x1ad4.
1: { unfold s1t_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HARb HFrb HGb ltac:(wscr_windows T9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (6%bv :: 24%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr3. cbn [ms_regs restrict] in HKr3.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia; rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; lia|]); destruct Hr)
V224c) as V224d.
cbn [ms_mem restrict mkst] in V224d.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r5 := eval vm_compute in (nth 5 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 5 r5 HS ltac:(vm_compute; reflexivity)) as HR5; cbn [ms_mem restrict mkst] in HR5;
lazymatch type of HR5 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 192 8%N (SOff 33 1) (i + 1) HR5
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite denot_lit_U; rewrite (U_atom_off _ 33 i 1); [reflexivity | rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | lia | lia])
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V208c end; clear HR5 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V208c.
prreg HS (12%bv : bv 5) Qa2. prreg HS (10%bv : bv 5) Qa0.
efact HS 19%nat T19 F19. efact HS 18%nat T24 F24. efact HS 34%nat T34 F34.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd + Wd)) (denot_add_atoms Ev 19 34 (fimg + i * Wd) Wd F19 F34 ltac:(lia) ltac:(lia) ltac:(lia)) R21;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd + Wd)) (denot_add_atoms Ev 19 34 (fimg + i * Wd) Wd F19 F34 ltac:(lia) ltac:(lia) ltac:(lia)) R19;
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd + Wd)) (denot_add_atoms Ev 18 34 (bimg + i * Wd) Wd F24 F34 ltac:(lia) ltac:(lia) ltac:(lia)) R20;
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd + Wd)) (denot_add_atoms Ev 18 34 (bimg + i * Wd) Wd F24 F34 ltac:(lia) ltac:(lia) ltac:(lia)) R24 end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i + 1)); [ lia | lia | exact HJI | exact WK3
| intros r Hr; transitivity (getr regsI r); [apply HKr3; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]
| rewrite (HKr3 6%bv ltac:(cbv; tauto)); exact H6I
| rewrite (HKr3 25%bv ltac:(cbv; tauto)); exact I25
| rewrite (HKr3 24%bv ltac:(cbv; tauto)); exact I18
| rewrite Qa2; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?T33; cbn [sv_denot]; rewrite ?unsigned_lit_small by lia; try reflexivity; f_equal; lia
| rewrite R21; f_equal; lia | rewrite R19; f_equal; lia | rewrite R20; f_equal; lia | rewrite R24; f_equal; lia
| rget Qa0 T34
| exact V208c | exact V224d ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & pc3 & -> & HJ3 & WK6 & HK3 & H63 & H213 & H223 & V2163 & Hex).
split; [reflexivity|]. exists regs3, mem3, md3, pc3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK6|].
split; [exact HK3|]. split; [exact H63|]. split; [exact H213|]. split; [exact H223|]. split; [exact V2163|].
assert (XROW : forall p, i * Wd <= p < (i + 1) * Wd -> ~ PDp p).
{ intros p Hp. replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp. lia. }
destruct Hex as [(-> & top & c0 & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & XN9) | (-> & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & XN9)].
-- left. split; [reflexivity|]. exists top, c0. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
intros p Hp. destruct (Z_lt_le_dec p ((i + 1) * Wd)) as [Hlo | Hhi]; [apply XROW; clear - Hp Hlo; lia | apply XN9; clear - Hp Hhi; lia].
-- right. split; [reflexivity|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
split; [exact Q6|]. split; [exact Q7|]. split; [exact Q8|].
intros p Hp. destruct (Z_lt_le_dec p ((i + 1) * Wd)) as [Hlo | Hhi]; [apply XROW; clear - Hp Hlo; lia | apply XN9; clear - Hp Hhi; lia].
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 33 i 1) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | lia]).
rewrite (U_atom _ 32 Hd) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T32 | lia]).
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x1f8c.
1: { unfold s1t_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HARb HFrb HGb ltac:(wscr_windows T9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (6%bv :: WKEPT5) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr3. cbn [ms_regs restrict] in HKr3.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia; rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; lia|]); destruct Hr)
V224c) as V224d.
cbn [ms_mem restrict mkst] in V224d.
prreg HS (27%bv : bv 5) R29. prreg HS (23%bv : bv 5) R23. prreg HS (26%bv : bv 5) R14.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22.
prreg HS (18%bv : bv 5) Qs2. prreg HS (20%bv : bv 5) Qs4.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r9 := eval vm_compute in (nth 9 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 9 r9 HS ltac:(vm_compute; reflexivity)) as HR9x; cbn [ms_mem restrict mkst] in HR9x;
lazymatch type of HR9x with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SLit 1) 1 HR9x
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160x end; clear HR9x end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V160x.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (BASE + 0x1f8c) end.
split; [reflexivity|]. split; [exact HJI|]. split; [exact WK3|].
split; [intros r Hr; transitivity (getr regsI r); [apply HKr3; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]|].
split; [rewrite (HKr3 6%bv ltac:(cbv; tauto)); exact H6I|].
split; [rget R21 T25|]. split; [rget R22 T18|]. split; [exact V224d|].
right. split; [reflexivity|]. split; [exact R29|]. split; [exact R23|]. split; [exact R14|]. split; [exact V160x|].
split; [rget Qa0 T35|]. split; [rget Qa1 T36|]. split; [rget Qs2 T38|]. split; [rget Qs4 T39|].
intros p Hp. replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp Hc HGEO Hi. destruct HGEO as (RW & _). nia.
Qed.
Lemma fl_s1oX : forall m, s1o_stmtX m.
Proof. induction m as [|m IH]; [unfold s1o_stmtX; intros; exfalso; lia | exact (fl_s1o_stepX m IH)]. Qed.
End j.
End f.
End d.
End c.
