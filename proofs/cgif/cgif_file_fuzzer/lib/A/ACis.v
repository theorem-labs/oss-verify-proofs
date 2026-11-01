(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
[ YP09.mkRegion (Some 9%nat) 168 176 168 176 []; YP09.mkRegion (Some 9%nat) 184 192 184 192 [] ].
Definition s1o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (10%nat, mkAF 1 65535 0); (12%nat, mkAF 0 65534 0);
(21%nat, HPTR 0); (20%nat, HPTR 0); (25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, mkAF 1 65535 0); (33%nat, HPTR 3) ] [] [].
Definition ss_s1o : sstate := mkSS 6868 s1o_regs s1o_mem None s1o_facts.
Definition s1t_regs := sr_set sr_atoms 20%bv (SOff 18 0).
Definition s1t_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 96 160 96 96
    [YP09.mkChunk 96 (CVal 8 (SOff 40 0)); YP09.mkChunk 104 (CVal 8 (SOff 41 0)); YP09.mkChunk 144 (CVal 8 (SOff 38 0))];
  YP09.mkRegion (Some 9%nat) 160 168 160 168 [];
  YP09.mkRegion (Some 9%nat) 168 192 168 168
    [YP09.mkChunk 168 (CVal 8 (SOff 35 0)); YP09.mkChunk 176 (CVal 8 (SOff 39 0)); YP09.mkChunk 184 (CVal 8 (SOff 33 0))];
  YP09.mkRegion (Some 9%nat) 192 200 192 200 [YP09.mkChunk 192 (CVal 8 (SOff 36 0))];
  YP09.mkRegion (Some 9%nat) 200 216 200 200 [YP09.mkChunk 200 (CVal 8 (SOff 32 0)); YP09.mkChunk 208 (CVal 8 (SOff 34 0))] ].
Definition s1t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (19%nat, HPTR 0); (18%nat, HPTR 0); (25%nat, HPTR 4); (24%nat, HPTR 3);
(32%nat, mkAF 1 65535 0); (33%nat, mkAF 0 65534 0); (34%nat, mkAF 1 65535 0); (35%nat, mkAF 0 18446744073709551615 0);
(36%nat, mkAF 0 18446744073709551615 0); (37%nat, HPTR 3) ] [] [].
Definition ss_s1t : sstate := mkSS 7012 s1t_regs s1t_mem None s1t_facts.
Definition s1o_postX (i : Z) : world SEGS -> config -> Prop := fun Wn cn =>
Wn = W /\ exists (regsn : bvmap 5 word) (memn : word -> option byte) (mdn : Model) (pcn : Z),
cn = {| cfg_ms := mkst regsn (Z_to_bv 64 pcn) memn (seg_rom SEGS); cfg_model := mdn |} /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memn mdn k /\
wkept B lyc Sc W sp1 memc memn /\
(forall r, In r WKEPT5 -> getr regsn r = getr regs r) /\
getr regsn 6 = Z_to_bv 64 SB /\ getr regsn 21 = Z_to_bv 64 g /\ getr regsn 22 = Z_to_bv 64 cfp /\
val_mem SEGS (mrestrict (w_H W) memn) (sp1 + 216) 8 bimg /\
(pcn = BASE + 7196 /\
 (exists top c0, i <= top < Hd /\ 0 <= c0 < Wd /\ PDp (top * Wd + c0) /\
  getr regsn 19 = Z_to_bv 64 top /\ getr regsn 10 = Z_to_bv 64 top /\ getr regsn 15 = Z_to_bv 64 Hd /\
  getr regsn 24 = Z_to_bv 64 cfp /\ val_mem SEGS (mrestrict (w_H W) memn) (sp1 + 184) 8 top /\
  (forall p, i * Wd <= p < top * Wd -> ~ PDp p))
 \/
 pcn = BASE + 8076 /\
 getr regsn 27 = Z_to_bv 64 0 /\ getr regsn 23 = Z_to_bv 64 0 /\ getr regsn 26 = Z_to_bv 64 1 /\
 val_mem SEGS (mrestrict (w_H W) memn) (sp1 + 160) 8 1 /\
 getr regsn 10 = Z_to_bv 64 a176 /\ getr regsn 11 = Z_to_bv 64 a184 /\
 getr regsn 18 = Z_to_bv 64 sv2 /\ getr regsn 20 = Z_to_bv 64 sv4 /\
 (forall p, i * Wd <= p < Wd * Hd -> ~ PDp p)).
Definition s1o_stmtX (m : nat) : Prop :=
forall (i : Z) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model),
Hd - i <= Z.of_nat m ->
0 <= i < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k ->
wkept B lyc Sc W sp1 memc memE ->
(forall r, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB ->
getr regsE 25 = Z_to_bv 64 g ->
getr regsE 24 = Z_to_bv 64 cfp ->
getr regsE 12 = Z_to_bv 64 i ->
getr regsE 21 = Z_to_bv 64 (fimg + i * Wd) ->
getr regsE 19 = Z_to_bv 64 (fimg + i * Wd) ->
getr regsE 20 = Z_to_bv 64 (bimg + i * Wd) ->
getr regsE 18 = Z_to_bv 64 (bimg + i * Wd) ->
getr regsE 10 = Z_to_bv 64 Wd ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 192) 8 i ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg ->
SRr SEGS W {| cfg_ms := mkst regsE (Z_to_bv 64 (BASE + 6868)) memE (seg_rom SEGS); cfg_model := mdE |} (s1o_postX i).
Lemma fl_s1o_stepX : forall m, s1o_stmtX m -> s1o_stmtX (Datatypes.S m).
Proof.
intros m Onward. red.
intros i rE mE dE Afuel Arng Ajr Awk Akp Ar6 Ar25 Ar24 Ar12 Ar21 Ar19 Ar20 Ar18 Ar10 Am192 Am216.
wctx_names. wprelude Ajr.
assert (Qlo : alloc_ceiling + 17040 <= sp1) by (rewrite FFS in Hslo; lia).
assert (Qhi : sp1 + 384 <= 2 ^ 47) by lia.
assert (QSB : SB = 2147450880) by reflexivity.
assert (QNb : req_size Nb = Nb) by (unfold req_size; destruct (Z.eqb_spec Nb 0); lia).
pose proof (al_blocks _ _ LAWS lyc Sc W mE dE fimg Nb HAR Hfi) as (Pf16 & Pf4k & Pfc & _).
pose proof (al_blocks _ _ LAWS lyc Sc W mE dE bimg Nb HAR Hbi) as (Pb16 & Pb4k & Pbc & _).
pose proof (al_blocks _ _ LAWS lyc Sc W mE dE g CGIF_SIZE HAR Hg) as (Pg16 & Pg4k & Pgc & _).
pose proof (al_blocks _ _ LAWS lyc Sc W mE dE cfp FRAME_SIZE HAR Hcf) as (Pc16 & Pc4k & Pcc & _).
assert (Qg : 0 < req_size CGIF_SIZE) by (vm_compute; reflexivity).
assert (Qc : 0 < req_size FRAME_SIZE) by (vm_compute; reflexivity).
rewrite QNb in Pfc, Pbc.
assert (Qrow : i * Wd + Wd <= Nb) by (rewrite HN; nia).
set (EA := Eimg (Ereg rE [Z_to_bv 64 Wd; Z_to_bv 64 cfp])).
assert (EAreg : forall r, getr rE r = sv_denot EA (sr_get sr_atoms r)) by exact (regs_ok_Eimg_Ereg rE _).
assert (EA9 : ew EA 9 = Z_to_bv 64 sp1).
{ change (getr rE 9 = Z_to_bv 64 sp1). rewrite Akp; [exact H9 | do 4 right; left; reflexivity]. }
assert (EA6 : ew EA 6 = Z_to_bv 64 SB) by exact Ar6.
assert (EA10 : ew EA 10 = Z_to_bv 64 Wd) by exact Ar10.
assert (EA12 : ew EA 12 = Z_to_bv 64 i) by exact Ar12.
assert (EA20 : ew EA 20 = Z_to_bv 64 (bimg + i * Wd)) by exact Ar20.
assert (EA21 : ew EA 21 = Z_to_bv 64 (fimg + i * Wd)) by exact Ar21.
assert (EA24 : ew EA 24 = Z_to_bv 64 cfp) by exact Ar24.
assert (EA25 : ew EA 25 = Z_to_bv 64 g) by exact Ar25.
assert (EA32 : ew EA 32 = Z_to_bv 64 Wd) by reflexivity.
assert (EA33 : ew EA 33 = Z_to_bv 64 cfp) by reflexivity.
assert (Awin : forall a, in_wrange EA (ss_mem ss_s1o) a -> wscr sp1 a) by wscr_windows EA9.
lazymatch eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 20 6896 ss_s1o) with
| (?sA, ?stA) => pose (ssB := sA);
  refine (RUNTOP W 20 6896 EA ss_s1o ssB stA (mkst rE (Z_to_bv 64 (BASE + 6868)) mE (seg_rom SEGS)) TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc dE k (s1o_postX i) _ _ _ _ Ajr _ _)
end.
- apply Eimg_env.
- rewrite restrict_mkst_fx. unfold ss_s1o. apply pa_entry_st_ok_full.
  + unfold s1o_regs. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity | ] | reflexivity | ].
    * rewrite Ar19, <- Ar21. apply EAreg.
    * rewrite Ar18, <- Ar20. apply EAreg.
  + reflexivity.
  + unfold s1o_mem. apply Forall_cons; [ | apply Forall_cons; [ | apply Forall_nil]].
    all: unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    all: rewrite EA9, unsigned_lit_small by lia.
    all: split; [lia | split; [lia | split; [intros o Ho; apply apresent_writable, HSpres; rewrite FFS; lia | apply Forall_nil]]].
  + unfold s1o_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, base_val.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite EA9, unsigned_lit_small by lia. repeat split; lia.
  + unfold s1o_facts, facts_ok, HPTR. cbn [f_atoms f_conds f_alias atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite EA9, EA6, EA10, EA12, EA21, EA20, EA25, EA24, EA32, EA33, QSB.
    rewrite !unsigned_lit_small by nia.
    split; [ | split; exact I].
    repeat split; try lia.
    all: first [change (2 ^ 0) with 1; apply Z.mod_1_r | change (2 ^ 4) with 16; lia | change (2 ^ 3) with 8; apply mod16_mod8, Pc16].
- vm_compute. reflexivity.
- exact I.
- intros a Ha. left. specialize (Awin a Ha). unfold wscr in Awin. rewrite FFS. lia.
- unfold run_post_pi_AJ. intros msB matB Bst Bjr Bfr Bfrr Bgr.
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ Bst eq_refl) as Bshape.
  set (rB := ms_regs msB) in *. set (mB := ms_mem msB) in *. set (dB := with_vm_backing (m_vm_lazy dE) matB dE) in *.
  rewrite Bshape in Bst |- *. rewrite restrict_mkst_fx in Bst.
  pose proof (st_ok_regs_ok _ _ _ _ Bst) as Brg. unfold regs_ok in Brg.
  change (forall r, getr rB r = sv_denot EA (sr_get (ss_regs ssB) r)) in Brg.
  assert (Bkp : forall r, In r WKEPT5 -> getr rB r = getr regs r).
  { intros r Hr. rewrite <- (Akp r Hr). unfold WKEPT5 in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; rewrite Brg, EAreg; reflexivity. }
  assert (Awin2 : forall a, in_wrange EA (ss_mem ss_s1o) a -> sp1 + 168 <= a < sp1 + 176 \/ sp1 + 184 <= a < sp1 + 192).
  { intros a (r & Hr & Hw). unfold ss_s1o, s1o_mem in Hr. cbn [ss_mem In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
    rewrite EA9, unsigned_lit_small in Hw by lia; lia. }
  assert (Soff0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v).
  { intros E n v Hv. cbn [sv_denot]. rewrite Hv, YP0n.Z_to_bv_unsigned_add. f_equal; lia. }
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ Bst eq_refl) as Breg2. cbn [ms_mem] in Breg2.
  pose proof (field_of_region EA _ 9 sp1 _ _ _ _ _ 184 8 (SOff 12 0) i Breg2) as Bm184.
  specialize (Bm184 ltac:(rewrite EA9; apply unsigned_lit_small; lia) ltac:(left; reflexivity) (Soff0 _ _ _ EA12) ltac:(lia) ltac:(lia)).
  pose proof (fl_s1iX B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
    gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd sv2 sv4 HC HGEO HSAV (Z.to_nat Wd)) as Inner.
  unfold s1i_stmtX in Inner.
  eapply SRr_bind.
  + apply (Inner 0 rB mB dB i).
    * lia.
    * lia.
    * exact Arng.
    * exact Bjr.
    * apply (wkept_trans _ _ _ _ _ _ _ _ Awk).
      apply (wkept_of_run B LAWS EA (ss_mem ss_s1o) lyc Sc W mE mB dE sp1 HAR); [exact Bfrr | exact Bgr | exact Awin | rewrite WS; lia | lia |].
      intros a Ha. apply HSpres. rewrite FFS. rewrite WS in Ha. lia.
    * exact Bkp.
    * rewrite <- Ar6, Brg, EAreg. reflexivity.
    * rewrite <- Ar25, Brg, EAreg. reflexivity.
    * rewrite <- Ar24, Brg, EAreg. reflexivity.
    * replace (fimg + (i * Wd + 0)) with (fimg + i * Wd) by lia. rewrite <- Ar21, Brg, EAreg. reflexivity.
    * replace (fimg + (i * Wd + 0)) with (fimg + i * Wd) by lia. rewrite <- Ar21, Brg, EAreg. reflexivity.
    * replace (bimg + (i * Wd + 0)) with (bimg + i * Wd) by lia. rewrite <- Ar20, Brg, EAreg. reflexivity.
    * replace (bimg + (i * Wd + 0)) with (bimg + i * Wd) by lia. rewrite <- Ar20, Brg, EAreg. reflexivity.
    * replace (Wd - 0) with Wd by lia. rewrite <- Ar10, Brg, EAreg. reflexivity.
    * apply (val_mem_frame EA (ss_mem ss_s1o) _ _ _ _ _ Bfrr); [ | lia | lia | exact Am192].
      intros q Hq Hin. apply Awin2 in Hin. lia.
  + intros Wc cc Cle Cpost.
    destruct Cpost as (-> & rC & mC & dC & pcC & -> & Cjr & Cwk & Clk & Ccl & Cr6 & Cexit).
    assert (Cm216 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 216) 8 bimg).
    { apply (val_mem_lkept W sp1 mB mC); [exact Clk | lia | lia |].
      apply (val_mem_frame EA (ss_mem ss_s1o) _ _ _ _ _ Bfrr); [ | lia | lia | exact Am216].
      intros q Hq Hin. apply Awin2 in Hin. lia. }
    assert (Ckp : forall r, In r WKEPT5 -> getr rC r = getr regs r).
    { intros r Hr. pose proof (Bkp r Hr) as Hk. unfold WKEPT5 in Hr.
      destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; rewrite <- Hk; apply Ccl; reflexivity. }
    destruct Cexit as [(-> & Cr20 & Cr18 & Cr19 & Cnone) | (-> & Cfound & Cr19 & Cr10 & Cr15 & Cr21 & Cr22)].
    * assert (Cflat : forall p, i * Wd <= p < i * Wd + Wd -> ~ PDp p).
      { intros p Hp. replace p with (i * Wd + (p - i * Wd)) by ring. apply Cnone. lia. }
      assert (Cr9 : getr rC 9 = Z_to_bv 64 sp1) by (rewrite Ckp; [exact H9 | do 4 right; left; reflexivity]).
      assert (Cr25 : getr rC 25 = Z_to_bv 64 g) by (rewrite Ccl by reflexivity; rewrite <- Ar25, Brg, EAreg; reflexivity).
      assert (Cr24 : getr rC 24 = Z_to_bv 64 cfp) by (rewrite Ccl by reflexivity; rewrite <- Ar24, Brg, EAreg; reflexivity).
      assert (Cv19 : getr rC 19 = Z_to_bv 64 (fimg + i * Wd)) by (rewrite Cr19, <- Ar21, Brg, EAreg; reflexivity).
      assert (Cv18 : getr rC 18 = Z_to_bv 64 (bimg + i * Wd)) by (rewrite Cr18, <- Ar20, Brg, EAreg; reflexivity).
      assert (Cv20 : getr rC 20 = Z_to_bv 64 (bimg + i * Wd)) by (rewrite Cr20, <- Ar20, Brg, EAreg; reflexivity).
      pose proof Cjr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Cpres & _).
      assert (Ckeep : forall off v, 0 <= off -> off + 8 <= 232 -> (forall q, 0 <= q < 8 -> ~ wscr sp1 (sp1 + off + q)) ->
        val_mem SEGS (mrestrict (w_H W) memc) (sp1 + off) 8 v -> val_mem SEGS (mrestrict (w_H W) mC) (sp1 + off) 8 v).
      { intros off v Ho1 Ho2 Hnw Hv. apply (val_mem_wkept B lyc Sc W sp1 memc mC off v Cwk); [lia | lia | lia | lia | lia | exact Hnw | exact Hv]. }
      assert (Cm96 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 96) 8 sv2) by (apply Ckeep; [lia | lia | intros q Hq; unfold wscr; lia | exact V96]).
      assert (Cm104 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 104) 8 sv4) by (apply Ckeep; [lia | lia | intros q Hq; unfold wscr; lia | exact V104]).
      assert (Cm144 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 144) 8 a176) by (apply Ckeep; [lia | lia | intros q Hq; unfold wscr; lia | exact V176]).
      assert (Cm176 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 176) 8 a184) by (apply Ckeep; [lia | lia | intros q Hq; unfold wscr; lia | exact V184]).
      assert (Cm200 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 200) 8 Wd) by (apply Ckeep; [lia | lia | intros q Hq; unfold wscr; lia | exact V200]).
      assert (Cm208 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 208) 8 Hd) by (apply Ckeep; [lia | lia | intros q Hq; unfold wscr; lia | exact V112]).
      pose proof (st_ok_pi_region_nth _ _ _ 0 _ Bst eq_refl) as Breg1. cbn [ms_mem] in Breg1.
      pose proof (field_of_region EA _ 9 sp1 _ _ _ _ _ 168 8 (SOff 21 0) (fimg + i * Wd) Breg1) as Bm168.
      specialize (Bm168 ltac:(rewrite EA9; apply unsigned_lit_small; lia) ltac:(left; reflexivity) (Soff0 _ _ _ EA21) ltac:(lia) ltac:(lia)).
      assert (Cm168 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 168) 8 (fimg + i * Wd)) by (apply (val_mem_lkept W sp1 mB mC); [exact Clk | lia | lia | exact Bm168]).
      assert (Cm184 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 184) 8 i) by (apply (val_mem_lkept W sp1 mB mC); [exact Clk | lia | lia | exact Bm184]).
      assert (Cm192 : val_mem SEGS (mrestrict (w_H W) mC) (sp1 + 192) 8 i).
      { apply (val_mem_lkept W sp1 mB mC); [exact Clk | lia | lia |].
        apply (val_mem_frame EA (ss_mem ss_s1o) _ _ _ _ _ Bfrr); [ | lia | lia | exact Am192].
        intros q Hq Hin. apply Awin2 in Hin. lia. }
      set (ET := Eimg (Ereg rC [Z_to_bv 64 Wd; Z_to_bv 64 i; Z_to_bv 64 Hd; Z_to_bv 64 (fimg + i * Wd); Z_to_bv 64 i; Z_to_bv 64 cfp;
                                Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 sv2; Z_to_bv 64 sv4])).
      assert (ETreg : forall r, getr rC r = sv_denot ET (sr_get sr_atoms r)) by exact (regs_ok_Eimg_Ereg rC _).
      assert (ET9 : ew ET 9 = Z_to_bv 64 sp1) by exact Cr9.
      assert (ET6 : ew ET 6 = Z_to_bv 64 SB) by exact Cr6.
      assert (ET18 : ew ET 18 = Z_to_bv 64 (bimg + i * Wd)) by exact Cv18.
      assert (ET19 : ew ET 19 = Z_to_bv 64 (fimg + i * Wd)) by exact Cv19.
      assert (ET24 : ew ET 24 = Z_to_bv 64 cfp) by exact Cr24.
      assert (ET25 : ew ET 25 = Z_to_bv 64 g) by exact Cr25.
      assert (ET32 : ew ET 32 = Z_to_bv 64 Wd) by reflexivity.
      assert (ET33 : ew ET 33 = Z_to_bv 64 i) by reflexivity.
      assert (ET34 : ew ET 34 = Z_to_bv 64 Hd) by reflexivity.
      assert (ET35 : ew ET 35 = Z_to_bv 64 (fimg + i * Wd)) by reflexivity.
      assert (ET36 : ew ET 36 = Z_to_bv 64 i) by reflexivity.
      assert (ET37 : ew ET 37 = Z_to_bv 64 cfp) by reflexivity.
      assert (ET38 : ew ET 38 = Z_to_bv 64 a176) by reflexivity.
      assert (ET39 : ew ET 39 = Z_to_bv 64 a184) by reflexivity.
      assert (ET40 : ew ET 40 = Z_to_bv 64 sv2) by reflexivity.
      assert (ET41 : ew ET 41 = Z_to_bv 64 sv4) by reflexivity.
      assert (Dwin : forall a, in_wrange ET (ss_mem ss_s1t) a -> wscr sp1 a) by wscr_windows ET9.
      lazymatch eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 20 6868 ss_s1t) with
      | (?sD, ?stD) => pose (ssD := sD);
        refine (RUNTOP W 20 6868 ET ss_s1t ssD stD (mkst rC (Z_to_bv 64 (BASE + 7012)) mC (seg_rom SEGS)) TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc dC k (s1o_postX i) _ _ _ _ Cjr _ _)
      end.
      -- apply Eimg_env.
      -- rewrite restrict_mkst_fx. unfold ss_s1t. apply pa_entry_st_ok_full.
         ++ unfold s1t_regs. apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity |].
            rewrite Cv20, <- Cv18. apply ETreg.
         ++ reflexivity.
         ++ unfold s1t_mem. repeat apply Forall_cons; try apply Forall_nil.
            all: unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            all: rewrite ET9, unsigned_lit_small by lia.
            all: split; [lia | split; [lia | split; [intros o Ho; apply apresent_writable, Cpres; rewrite FFS; lia | ]]].
            all: repeat apply Forall_cons; try apply Forall_nil.
            all: eapply chunk_ok_val; [apply Soff0; reflexivity | lia | lia | ].
            all: first [exact Cm96 | exact Cm104 | exact Cm144 | exact Cm168 | exact Cm176 | exact Cm184 | exact Cm192 | exact Cm200 | exact Cm208].
         ++ unfold s1t_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, base_val.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi]. rewrite ET9, unsigned_lit_small by lia. repeat split; lia.
         ++ unfold s1t_facts, facts_ok, HPTR. cbn [f_atoms f_conds f_alias atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
            rewrite ET9, ET6, ET19, ET18, ET25, ET24, ET32, ET33, ET34, ET35, ET36, ET37, QSB.
            rewrite !unsigned_lit_small by nia.
            split; [ | split; exact I].
            repeat split; try lia.
            all: first [change (2 ^ 0) with 1; apply Z.mod_1_r | change (2 ^ 4) with 16; lia | change (2 ^ 3) with 8; apply mod16_mod8, Pc16].
      -- vm_compute. reflexivity.
      -- exact I.
      -- intros a Ha. left. specialize (Dwin a Ha). unfold wscr in Dwin. rewrite FFS. lia.
      -- unfold run_post_pi_AJ. intros msD matD Dst Djr Dfr Dfrr Dgr.
         set (mD := ms_mem msD) in *. set (dD := with_vm_backing (m_vm_lazy dC) matD dC) in *.
         assert (Dwin2 : forall a, in_wrange ET (ss_mem ss_s1t) a -> sp1 + 160 <= a < sp1 + 168 \/ sp1 + 192 <= a < sp1 + 200).
         { intros a (r & Hr & Hw). lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end.
           cbn [In] in Hr. repeat (destruct Hr as [<- | Hr];
             [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ET9, unsigned_lit_small in Hw by lia; lia |]).
           destruct Hr. }
         assert (DwkC : wkept B lyc Sc W sp1 mC mD).
         { apply (wkept_of_run B LAWS ET (ss_mem ss_s1t) lyc Sc W mC mD dC sp1 (proj1 Cjr)); [exact Dfrr | exact Dgr | exact Dwin | rewrite WS; lia | lia |].
           intros a Ha. apply Cpres. rewrite FFS. rewrite WS in Ha. lia. }
         assert (Dm216 : val_mem SEGS (mrestrict (w_H W) mD) (sp1 + 216) 8 bimg).
         { apply (val_mem_frame ET (ss_mem ss_s1t) _ _ _ _ _ Dfrr); [ | lia | lia | exact Cm216].
           intros q Hq Hin. apply Dwin2 in Hin. lia. }
         pose proof Djr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dpres & _).
         apply (BR W ET ssD msD dD (s1o_postX i) BC_NE (SOff 33 1) (SOff 34 0) Dst).
         ++ intros Dtk Dst1.
            assert (Dne : i + 1 <> Hd).
            { intros Heq. revert Dtk. cbn [branch_taken]. rewrite (Soff0 _ _ _ ET34). cbn [sv_denot].
              rewrite ET33, YP0n.Z_to_bv_unsigned_add, Heq, bv_eqb_refl. cbn [negb]. intro Hf. discriminate Hf. }
            assert (Fwin : forall a, in_wrange ET (ss_mem (add_cond ssD {| ac_c := BC_NE; ac_a := SOff 33 1; ac_b := SOff 34 0 |})) a ->
              sp1 + 160 <= a < sp1 + 168 \/ sp1 + 192 <= a < sp1 + 200).
            { intros a (r & Hr & Hw). lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end.
              cbn [In] in Hr. repeat (destruct Hr as [<- | Hr];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ET9, unsigned_lit_small in Hw by lia; lia |]).
              destruct Hr. }
            lazymatch eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 20 6868 (add_cond ssD {| ac_c := BC_NE; ac_a := SOff 33 1; ac_b := SOff 34 0 |})) with
            | (?sF, ?stF) => pose (ssF := sF);
              refine (RUNTOP W 20 6868 ET _ ssF stF msD TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc dD k (s1o_postX i) _ Dst1 _ _ Djr _ _)
            end.
            ** apply Eimg_env.
            ** vm_compute. reflexivity.
            ** exact I.
            ** intros a Ha. left. apply Fwin in Ha. rewrite FFS. lia.
            ** unfold run_post_pi_AJ. intros msF matF Fst Fjr Ffr Ffrr Fgr.
               pose proof (st_ok_pi_restrict_mkst _ _ _ _ Fst eq_refl) as Fshape.
               set (rF := ms_regs msF) in *. set (mF := ms_mem msF) in *. set (dF := with_vm_backing (m_vm_lazy dD) matF dD) in *.
               rewrite Fshape in Fst |- *. rewrite restrict_mkst_fx in Fst.
               pose proof (st_ok_regs_ok _ _ _ _ Fst) as Frg. unfold regs_ok in Frg.
               change (forall r, getr rF r = sv_denot ET (sr_get (ss_regs ssF) r)) in Frg.
               pose proof (st_ok_pi_region_nth _ _ _ 3 _ Fst eq_refl) as Freg4. cbn [ms_mem] in Freg4.
               eapply SRr_mono.
               { apply (Onward (i + 1) rF mF dF).
                 - lia.
                 - lia.
                 - exact Fjr.
                 - apply (wkept_trans _ _ _ _ _ _ _ _ Cwk). apply (wkept_trans _ _ _ _ _ _ _ _ DwkC).
                   apply (wkept_of_run B LAWS ET (ss_mem (add_cond ssD {| ac_c := BC_NE; ac_a := SOff 33 1; ac_b := SOff 34 0 |})) lyc Sc W mD mF dD sp1 (proj1 Djr)); [exact Ffrr | exact Fgr | | rewrite WS; lia | lia |].
                   + intros a Ha. apply Fwin in Ha. unfold wscr. lia.
                   + intros a Ha. apply Dpres. rewrite FFS. rewrite WS in Ha. lia.
                 - intros r Hr. rewrite <- (Ckp r Hr). unfold WKEPT5 in Hr.
                   destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; rewrite Frg, ETreg; reflexivity.
                 - rewrite <- Cr6, Frg, ETreg. reflexivity.
                 - rewrite <- Cr25, Frg, ETreg. reflexivity.
                 - rewrite <- Cr24, Frg, ETreg. reflexivity.
                 - rewrite Frg. change (sv_denot ET (SOff 33 1) = Z_to_bv 64 (i + 1)). cbn [sv_denot].
                   rewrite ET33. apply YP0n.Z_to_bv_unsigned_add.
                 - rewrite Frg. change (sv_denot ET (SAlu ALU_ADD (SOff 32 0) (SOff 35 0)) = Z_to_bv 64 (fimg + (i + 1) * Wd)).
                   rewrite (denot_add_atoms ET 32 35 Wd (fimg + i * Wd) ET32 ET35) by nia. f_equal; lia.
                 - rewrite Frg. change (sv_denot ET (SAlu ALU_ADD (SOff 19 0) (SOff 32 0)) = Z_to_bv 64 (fimg + (i + 1) * Wd)).
                   rewrite (denot_add_atoms ET 19 32 (fimg + i * Wd) Wd ET19 ET32) by nia. f_equal; lia.
                 - rewrite Frg. change (sv_denot ET (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) = Z_to_bv 64 (bimg + (i + 1) * Wd)).
                   rewrite (denot_add_atoms ET 18 32 (bimg + i * Wd) Wd ET18 ET32) by nia. f_equal; lia.
                 - rewrite Frg. change (sv_denot ET (SAlu ALU_ADD (SOff 18 0) (SOff 32 0)) = Z_to_bv 64 (bimg + (i + 1) * Wd)).
                   rewrite (denot_add_atoms ET 18 32 (bimg + i * Wd) Wd ET18 ET32) by nia. f_equal; lia.
                 - rewrite Frg. exact (Soff0 _ _ _ ET32).
                 - apply (field_of_region ET _ 9 sp1 _ _ _ _ _ 192 8 (SAluw ALU_ADD (SOff 36 0) (SLit 1)) (i + 1) Freg4).
                   + rewrite ET9. apply unsigned_lit_small. lia.
                   + left. reflexivity.
                   + cbn [sv_denot]. rewrite ET36, YP0n.Z_to_bv_unsigned_add, zalu32_sound. f_equal.
                     unfold zalu32, zcanon, bv_swrap, zu32. cbn [zalu_raw]. unfold bv_wrap, bv_half_modulus, bv_modulus, M32, M64.
                     change (2 ^ Z.of_N 32 / 2) with 2147483648. change (2 ^ Z.of_N 32) with 4294967296.
                     rewrite (Z.mod_small (i + 0)), (Z.mod_small 1) by lia.
                     rewrite (Z.mod_small (i + 0 + 1 + 2147483648)) by lia. rewrite Z.mod_small by lia. lia.
                   + lia.
                   + lia.
                 - apply (val_mem_frame ET _ _ _ _ _ _ Ffrr); [ | lia | lia | exact Dm216].
                   intros q Hq Hin. apply Fwin in Hin. lia. }
               intros Wn cn _ (Weq & regsn & memn & mdn & pcn & Ceq & Pj & Pk & Pr & P6 & P21 & P22 & P216 & Px).
               split; [exact Weq |]. exists regsn, memn, mdn, pcn.
               do 8 (split; [assumption |]).
               destruct Px as [(Hpc & top & cw & Rtop & Pfound) | (Hpc & Pnf)].
               --- left. split; [exact Hpc |]. exists top, cw. split; [lia |].
                   destruct Pfound as (Rcw & Pcw & P19 & P10 & P15 & P24 & P184 & Pbefore).
                   do 7 (split; [assumption |]).
                   intros p Hp. destruct (Z_lt_le_dec p (i * Wd + Wd)) as [Hlo | Hhi]; [apply Cflat; lia | apply Pbefore; nia].
               --- right. split; [exact Hpc |].
                   destruct Pnf as (P27 & P23 & P26 & P160 & P10 & P11 & P18 & P20 & Pnone).
                   do 8 (split; [assumption |]).
                   intros p Hp. destruct (Z_lt_le_dec p (i * Wd + Wd)) as [Hlo | Hhi]; [apply Cflat; lia | apply Pnone; nia].
         ++ intros Dnt Dst1.
            assert (Deq : i + 1 = Hd).
            { revert Dnt. cbn [branch_taken]. rewrite (Soff0 _ _ _ ET34). cbn [sv_denot].
              rewrite ET33, YP0n.Z_to_bv_unsigned_add, YN32.eqb_w by lia.
              destruct (Z.eqb_spec (i + 1) Hd); cbn [negb]; [auto | intro Hf; discriminate Hf]. }
            assert (Gwin : forall a, in_wrange ET (ss_mem (add_cond ssD {| ac_c := neg_bc BC_NE; ac_a := SOff 33 1; ac_b := SOff 34 0 |})) a ->
              sp1 + 160 <= a < sp1 + 168 \/ sp1 + 192 <= a < sp1 + 200).
            { intros a (r & Hr & Hw). lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end.
              cbn [In] in Hr. repeat (destruct Hr as [<- | Hr];
                [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ET9, unsigned_lit_small in Hw by lia; lia |]).
              destruct Hr. }
            lazymatch eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 20 8076 (add_cond ssD {| ac_c := neg_bc BC_NE; ac_a := SOff 33 1; ac_b := SOff 34 0 |})) with
            | (?sG, ?stG) => pose (ssG := sG);
              refine (RUNTOP W 20 8076 ET _ ssG stG msD TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc dD k (s1o_postX i) _ Dst1 _ _ Djr _ _)
            end.
            ** apply Eimg_env.
            ** vm_compute. reflexivity.
            ** exact I.
            ** intros a Ha. left. apply Gwin in Ha. rewrite FFS. lia.
            ** unfold run_post_pi_AJ. intros msG matG Gst Gjr Gfr Gfrr Ggr.
               pose proof (st_ok_pi_restrict_mkst _ _ _ _ Gst eq_refl) as Gshape.
               set (rG := ms_regs msG) in *. set (mG := ms_mem msG) in *. set (dG := with_vm_backing (m_vm_lazy dD) matG dD) in *.
               rewrite Gshape in Gst |- *. rewrite restrict_mkst_fx in Gst.
               pose proof (st_ok_regs_ok _ _ _ _ Gst) as Grg. unfold regs_ok in Grg.
               change (forall r, getr rG r = sv_denot ET (sr_get (ss_regs ssG) r)) in Grg.
               pose proof (st_ok_pi_region_nth _ _ _ 1 _ Gst eq_refl) as Greg2. cbn [ms_mem] in Greg2.
               apply SRr_ret. split; [reflexivity |].
               exists rG, mG, dG, (BASE + 8076). split; [reflexivity |].
               split; [exact Gjr |].
               split.
               { apply (wkept_trans _ _ _ _ _ _ _ _ Cwk). apply (wkept_trans _ _ _ _ _ _ _ _ DwkC).
                 apply (wkept_of_run B LAWS ET (ss_mem (add_cond ssD {| ac_c := neg_bc BC_NE; ac_a := SOff 33 1; ac_b := SOff 34 0 |})) lyc Sc W mD mG dD sp1 (proj1 Djr)); [exact Gfrr | exact Ggr | | rewrite WS; lia | lia |].
                 - intros a Ha. apply Gwin in Ha. unfold wscr. lia.
                 - intros a Ha. apply Dpres. rewrite FFS. rewrite WS in Ha. lia. }
               split.
               { intros r Hr. rewrite <- (Ckp r Hr). unfold WKEPT5 in Hr.
                 destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; rewrite Grg, ETreg; reflexivity. }
               split; [rewrite <- Cr6, Grg, ETreg; reflexivity |].
               split; [rewrite <- Cr25, Grg, ETreg; reflexivity |].
               split; [rewrite <- Cr24, Grg, ETreg; reflexivity |].
               split.
               { apply (val_mem_frame ET _ _ _ _ _ _ Gfrr); [ | lia | lia | exact Dm216].
                 intros q Hq Hin. apply Gwin in Hin. lia. }
               right. split; [reflexivity |].
               split; [rewrite Grg; reflexivity |].
               split; [rewrite Grg; reflexivity |].
               split; [rewrite Grg; reflexivity |].
               split; [apply (field_of_region ET _ 9 sp1 _ _ _ _ _ 160 8 (SLit 1) 1 Greg2); [rewrite ET9; apply unsigned_lit_small; lia | left; reflexivity | reflexivity | lia | lia] |].
               split; [rewrite Grg; exact (Soff0 _ _ _ ET38) |].
               split; [rewrite Grg; exact (Soff0 _ _ _ ET39) |].
               split; [rewrite Grg; exact (Soff0 _ _ _ ET40) |].
               split; [rewrite Grg; exact (Soff0 _ _ _ ET41) |].
               intros p Hp; apply Cflat; nia.
    * apply SRr_ret.
      split; [reflexivity |].
      exists rC, mC, dC, (BASE + 7196). split; [reflexivity |].
      split; [exact Cjr |]. split; [exact Cwk |]. split; [exact Ckp |].
      split; [exact Cr6 |]. split; [exact Cr21 |]. split; [exact Cr22 |]. split; [exact Cm216 |].
      left. split; [reflexivity |].
      destruct Cfound as (cw & Rcw & Pcw).
      exists i, cw. split; [lia |]. split; [exact Rcw |]. split; [exact Pcw |].
      split; [exact Cr19 |]. split; [exact Cr10 |]. split; [exact Cr15 |].
      split. { rewrite Ccl by reflexivity. rewrite <- Ar24, Brg, EAreg. reflexivity. }
      split; [apply (val_mem_lkept W sp1 mB mC); [exact Clk | lia | lia | exact Bm184] |].
      intros p Hp; nia.
Qed.
Lemma fl_s1oX : forall m, s1o_stmtX m.
Proof. induction m as [|m IH]; [unfold s1o_stmtX; intros; exfalso; lia | exact (fl_s1o_stepX m IH)]. Qed.
End j.
End f.
End d.
End c.
