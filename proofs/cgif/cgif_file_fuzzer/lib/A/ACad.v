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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0y YC4a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC44.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACbk AC8a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8h AC8j ACbc ACbf ACbd ACab ACai ACam ACan ACac.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma il_rows1 : forall h mm, 1 <= h -> 1 <= mm -> 0 + 8 * (mm - 1) < h -> h <= 0 + 8 * mm -> mm = (h + 7) / 8.
Proof. intros. lia. Qed.
Lemma il_rows2 : forall h mm, 1 <= h -> 1 <= mm -> 4 + 8 * (mm - 1) < h -> h <= 4 + 8 * mm -> mm = (h + 3) / 8.
Proof. intros. lia. Qed.
Lemma il_rows3 : forall h mm, 1 <= h -> 1 <= mm -> 2 + 4 * (mm - 1) < h -> h <= 2 + 4 * mm -> mm = (h + 1) / 4.
Proof. intros. lia. Qed.
Lemma il_bound2 : forall h j, 1 <= h -> 0 <= j -> 4 + 8 * j < h -> (h + 7) / 8 + j + 1 <= h.
Proof. intros. lia. Qed.
Lemma il_bound3 : forall h j, 1 <= h -> 0 <= j -> 2 + 4 * j < h -> (h + 7) / 8 + (h + 3) / 8 + j + 1 <= h.
Proof. intros. lia. Qed.
Lemma il_bound4 : forall h j, 1 <= h -> 0 <= j -> 1 + 2 * j < h -> (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 + j + 1 <= h.
Proof. intros. lia. Qed.
Lemma il_rows_le : forall h, 1 <= h -> 1 <= (h + 7) / 8 /\ 0 <= (h + 3) / 8 /\ 0 <= (h + 1) / 4 /\ (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 + h / 2 = h.
Proof. intros. lia. Qed.
Lemma il_skip2 : forall h, 1 <= h < 5 -> (h + 3) / 8 = 0. Proof. intros. lia. Qed.
Lemma il_skip3 : forall h, 1 <= h < 3 -> (h + 1) / 4 = 0. Proof. intros. lia. Qed.
Lemma il_rows4 : forall h mm, 1 <= h -> 1 <= mm -> 1 + 2 * (mm - 1) < h -> h <= 1 + 2 * mm -> mm = h / 2.
Proof. intros. lia. Qed.
Lemma il_skip4 : forall h, 1 <= h < 2 -> (h + 7) / 8 + (h + 3) / 8 + (h + 1) / 4 = h. Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac iln_obl HJx Hx25 Hx32 cfp LAWS Hfin Hcid0 Hflo Hfhi Hfal Hrh C2 C3 HAR0 HRA :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 25 ?c)) ?len =>
first [ rewrite (U_atom_off Ex 25 (cfp + 8) c Hx25) by lia | rewrite (U_atom Ex 25 (cfp + 8) Hx25) by lia ];
eapply (obl_of_range _ _ _ Ex (SOff 32 0) _ len cfp 40);
[ eapply (range_addressable_entry_frame _ _ LAWS); [exact HJx | exact Hfin | exact Hcid0 | exact Hflo | exact Hfhi | exact Hfal
| let x := fresh "x" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Hxr := fresh "Hxr" in
intros x (rg & Hrg & Hxr); cbn [In] in Hrg; destruct Hrg as [<- | []]; cbn [fst snd] in Hxr; clear - Hxr Hrh C2 C3; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; change (req_size RAW_SIZE) with 48 in *; lia
| exact HAR0 | exact HRA ]
| rewrite (U_atom Ex 32 SB Hx32); [reflexivity | unfold SB; lia] | lia | lia ] end.
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
Section f.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA AS_asan_memcpy).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_asan3_1) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_asan3_1 PI.
Hypothesis TLF : PALibF B.
Hypothesis HGOT9 : forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 9)) 8 (BASE + AF_asan3_cgif_raw_addframe).
Variable CTX : list (list Z).
Hypothesis HDEEP : forall c, In c CTX -> (2 <= length c)%nat.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Definition IL_CLOB : list (bv 5) := ILN_CLOB.
Definition ilg_facts : facts :=
mkFacts [ (2%nat, mkAF 70368744177664 140737488355328 4); (27%nat, HPTR 0); (25%nat, HPTR 3); (33%nat, HPTR 0);
(34%nat, mkAF 1 65535 0); (35%nat, mkAF 1 65535 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_ilg (pc : Z) (rh : bv 5) : sstate := mkSS pc (sr_set iln_regs rh (SOff 35 0)) iln_regions None ilg_facts.
Definition il_at (pcX RX : Z) W (regs : bvmap 5 word) (memc : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k (fpos raw pint w h : Z)
: world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 pcX) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TRAWADD_STK sp0 [(raw + 40, raw + 44)] ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
getr regs' 27 = Z_to_bv 64 (pint + w * RX) /\ getr regs' 10 = Z_to_bv 64 h /\
(forall r : bv 5, reg_in r IL_CLOB = false -> getr regs' r = getr regs r) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a).
Definition il_done W (regs : bvmap 5 word) (memc : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k (fpos raw pint w h : Z)
: world SEGS -> config -> Prop := il_at (BASE + 0xd64) h W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h.
Lemma il_at_after : forall pcX RX W (regs regsX : bvmap 5 word) (memc memX : word -> option byte) sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h,
(forall r : bv 5, reg_in r IL_CLOB = false -> getr regsX r = getr regs r) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + w * h) -> ~ (sp0 - 320 - ESTACK <= a < sp0 - 320) ->
aview SEGS (w_H W) memX a = aview SEGS (w_H W) memc a) ->
(forall a, apresent (w_H W) memc a -> apresent (w_H W) memX a) ->
forall W' c', il_at pcX RX W regsX memX sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h W' c' ->
il_at pcX RX W regs memc sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h W' c'.
Proof.
intros pcX RX W regs regsX memc memX sp0 ly S W0 mem0 md0 lyc Sc k fpos raw pint w h HK Hout Hpres W' c'
(-> & regs' & mem' & md' & -> & HJ & P27 & P10 & HK' & Hout' & Hpres').
split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact P27|]. split; [exact P10|].
split; [intros r Hr; rewrite (HK' r Hr); exact (HK r Hr)|].
split; [intros a Ha Hna Hnb; rewrite (Hout' a Ha Hna Hnb); exact (Hout a Ha Hna Hnb)|].
intros a Ha. apply Hpres', Hpres, Ha.
Qed.
Lemma il_cells_kept : forall H (memc mm : word -> option byte) lo hi pint L cfp img w h,
(forall a, 0 <= a < 2 ^ 64 -> ~ (pint <= a < pint + L) -> ~ (lo <= a < hi) -> aview SEGS H mm a = aview SEGS H memc a) ->
0 <= cfp -> cfp + 40 <= 2 ^ 64 -> (pint + L <= cfp \/ cfp + 40 <= pint) -> (cfp + 40 <= lo \/ hi <= cfp) ->
val_mem SEGS (mrestrict H memc) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict H memc) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict H memc) (cfp + 22) 2 h ->
val_mem SEGS (mrestrict H mm) (cfp + 8) 8 img /\ val_mem SEGS (mrestrict H mm) (cfp + 20) 2 w /\ val_mem SEGS (mrestrict H mm) (cfp + 22) 2 h.
Proof.
intros H memc mm lo hi pint L cfp img w h Hout H0 H64 Hs1 Hs2 (V1 & V2 & V3).
split; [|split]; (eapply val_mem_kept; [| first [exact V1 | exact V2 | exact V3]]); intros q Hq; apply Hout; lia.
Qed.
Lemma il_slot_kept : forall H (memc mm : word -> option byte) lo hi pint L a v,
(forall x, 0 <= x < 2 ^ 64 -> ~ (pint <= x < pint + L) -> ~ (lo <= x < hi) -> aview SEGS H mm x = aview SEGS H memc x) ->
0 <= a -> a + 8 <= 2 ^ 64 -> (pint + L <= a \/ a + 8 <= pint) -> (a + 8 <= lo \/ hi <= a) ->
val_mem SEGS (mrestrict H memc) a 8 v -> val_mem SEGS (mrestrict H mm) a 8 v.
Proof.
intros H memc mm lo hi pint L a v Hout H0 H64 Hs1 Hs2 V. eapply val_mem_kept; [| exact V]. intros q Hq. apply Hout; lia.
Qed.
End f.
End e.
End d.
