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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACjm.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACjj.
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
Lemma U_idx16 : forall E ny nw nx y w x, ew E ny = Z_to_bv 64 y -> ew E nw = Z_to_bv 64 w -> ew E nx = Z_to_bv 64 x ->
0 <= y < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= x < 2 ^ 16 ->
U E (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff ny 0) (SLit 65535)) (SOff nw 0)) (SAlu ALU_AND (SOff nx 0) (SLit 65535))) = y * w + x.
Proof.
intros E ny nw nx y w x Hy Hw Hx Ry Rw Rx.
assert (H1 : U E (SAlu ALU_AND (SOff ny 0) (SLit 65535)) = y) by (apply U_and16; [apply (U_atom E ny y Hy); lia | lia]).
assert (H2 : U E (SAlu ALU_AND (SOff nx 0) (SLit 65535)) = x) by (apply U_and16; [apply (U_atom E nx x Hx); lia | lia]).
assert (H3 : U E (SMd M_MUL (SAlu ALU_AND (SOff ny 0) (SLit 65535)) (SOff nw 0)) = y * w) by (apply U_mul_small1; [exact H1 | apply (U_atom E nw w Hw); lia | lia | lia | nia]).
apply U_add_small2; [exact H3 | exact H2 | nia | lia | nia].
Qed.
Lemma U_add_not_ltu : forall E nx na nb x a b c, ew E nx = Z_to_bv 64 x -> ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
0 <= x -> x + 1 < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> 0 <= a + c < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nx 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SOff na c) (SOff nb 0)) (SLit 1))) = x + (if a + c <? b then 0 else 1).
Proof.
intros E nx na nb x a b c Hx Ha Hb Rx Rx1 Ra Rac Rb.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E nx x Hx), (U_atom_off E na a c Ha), (U_atom E nb b Hb), U_SLit by lia. change (zcanon 1) with 1.
destruct (a + c <? b); [change (zcanon 1) with 1; change (Z.lxor 1 1) with 0; change (zcanon 0) with 0 | change (zcanon 0) with 0; change (Z.lxor 0 1) with 1; change (zcanon 1) with 1];
apply zcanon_id; rewrite M64_val; lia.
Qed.


Lemma U_lin_sub_zext16 : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= a <= b -> b < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff na 0) (SLit 5192296858534827628249021352509440)) (SAlu ALU_SLL (SOff nb 0) (SLit 48))) (SLit 48)) = b - a.
Proof.
intros E na nb a b Ha Hb Rab Rb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E na a Ha), (U_atom E nb b Hb), !U_SLit by lia. rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
change (zcanon 5192296858534827628249021352509440) with (2 ^ 64 - 2 ^ 48).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (b * 2 ^ 48)) by (rewrite M64_val; change (2 ^ 48) with 281474976710656 in *; lia).
replace (zcanon (zcanon (a * (2 ^ 64 - 2 ^ 48)) + b * 2 ^ 48)) with ((b - a) * 2 ^ 48).
2: { unfold zcanon. rewrite M64_val. rewrite Zplus_mod_idemp_l. replace (a * (2 ^ 64 - 2 ^ 48) + b * 2 ^ 48) with ((b - a) * 2 ^ 48 + a * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. change (2 ^ 48) with 281474976710656 in *. lia. }
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_lin_sub_c : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= a <= b -> b < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nb 0) (SMd M_MUL (SOff na 0) (SLit 18446744073709551615))) = b - a.
Proof.
intros E na nb a b Ha Hb Rab Rb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E na a Ha), (U_atom E nb b Hb), U_SLit by lia. unfold zcanon. rewrite M64_val.
rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_r. replace (b + a * 18446744073709551615) with ((b - a) + a * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_lin_sub_zext16_c : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= a <= b -> b < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff nb 0) (SLit 48)) (SMd M_MUL (SOff na 0) (SLit 5192296858534827628249021352509440))) (SLit 48)) = b - a.
Proof.
intros E na nb a b Ha Hb Rab Rb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E na a Ha), (U_atom E nb b Hb), !U_SLit by lia. rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
change (zcanon 5192296858534827628249021352509440) with (2 ^ 64 - 2 ^ 48).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (b * 2 ^ 48)) by (rewrite M64_val; change (2 ^ 48) with 281474976710656 in *; lia).
replace (zcanon (b * 2 ^ 48 + zcanon (a * (2 ^ 64 - 2 ^ 48)))) with ((b - a) * 2 ^ 48).
2: { unfold zcanon. rewrite M64_val. rewrite Zplus_mod_idemp_r. replace (b * 2 ^ 48 + a * (2 ^ 64 - 2 ^ 48)) with ((b - a) * 2 ^ 48 + a * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. change (2 ^ 48) with 281474976710656 in *. lia. }
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Section e.
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
Section f.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HFIMG : val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Let CALL := cmp_callW B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112).
Ltac wprelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac off_windows E9 :=
cbn [ss_mem]; let kk := fresh "kk" in let Hk := fresh "Hk" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros kk Hk (r & Hr & Hw); cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_havoc_old in Hw by lia;
cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_ewset_other in Hw by lia; rewrite E9, unsigned_lit_small in Hw by lia; lia |]);
destruct Hr.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Ltac evE_in H := rewrite ?ew_havoc_old in H by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in H; rewrite ?ew_ewset_other in H by lia.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition S3_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 23; 24; 27; 28; 29; 30; 31]%bv.
Definition S3_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 21; 22; 25; 26]%bv.
Lemma s3_clob_cases : forall r : bv 5, reg_in r S3_CLOB = false -> r = 0%bv \/ In r S3_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Definition s3_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 216 256 216 216 [YP09.mkChunk 216 (CVal 8 (SOff 32 0)); YP09.mkChunk 224 (CVal 8 (SOff 38 0)); YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 160 168 160 168 [];
YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))];
YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))] ].
Definition s3_regs := sr_set sr_atoms 27%bv (SLit 65535).
Definition s3_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (18%nat, mkAF 0 65534 0); (23%nat, mkAF 0 65534 0);
(19%nat, mkAF 0 65534 0); (26%nat, mkAF 1 65535 0); (25%nat, mkAF 1 65535 0); (38%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3);
(32%nat, HPTR 0); (33%nat, HPTR 3); (34%nat, HPTR 0); (35%nat, mkAF 0 255 0); (36%nat, HPTR 0); (37%nat, mkAF 0 255 0) ] [] [].
Definition ss_s3 : sstate := mkSS 0x1dfc s3_regs s3_mem None s3_facts.
Definition s3_postX (c0 top bot : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' left,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x1ec8)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
0 <= left <= c0 /\ getr regs' 23 = Z_to_bv 64 left /\ getr regs' 18 = Z_to_bv 64 (Wd - 1) /\ getr regs' 19 = Z_to_bv 64 65535 /\
getr regs' 27 = Z_to_bv 64 top /\ getr regs' 20 = Z_to_bv 64 top /\ getr regs' 26 = Z_to_bv 64 (bot + 1) /\
getr regs' 25 = Z_to_bv 64 Wd /\ getr regs' 24 = Z_to_bv 64 bimg /\ getr regs' 14 = Z_to_bv 64 SB /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 216) 8 bimg /\ val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 (bot + 1 - top) /\
(exists y', top <= y' < bot + 1 /\ PDp (y' * Wd + left)) /\ (forall i x', top <= i < bot + 1 -> 0 <= x' < left -> ~ PDp (i * Wd + x')).
Definition s3_stmtX (m : nat) : Prop :=
forall (x y c0 top bot : Z) (regsE : bvmap 5 word) memE mdE,
(c0 - x) * Hd + (bot - y) < Z.of_nat m -> 0 <= x <= c0 -> c0 < Wd -> 0 <= top -> top <= y <= bot -> bot < Hd -> (x < c0 \/ y = top) -> PDp (top * Wd + c0) ->
(forall i x', top <= i < bot + 1 -> 0 <= x' -> (x' < x \/ (x' = x /\ i < y)) -> ~ PDp (i * Wd + x')) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp -> getr regsE 27 = Z_to_bv 64 65535 ->
getr regsE 18 = Z_to_bv 64 y -> getr regsE 23 = Z_to_bv 64 x -> getr regsE 19 = Z_to_bv 64 top -> getr regsE 26 = Z_to_bv 64 (bot + 1) ->
getr regsE 25 = Z_to_bv 64 Wd -> getr regsE 24 = Z_to_bv 64 (bot + 1 - top) ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1dfc)) memE (seg_rom SEGS)) mdE) (s3_postX c0 top bot).
Lemma fl_s3l_stepX : forall m, s3_stmtX m -> s3_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold s3_stmtX.
intros x y c0 top bot regsE memE mdE Hm Hx Hc0 Ht0 Hy Hbt Hxw HPDw XACC HJE WK HKE E6 E21r E22r E27r E18r E23r E20r E26r E24r E19r V224.
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
assert (HyW : 0 <= y * Wd <= (Hd - 1) * Wd) by (clear - Hy Hbt Ht0 RW RH; nia).
assert (HW1 : (Hd - 1) * Wd = Hd * Wd - Wd) by (clear; lia).
assert (Hp : 0 <= y * Wd + x /\ y * Wd + x < Nb) by (rewrite HN; clear - Hx Hc0 HyW HW1 RW RH; nia).
assert (Hp32 : y * Wd + x < 2 ^ 32) by (clear - Hp HN RW RH; nia).
set (p := y * Wd + x) in *.
assert (HSpresE : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as [VbC RbC].
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as [VbB RbB].
set (bC := bval (aview SEGS (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 248 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as VfimgE.
remember (Eimg (Ereg regsE [Z_to_bv 64 bimg; Z_to_bv 64 bfp; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 fimg])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 bimg; Z_to_bv 64 bfp; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 fimg]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite E18r in E18. pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23.
pose proof (EE 19%nat 19%bv eq_refl) as E20. rewrite E20r in E20. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 25%nat 25%bv eq_refl) as E24. rewrite E24r in E24. assert (E25 : ew E 38 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 6)).
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
pose proof (EE 24%nat 24%bv eq_refl) as E19. rewrite E19r in E19.
assert (E32 : ew E 32 = Z_to_bv 64 bimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (fimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 bC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (bimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 bB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 5)).
assert (HS : st_ok_pi SEGS VAL E ss_s3 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1dfc)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s3, s3_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1dfc) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E27r; reflexivity].
- reflexivity.
- unfold s3_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ bimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V224]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E25, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VfimgE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite F6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HSpresE; lia|]. apply Forall_nil.
+ rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
- unfold s3_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E9, E34, E36, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s3_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E18, E23, E20, E26, E24, E25, E21, E22, E32, E33, E34, E35, E36, E37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1e1c.
1: { unfold s3_mem. repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr1. rename HG into HG1. clear HF.
assert (O1 : forall kk, sp1 + 216 <= kk < sp1 + 224 -> ~ in_wrange E (ss_mem ss_s3) kk).
{ unfold ss_s3, s3_mem; cbn [ss_mem]. intros kk Hk (r & Hr & Hw); cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [rewrite E9, unsigned_lit_small in Hw by lia; lia | rewrite E9, unsigned_lit_small in Hw by lia; lia | lia | lia]. }
assert (W1 : forall a, in_wrange E (ss_mem ss_s3) a -> wscr sp1 a).
{ unfold ss_s3, s3_mem; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia | lia | lia]. }
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 W1 ltac:(lia) ltac:(lia) HSpresE)) as WK1.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 216) 8 bimg HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V224) as V224a.
cbn [ms_mem restrict mkst] in V224a.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
assert (F25 : ew Ev 38 = Z_to_bv 64 fimg) by (evE; exact E25);
assert (F18 : ew Ev 18 = Z_to_bv 64 y) by (evE; exact E18); assert (F24 : ew Ev 25 = Z_to_bv 64 Wd) by (evE; exact E24); assert (F23 : ew Ev 23 = Z_to_bv 64 x) by (evE; exact E23);
assert (F34 : ew Ev 34 = Z_to_bv 64 (fimg + p)) by (evE; exact E34);
assert (UI : U Ev (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 18 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 23 0) (SLit 65535))) = p) by (apply (U_idx16 Ev 18 25 23 y Wd x F18 F24 F23); lia);
assert (UA : U Ev (SAlu ALU_ADD (SOff 38 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 18 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 23 0) (SLit 65535))) (SLit 32)) (SLit 32))) = fimg + p)
by (rewrite (U_add_atom_zext32 Ev 38 _ fimg F25) by lia; rewrite UI, Z.mod_small by lia; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Ra0;
pose proof (st_ok_pin_rege Ev ssv msv 10%bv (SOff 34 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJE) as HAR2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1e34.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 34 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 34 (fimg + p) cc ltac:(evE; exact E34)) by lia | rewrite (U_atom Ex 34 (fimg + p) ltac:(evE; exact E34)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR2 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | |- awr_ok _ _ _ _ _ _ _ => idtac "AWR" | |- ?g => idtac "OTHER" g end.
1: { repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | evE; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
all: match goal with |- ?g => idtac "AWR-LEFT" g end. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK1 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia | lia | lia])
ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia | lia | lia]) V224a) as V224b.
cbn [ms_mem restrict mkst] in V224b.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
assert (G32 : ew Ev 32 = Z_to_bv 64 bimg) by (evE; exact E32);
assert (G18 : ew Ev 18 = Z_to_bv 64 y) by (evE; exact E18); assert (G24 : ew Ev 25 = Z_to_bv 64 Wd) by (evE; exact E24); assert (G23 : ew Ev 23 = Z_to_bv 64 x) by (evE; exact E23);
assert (G36 : ew Ev 36 = Z_to_bv 64 (bimg + p)) by (evE; exact E36);
assert (UI2 : U Ev (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 18 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 23 0) (SLit 65535))) = p) by (apply (U_idx16 Ev 18 25 23 y Wd x G18 G24 G23); lia);
assert (UB : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 18 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 23 0) (SLit 65535))) (SLit 32)) (SLit 32))) = bimg + p)
by (rewrite (U_add_atom_zext32 Ev 32 _ bimg G32) by lia; rewrite UI2, Z.mod_small by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Ra1;
pose proof (st_ok_pin_rege Ev ssv msv 11%bv (SOff 36 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra1; cbn [sv_denot]; rewrite G36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJE) as HAR3.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan AF_asan3_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 36 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 36 (bimg + p) cc ltac:(evE; exact E36)) by lia | rewrite (U_atom Ex 36 (bimg + p) ltac:(evE; exact E36)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR3 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | evE; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
all: match goal with |- ?g => idtac "AWR-LEFT" g end. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia | lia | lia])
ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr3 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia | lia | lia]) V224b) as V224c.
cbn [ms_mem restrict mkst] in V224c.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S3_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr3. cbn [ms_regs restrict] in HKr3.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX p (Z_to_bv 64 (BASE + 0x1e5c)) HJE WK3) end.
- lia.
- unfold spZ. rewrite Qsp; evE. rewrite (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp; evE. rewrite (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp; evE. rewrite (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- unfold s0Z. rewrite Qs0; evE. rewrite (EE 8%nat 8%bv eq_refl), (HKE 8%bv ltac:(cbv; tauto)). exact Hs0.
- rewrite Qa0; evE. exact E21. - rewrite Qa1; evE. exact E22. - rewrite Qa2; evE. exact E33. - rewrite Qa3; evE. exact E35. - rewrite Qa4; evE. exact E37.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. - rewrite unsigned_lit_small by lia. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hz & WK4 & Kc & Lc).
clear Qa0 Qa1 Qa2 Qa3 Qa4 Qra Qsp Qgp Qtp Qs0.
assert (HSpres2 : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 216) 8 _ Lc ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V224c) as V224d.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 6 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 6%nat.
pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | evE; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK4 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia])
ltac:(lia) ltac:(lia) HSpres2)) as WK5.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr4 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia]) V224d) as V224e.
cbn [ms_mem restrict mkst] in V224e.
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ =>
assert (G6 : ew Ecur 6 = Z_to_bv 64 SB) by (evE; exact F6);
assert (G9 : ew Ecur 9 = Z_to_bv 64 sp1) by (evE; exact E9) end.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (HPD : PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
intros HZ; apply Hc; lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
evE; unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros HP; exact (HP HZ) end. }
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1ec8.
1: { repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | evE; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
all: match goal with |- ?g => idtac "AWR-LEFT" g end. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK5 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia])
ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia]) V224e) as V224f.
cbn [ms_mem restrict mkst] in V224f.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SOff 24 0) (bot + 1 - top) HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; evE; rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V120 end; clear HR1 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V120.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S3_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (23%bv : bv 5) R23. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19. prreg HS (27%bv : bv 5) R27.
prreg HS (20%bv : bv 5) R20x. prreg HS (24%bv : bv 5) R24x. prreg HS (14%bv : bv 5) R14x.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, x end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 S3_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [exact Hx|]. split; [rewrite R23; evE; exact E23|].
split; [rewrite R18; evE; rewrite E24, unsigned_lit_small by lia; f_equal; lia|]. split; [exact R19|].
split; [rewrite R27; evE; exact E20|]. split; [rewrite R20x; evE; exact E20|].
split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E24r|].
split; [rewrite R24x; evE; exact E32|]. split; [rewrite R14x; evE; exact F6|].
split; [exact V224f|]. split; [exact V120|].
split; [exists y; split; [clear - Hy; lia | exact HPD] | intros i' x' Hi' Hx'; apply XACC; [exact Hi' | clear - Hx'; lia | left; clear - Hx'; lia]].
-
assert (HnPD : ~ PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
lazymatch goal with |- getr regs2 10 = w64 0 =>
enough (Hvz : U Ex (SOff n 0) = bv_unsigned (getr regs2 10)) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hvz; exact Hc) end;
rewrite U_SOff; evE; unfold CLOB; cbn [map nth]; rewrite Z.add_0_r; apply zcanon_id; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia end. }
assert (Hxc : x < c0).
{ destruct Hxw as [Hl | Hyt]; [exact Hl|]. destruct (Z_lt_le_dec x c0) as [Hl|Hge]; [exact Hl|]. exfalso. apply HnPD.
replace p with (top * Wd + c0) by (subst p; rewrite Hyt; f_equal; lia). exact HPDw. }
reshok_bx HS 6%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | evE; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK5 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia])
ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia]) V224e) as V224f.
cbn [ms_mem restrict mkst] in V224f.
clear Hc. hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_atom_off _ 18 y 1) in HGEU by (first [evE; exact E18 | lia]); rewrite (U_atom _ 26 (bot + 1)) in HGEU by (first [evE; exact E26 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 6%nat; pose proof (proj1 HJ2) as HAR6;
(hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1dfc;
[ repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | evE; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ])
| ]);
rename HFr into HFr6; rename HG into HG6; clear HF;
pose proof (wkept_trans B _ _ _ _ _ _ _ WK6 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR6 HFr6 HG6
ltac:(intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia])
ltac:(lia) ltac:(lia) ltac:(pose proof WK6 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK7;
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr6 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; [lia | evE_in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia]) V224f) as V224g;
cbn [ms_mem restrict mkst] in V224g;
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S3_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr; cbn [ms_regs restrict] in HKr;
prreg HS (6%bv : bv 5) R6; prreg HS (18%bv : bv 5) R18; prreg HS (24%bv : bv 5) R19; prreg HS (27%bv : bv 5) R27; prreg HS (19%bv : bv 5) R19t;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (x + (if y + 1 <? bot + 1 then 0 else 1)))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_add_not_ltu Ev 23 18 26 x y (bot + 1) 1 ltac:(evE; exact E23) ltac:(evE; exact E18) ltac:(evE; exact E26)
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))) R23 end;
pmkst HS.
+
eapply (IH (x + 1) top c0 top bot); [ clear - Hm Hc0 Hy Ht0 Hbt Hxc HGEU; nia | lia | exact Hc0 | exact Ht0 | lia | exact Hbt | right; reflexivity | exact HPDw
|   intros i' x' Hi' Hx0' Hd'; destruct (Z.eq_dec x' x) as [-> | Hnx];
[ destruct (Z.eq_dec i' y) as [-> | Hny]; [exact HnPD | apply XACC; [exact Hi' | exact Hx0' | right; split; [reflexivity | clear - Hd' Hny Hi' Hy HGEU; lia]]]
| apply XACC; [exact Hi' | exact Hx0' | left; clear - Hd' Hnx Hi'; lia] ]
| exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 S3_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite R6; evE; exact F6
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact R27
| rewrite R18; evE; exact E20
| rewrite R23; f_equal; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia
| rewrite R19t; evE; exact E20 | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E24r
| rewrite R19; evE; exact E19
| exact V224g ].
+
eapply (IH x (y + 1) c0 top bot); [ clear - Hm Hc0 Hy Ht0 Hbt Hxc HGEU; nia | lia | exact Hc0 | exact Ht0 | lia | exact Hbt | left; exact Hxc | exact HPDw
|   intros i' x' Hi' Hx0' Hd'; destruct (Z.eq_dec x' x) as [-> | Hnx];
[ destruct (Z.eq_dec i' y) as [-> | Hny]; [exact HnPD | apply XACC; [exact Hi' | exact Hx0' | right; split; [reflexivity | clear - Hd' Hny Hi' Hy HGEU; lia]]]
| apply XACC; [exact Hi' | exact Hx0' | left; clear - Hd' Hnx Hi'; lia] ]
| exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 S3_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite R6; evE; exact F6
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact R27
| rewrite R18; evE; rewrite E18, unsigned_lit_small by lia; reflexivity
| rewrite R23; f_equal; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia
| rewrite R19t; evE; exact E20 | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E24r
| rewrite R19; evE; exact E19
| exact V224g ].
Qed.
Lemma fl_s3lX : forall m, s3_stmtX m.
Proof. induction m as [|m IH]; [unfold s3_stmtX; intros; exfalso; nia | exact (fl_s3l_stepX m IH)]. Qed.
Definition s3s_regs := sr_set sr_atoms 27%bv (SLit 65535).
Definition s3s_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 184 232 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 19 0)); YP09.mkChunk 200 (CVal 8 (SOff 33 0));
YP09.mkChunk 224 (CVal 8 (SOff 34 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0))] ].
Definition s3s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (19%nat, mkAF 0 65534 0); (15%nat, mkAF 1 65535 0);
(21%nat, HPTR 4); (22%nat, HPTR 3); (33%nat, mkAF 1 65535 0); (34%nat, HPTR 0); (32%nat, HPTR 0) ] [] [].
Definition ss_s3s : sstate := mkSS 0x1dd8 s3s_regs s3s_mem None s3s_facts.
Lemma fl_s3X : forall (top bot c0 : Z) (regsF : bvmap 5 word) memF mdF,
0 <= top <= bot -> bot < Hd -> 0 <= c0 < Wd -> PDp (top * Wd + c0) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkept B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 6 = Z_to_bv 64 SB -> getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp -> getr regsF 27 = Z_to_bv 64 65535 ->
getr regsF 19 = Z_to_bv 64 top -> getr regsF 15 = Z_to_bv 64 (bot + 1) ->
val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 216) 8 bimg -> val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 184) 8 top ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x1dd8)) memF (seg_rom SEGS)) mdF) (s3_postX c0 top bot).
Proof.
intros top bot c0 regsF memF mdF Htb Hbt Hc0 HPDw HJF WK HKF E6 E21r E22r E27r E11r E14r V224 V192.
wctx_names. wprelude HJF. pose proof HJF as HJF0.
pose proof (proj1 (proj2 HJF)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_imgP _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HSpresF : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkept B lyc Sc W sp1 memc memF 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200F.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memF 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216F.
remember (Eimg (Ereg regsF [Z_to_bv 64 bimg; Z_to_bv 64 Wd; Z_to_bv 64 fimg])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 bimg; Z_to_bv 64 Wd; Z_to_bv 64 fimg]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 19%nat 19%bv eq_refl) as E11. rewrite E11r in E11. pose proof (EE 15%nat 15%bv eq_refl) as E14. rewrite E14r in E14.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 bimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 2)).
assert (HS : st_ok_pi SEGS VAL E ss_s3s (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 0x1dd8)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s3s, s3s_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1dd8) _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E27r; reflexivity].
- reflexivity.
- unfold s3s_mem. apply Forall_cons; [|apply Forall_nil]. unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 184 8 _ top); [cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V192]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200F]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216F]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ bimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V224]|]. apply Forall_nil.
- unfold s3s_mem. cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [s3s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E11, E14, E21, E22, E33, E34, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT3" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memF).
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x1dfc.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memF _ mdF sp1 HAR HFr1 HG1
ltac:(unfold ss_s3s, s3s_mem; cbn [ss_mem]; intros a (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia)
ltac:(lia) ltac:(lia) HSpresF)) as WK1.
pose proof (val_mem_run_out E _ W memF _ (sp1 + 216) 8 bimg HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia)
ltac:(unfold ss_s3s, s3s_mem; cbn [ss_mem]; intros kk Hk (r & Hr & Hw); cbn [In] in Hr; destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia) V224) as V224a.
cbn [ms_mem restrict mkst] in V224a.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (6%bv :: 19%bv :: 21%bv :: 22%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (18%bv : bv 5) R18. prreg HS (23%bv : bv 5) R23. prreg HS (25%bv : bv 5) R24. prreg HS (27%bv : bv 5) R27.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (G11 : ew Ev 19 = Z_to_bv 64 top) by (evE; exact E11); assert (G14 : ew Ev 15 = Z_to_bv 64 (bot + 1)) by (evE; exact E14);
assert (UH : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 48)) (SMd M_MUL (SOff 19 0) (SLit 5192296858534827628249021352509440))) (SLit 48)) = bot + 1 - top)
by (apply (U_lin_sub_zext16_c Ev 19 15 top (bot + 1) G11 G14); lia);
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (bot + 1 - top)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_lin_sub_c Ev 19 15 top (bot + 1) G11 G14 ltac:(lia) ltac:(lia)))) R19;
assert (U26 : U Ev (SAluw ALU_ADD (SOff 19 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 48)) (SMd M_MUL (SOff 19 0) (SLit 5192296858534827628249021352509440))) (SLit 48))) = bot + 1)
by (rewrite (U_addw_small Ev (SOff 19 0) _ top (bot + 1 - top) (U_atom Ev 19 top G11 ltac:(lia)) UH) by lia; lia);
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (bot + 1)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) U26)) R26 end.
pmkst HS.
eapply (fl_s3lX (Z.to_nat ((c0 + 1) * Hd)) 0 top c0 top bot);
[ rewrite Z2Nat.id by (clear - Hc0 RH; nia); clear - Hc0 Htb Hbt RH; nia | lia | lia | lia | lia | exact Hbt | right; reflexivity | exact HPDw |   intros i' x' Hi' Hx0' Hd'; exfalso; clear - Hi' Hx0' Hd'; lia | exact HJF | exact WK1
| intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]
| rewrite (HKr 6%bv ltac:(cbv; tauto)); exact E6
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact R27
| rewrite R18; evE; exact E11
| rewrite R23; reflexivity
| rewrite (HKr 19%bv ltac:(cbv; tauto)); exact E11r
| exact R26
| rewrite R24; evE; exact E33
| exact R19
| exact V224a ].
Qed.
End f.
End e.
End d.
End c.
