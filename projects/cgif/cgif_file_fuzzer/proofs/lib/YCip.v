(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI08 YI0m YI0n YI0s YCbw.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI5w.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0z YC4a YC8i YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCj2 YCjm YC8g YC8a YChd YCjr YCj1 YCj0 YCjc YCje YCjf YCjj YCjk YCjl YCjg.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Definition cplF (p : Z) : Z := 18446744073709551615 - p.
Lemma U_hgt_zext16 : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= a <= b -> b + 1 < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff nb 0) (SLit 48)) (SLit 281474976710656)) (SMd M_MUL (SOff na 0) (SLit 5192296858534827628249021352509440))) (SLit 48)) = b + 1 - a.
Proof.
intros E na nb a b Ha Hb Rab Rb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E na a Ha), (U_atom E nb b Hb), !U_SLit by lia. rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
change (zcanon 5192296858534827628249021352509440) with (2 ^ 64 - 2 ^ 48). change (zcanon 281474976710656) with (2 ^ 48).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (b * 2 ^ 48)) by (rewrite M64_val; change (2 ^ 48) with 281474976710656 in *; lia).
rewrite (zcanon_id (b * 2 ^ 48 + 2 ^ 48)) by (rewrite M64_val; change (2 ^ 48) with 281474976710656 in *; lia).
replace (zcanon (b * 2 ^ 48 + 2 ^ 48 + zcanon (a * (2 ^ 64 - 2 ^ 48)))) with ((b + 1 - a) * 2 ^ 48).
2: { unfold zcanon. rewrite M64_val. rewrite Zplus_mod_idemp_r. replace (b * 2 ^ 48 + 2 ^ 48 + a * (2 ^ 64 - 2 ^ 48)) with ((b + 1 - a) * 2 ^ 48 + a * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. change (2 ^ 48) with 281474976710656 in *. lia. }
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_lin_sub1 : forall E na nb a b, ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b -> 0 <= a <= b -> b + 1 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nb 1) (SMd M_MUL (SOff na 0) (SLit 18446744073709551615))) = b + 1 - a.
Proof.
intros E na nb a b Ha Hb Rab Rb. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom_off E nb b 1 Hb), (U_atom E na a Ha), U_SLit by lia. unfold zcanon. rewrite M64_val.
rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_r. replace (b + 1 + a * 18446744073709551615) with ((b + 1 - a) + a * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_add_lit0 : forall E a, U E (SAlu ALU_ADD a (SLit 0)) = U E a.
Proof. intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range. Qed.
Lemma U_dec_zext16 : forall E n x, ew E n = Z_to_bv 64 x -> 1 <= x < 2 ^ 16 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = x - 1.
Proof.
intros E n x Hn Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n x Hn), !U_SLit by lia. rewrite (zcanon_id 48) by (rewrite M64_val; lia). change (Z.land 48 63) with 48.
change (zcanon (-281474976710656)) with (2 ^ 64 - 2 ^ 48).
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (zcanon_id (x * 2 ^ 48)) by (rewrite M64_val; change (2 ^ 48) with 281474976710656 in *; lia).
replace (zcanon (x * 2 ^ 48 + (2 ^ 64 - 2 ^ 48))) with ((x - 1) * 2 ^ 48).
2: { unfold zcanon. rewrite M64_val. replace (x * 2 ^ 48 + (2 ^ 64 - 2 ^ 48)) with ((x - 1) * 2 ^ 48 + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. change (2 ^ 48) with 281474976710656 in *. lia. }
rewrite Z.div_mul by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg lib_both3_0_listing}.
Context {RO : YC8g.ro_below_ofl (@pa_segs _ lib_both3_0_listing PI) (@pa_relro_lo _ lib_both3_0_listing PI) (@pa_relro_hi _ lib_both3_0_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Ltac eimg_low := rewrite ?Eimg_low by (unfold A_TEXT; lia).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA AS_memcmp_2).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL. Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_both3_0) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_both3_0 PI.
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
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let BDp := BD W memc fimg bimg.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp & Vg & Vcfp);
pose proof HGEO as (RW & RH & HN & V176 & V136 & V168).
Ltac wprelude HJ :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (HFB : FBAND = 8192) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition F4_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 12; 13; 14; 16; 22; 23; 25; 26; 27; 29]%bv.
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
Ltac efact HS n En G :=
lazymatch type of HS with st_ok_pi _ _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end | st_ok _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end  end.
Ltac rget R En :=
rewrite R; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En.
Ltac pix_obls HARx E29 E32 E33 Hfi Hbi p :=
try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 32 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 32 (fimg + p) cc ltac:(evE; exact E32)) by lia | rewrite (U_atom Ex 32 (fimg + p) ltac:(evE; exact E32)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len fimg Nb HARx Hfi); [rewrite (U_atom Ex 29 SB ltac:(evE; exact E29)); [reflexivity | unfold SB; lia] | lia | lia] end);
try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (bimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (bimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 29 0) _ len bimg Nb HARx Hbi); [rewrite (U_atom Ex 29 SB ltac:(evE; exact E29)); [reflexivity | unfold SB; lia] | lia | lia] end);
match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
Definition f4_regs := sr_set sr_atoms 17%bv (SLit 65535).
Definition f4_scr : YP09.region := YP09.mkRegion (Some 9%nat) 152 160 152 160 [].
Definition f4_loc : YP09.region := YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 36 0))].
Definition f4_cur : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))].
Definition f4_bef : YP09.region := YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition f4_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (29%nat, mkAF SB SB 0); (32%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0);
(36%nat, HPTR 0); (25%nat, HPTR 0); (11%nat, mkAF 0 4294967295 0); (12%nat, mkAF 0 4294967295 0); (6%nat, mkAF 0 4294967295 0);
(13%nat, mkAF 18446603336221196288 18446744073709551615 0); (16%nat, mkAF 18446603336221196288 18446744073709551615 0);
(14%nat, mkAF 1 65535 0); (5%nat, mkAF 0 65534 0); (15%nat, mkAF 0 65534 0); (22%nat, mkAF 0 65534 0);
(26%nat, mkAF 0 65534 0); (27%nat, mkAF 1 65535 0) ] []
[ (SAlu ALU_ADD (SOff 11 0) (SOff 36 0), SOff 32 0); (SAlu ALU_ADD (SOff 11 0) (SOff 25 0), SOff 33 0) ].
Definition ss_f4 : sstate := mkSS 0x2514 f4_regs [f4_scr; f4_loc; f4_cur; f4_bef] None f4_facts.
Definition f4_postX (top bot left : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' w,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x25bc)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
1 <= w /\ left + w <= Wd /\ getr regs' 21 = Z_to_bv 64 w /\ getr regs' 22 = Z_to_bv 64 left /\ getr regs' 23 = Z_to_bv 64 (bot + 1 - top) /\
getr regs' 27 = Z_to_bv 64 Wd /\ val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 152) 8 top /\
(exists y', top <= y' <= bot /\ BDp (y' * Wd + (left + w - 1))) /\ (forall i x0, top <= i <= bot -> left + w - 1 < x0 < Wd -> ~ BDp (i * Wd + x0)).
Definition f4_stmtX (m : nat) : Prop :=
forall (x y c0 top bot left : Z) (regsE : bvmap 5 word) memE mdE,
(x - c0) * Hd + (bot + 1 - y) <= Z.of_nat m -> c0 <= x < Wd -> 0 <= left <= c0 -> 0 <= top -> top <= y <= bot -> bot < Hd -> (c0 < x \/ y = top) -> BDp (top * Wd + c0) ->
(forall i x0, top <= i <= bot -> x0 < Wd -> (x < x0 \/ (x0 = x /\ i < y)) -> ~ BDp (i * Wd + x0)) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 29 = Z_to_bv 64 SB -> getr regsE 11 = Z_to_bv 64 (y * Wd + x) -> getr regsE 12 = Z_to_bv 64 (top * Wd) -> getr regsE 13 = Z_to_bv 64 (cplF fimg) ->
getr regsE 14 = Z_to_bv 64 (bot + 1) -> getr regsE 15 = Z_to_bv 64 x -> getr regsE 16 = Z_to_bv 64 (cplF bimg) -> getr regsE 17 = Z_to_bv 64 65535 ->
getr regsE 5 = Z_to_bv 64 y -> getr regsE 6 = Z_to_bv 64 (y * Wd) -> getr regsE 22 = Z_to_bv 64 left -> getr regsE 23 = Z_to_bv 64 (bot + 1 - top) ->
getr regsE 25 = Z_to_bv 64 bimg -> getr regsE 26 = Z_to_bv 64 top -> getr regsE 27 = Z_to_bv 64 Wd ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x2514)) memE (seg_rom SEGS)) mdE) (f4_postX top bot left).
Lemma fl_f4l_stepX : forall m, f4_stmtX m -> f4_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold f4_stmtX.
intros x y c0 top bot left regsE memE mdE Hm Hx Hl Ht0 Hy Hbt Hxw HBDw XACC HJE WK HKE E29r E11r E12r E13r E14r E15r E16r E17r E5r E6r E22r E23r E25r E26r E27r.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_imgP _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HyW : 0 <= y * Wd /\ y * Wd + Wd <= Nb) by (rewrite HN; clear - Hy Hbt Ht0 RW RH; nia).
assert (HtW : 0 <= top * Wd /\ top * Wd + Wd <= Nb) by (rewrite HN; clear - Hy Hbt Ht0 RW RH; nia).
assert (Hp : 0 <= y * Wd + x /\ y * Wd + x < Nb) by (clear - HyW Hx Hl; lia).
set (p := y * Wd + x) in *.
destruct (wimg_byteF B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as (VbC & RbC & AbC & SbC).
destruct (wimg_byteF B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as (VbB & RbB & AbB & SbB).
set (bC := bval (aview SEGS (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Eimg (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 (bimg + p); Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 fimg])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 (bimg + p); Z_to_bv 64 bC; Z_to_bv 64 bB; Z_to_bv 64 fimg]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr regsE r0) by (intros n r0 Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 29%nat 29%bv eq_refl) as E29. rewrite E29r in E29. pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite E11r in E11.
pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12. pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite E13r in E13.
pose proof (EE 14%nat 14%bv eq_refl) as E14. rewrite E14r in E14. pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15.
pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite E16r in E16.
pose proof (EE 5%nat 5%bv eq_refl) as E5. rewrite E5r in E5. pose proof (EE 6%nat 6%bv eq_refl) as E6. rewrite E6r in E6.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
assert (E32 : ew E 32 = Z_to_bv 64 (fimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (bimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 bB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (HS : st_ok_pi SEGS VAL E ss_f4 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x2514)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f4, f4_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x2514) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E17r; cbn [sv_denot]; reflexivity].
- reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]; unfold region_ok, f4_scr, f4_loc, f4_cur, f4_bef;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HSpresE; lia|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|]. apply Forall_nil.
+ rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, f4_scr, f4_loc, f4_cur, f4_bef. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E9, E32, E33, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
+ cbn [f4_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E29, E32, E33, E34, E35, E36, E25, E11, E12, E6, E13, E16, E14, E5, E15, E22, E26, E27, !unsigned_lit_small by (unfold SB, cplF; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB, cplF. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end].
+ cbn [f4_facts f_alias alias_ok].
split; [rewrite (denot_add_atoms E 11 36 p fimg E11 E36) by lia; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; lia|].
split; [rewrite (denot_add_atoms E 11 25 p bimg E11 E25) by lia; cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; f_equal; lia | exact I]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
all: pix_obls HAR E29 E32 E33 Hfi Hbi p.
1: { unfold ss_f4, f4_scr, f4_loc, f4_cur, f4_bef; cbn [ss_mem]. awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (HBD : BDp p).
{ rewrite branch_ne_U in Hc. rewrite (U_atom _ 34 bC) in Hc by (first [evE; exact E34 | lia]). rewrite (U_atom _ 35 bB) in Hc by (first [evE; exact E35 | lia]).
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc. intros HD. apply Hc. rewrite SbC, SbB in HD. fold bC bB in HD. injection HD as HD. exact HD. }
clear Hc. reshok_bx HS 29%nat. pose proof (proj1 HJE) as HAR3.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x25bc.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR3 WK1 WK3 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
efact HS 15%nat E15 K15. efact HS 22%nat E22 K22. efact HS 26%nat E26 K26. efact HS 9%nat E9 K9.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SOff 26 0) top HR1
ltac:(rewrite K9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite K26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152 end; clear HR1 | st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 0 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SOff 26 0) top HR1
ltac:(rewrite K9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite K26, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152 end; clear HR1  end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V152.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (UW : U Ev (SAlu ALU_ADD (SOff 15 1) (SMd M_MUL (SOff 22 0) (SLit 18446744073709551615))) = x + 1 - left) by (apply (U_lin_sub1 Ev 22 15 left x K22 K15); lia);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (x + 1 - left)) (denot_of_U2 Ev _ _ UW) Rg21 | st_ok _ ?Ev _ _ =>
assert (UW : U Ev (SAlu ALU_ADD (SOff 15 1) (SMd M_MUL (SOff 22 0) (SLit 18446744073709551615))) = x + 1 - left) by (apply (U_lin_sub1 Ev 22 15 left x K22 K15); lia);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (x + 1 - left)) (denot_of_U2 Ev _ _ UW) Rg21  end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (x + 1 - left) end.
split; [reflexivity|]. split; [exact HJE|]. split; [exact WK3|].
split; [intros r0 Hr0; transitivity (getr regsE r0); [apply HKr; cbv [WKEPT5 F4_KEPT In] in Hr0 |- *; tauto | apply HKE; exact Hr0]|].
split; [lia|]. split; [lia|]. split; [exact Rg21|].
split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [exact V152|].
replace (left + (x + 1 - left) - 1) with x by (clear; lia).
split; [exists y; split; [exact Hy | exact HBD] | intros i' x0 Hi' Hx0; apply XACC; [exact Hi' | clear - Hx0; lia | left; clear - Hx0; lia]].
-
assert (HnBD : ~ BDp p).
{ rewrite branch_ne_U in Hc. rewrite (U_atom _ 34 bC) in Hc by (first [evE; exact E34 | lia]). rewrite (U_atom _ 35 bB) in Hc by (first [evE; exact E35 | lia]).
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc. intros HD. apply HD. rewrite SbC, SbB. fold bC bB. rewrite Hc. reflexivity. }
assert (Hxc : c0 < x).
{ destruct Hxw as [Hlt | ->]; [exact Hlt|]. destruct (Z_lt_le_dec c0 x) as [Hlt | Hge]; [exact Hlt|]. exfalso. assert (x = c0) by lia. subst x. apply HnBD. unfold p. exact HBDw. }
clear Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJE) as HAR3.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR3 WK1 WK3 E9. clear HF HFr HG.
efact HS 5%nat E5 B5. efact HS 14%nat E14 B14.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
+
rewrite branch_geu_U in Hc. rewrite (U_and16 _ _ (y + 1) (U_atom_off _ 5 y 1 B5 ltac:(lia) ltac:(lia))), (U_atom _ 14 (bot + 1) B14) in Hc by lia.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJE) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR4 WK3 WK4 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: {
exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ =>
rewrite branch_ltu_U in Hb;
rewrite (U_atom _ 13 (cplF fimg)) in Hb by (first [evE; exact E13 | unfold cplF; lia]);
apply Z.ltb_lt in Hb;
lazymatch type of Hb with _ < U ?Ex (SAlu ALU_SRL (SAlu ALU_SLL ?a _) _) => pose proof (U_zext32_lt Ex a) as Hz32 end; unfold cplF in Hb; lia end. }
reshok_bx HS 29%nat. pose proof (proj1 HJE) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2514.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK4 WK5 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
efact HS 5%nat E5 K5. efact HS 15%nat E15 K15. efact HS 14%nat E14 K14. efact HS 12%nat E12 K12.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (UY : U Ev (SAlu ALU_AND (SOff 5 1) (SLit 65535)) = y + 1) by (apply U_and16; [apply (U_atom_off Ev 5 y 1 K5); lia | lia]);
assert (UL : U Ev (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) = 0) by (apply U_sltu_ge; rewrite UY, (U_atom Ev 14 (bot + 1) K14) by lia; lia);
assert (UF : U Ev (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1)) = 1) by (rewrite (U_xor1_bit Ev _ 0 UL) by lia; reflexivity);
assert (UX : U Ev (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) = x - 1)
by (apply U_sub_small2; [apply (U_atom Ev 15 x K15); lia | exact UF | lia | lia]);
assert (UZ : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32)) = top * Wd + (x - 1))
by (apply U_zext_sh; [apply U_add_small2; [apply (U_atom Ev 12 (top * Wd) K12); lia | apply U_and16; [exact UX | lia] | lia | lia | lia] | lia | lia]);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (top * Wd + (x - 1))) (denot_of_U2 Ev _ _ UZ) Rg11;
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (x - 1)) (denot_of_U2 Ev _ _ UX) Rg15 | st_ok _ ?Ev _ _ =>
assert (UY : U Ev (SAlu ALU_AND (SOff 5 1) (SLit 65535)) = y + 1) by (apply U_and16; [apply (U_atom_off Ev 5 y 1 K5); lia | lia]);
assert (UL : U Ev (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) = 0) by (apply U_sltu_ge; rewrite UY, (U_atom Ev 14 (bot + 1) K14) by lia; lia);
assert (UF : U Ev (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1)) = 1) by (rewrite (U_xor1_bit Ev _ 0 UL) by lia; reflexivity);
assert (UX : U Ev (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) = x - 1)
by (apply U_sub_small2; [apply (U_atom Ev 15 x K15); lia | exact UF | lia | lia]);
assert (UZ : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32)) = top * Wd + (x - 1))
by (apply U_zext_sh; [apply U_add_small2; [apply (U_atom Ev 12 (top * Wd) K12); lia | apply U_and16; [exact UX | lia] | lia | lia | lia] | lia | lia]);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (top * Wd + (x - 1))) (denot_of_U2 Ev _ _ UZ) Rg11;
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (x - 1)) (denot_of_U2 Ev _ _ UX) Rg15  end.
prreg HS (5%bv : bv 5) Rg5. prreg HS (6%bv : bv 5) Rg6. prreg HS (17%bv : bv 5) Rg17.
pmkst HS.
eapply (IH (x - 1) top c0 top bot left); [ clear - Hm Hc Hy Hbt Ht0; nia | lia | lia | lia | lia | lia | right; reflexivity | exact HBDw
|   intros i' x0 Hi' HxW' Hd'; destruct (Z.eq_dec x0 x) as [-> | Hnx];
[ destruct (Z.eq_dec i' y) as [-> | Hny]; [exact HnBD | apply XACC; [exact Hi' | exact HxW' | right; split; [reflexivity | clear - Hd' Hny Hi' Hy Hc; lia]]]
| apply XACC; [exact Hi' | exact HxW' | left; clear - Hd' Hnx Hi'; lia] ]
| exact HJE | exact WK5
| intros r0 Hr0; transitivity (getr regsE r0); [apply HKr; cbv [WKEPT5 F4_KEPT In] in Hr0 |- *; tauto | apply HKE; exact Hr0]
| rewrite (HKr 29%bv ltac:(cbv; tauto)); exact E29r
| rewrite Rg11; f_equal; lia
| rewrite (HKr 12%bv ltac:(cbv; tauto)); exact E12r | rewrite (HKr 13%bv ltac:(cbv; tauto)); exact E13r | rewrite (HKr 14%bv ltac:(cbv; tauto)); exact E14r
| exact Rg15 | rewrite (HKr 16%bv ltac:(cbv; tauto)); exact E16r | exact Rg17 | rget Rg5 E26 | rget Rg6 E12
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r ].
+
rewrite branch_geu_U in Hc. rewrite (U_and16 _ _ (y + 1) (U_atom_off _ 5 y 1 B5 ltac:(lia) ltac:(lia))), (U_atom _ 14 (bot + 1) B14) in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
reshok_bx HS 29%nat. pose proof (proj1 HJE) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR4 WK3 WK4 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: { exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ =>
rewrite branch_ltu_U in Hb;
rewrite (U_atom _ 13 (cplF fimg)) in Hb by (first [evE; exact E13 | unfold cplF; lia]);
apply Z.ltb_lt in Hb;
lazymatch type of Hb with _ < U ?Ex (SAlu ALU_SRL (SAlu ALU_SLL ?a _) _) => pose proof (U_zext32_lt Ex a) as Hz32 end; unfold cplF in Hb; lia end. }
reshok_bx HS 29%nat. pose proof (proj1 HJE) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2514.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR5 WK4 WK5 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
assert (HyW2 : 0 <= (y + 1) * Wd /\ (y + 1) * Wd + Wd <= Nb) by (rewrite HN; clear - Hy Hbt Ht0 RW RH Hc; nia).
efact HS 5%nat E5 K5. efact HS 15%nat E15 K15. efact HS 14%nat E14 K14. efact HS 6%nat E6 K6. efact HS 27%nat E27 K27.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (UY : U Ev (SAlu ALU_AND (SOff 5 1) (SLit 65535)) = y + 1) by (apply U_and16; [apply (U_atom_off Ev 5 y 1 K5); lia | lia]);
assert (UL : U Ev (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) = 1) by (apply U_sltu_lt; rewrite UY, (U_atom Ev 14 (bot + 1) K14) by lia; lia);
assert (UF : U Ev (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1)) = 0) by (rewrite (U_xor1_bit Ev _ 1 UL) by lia; reflexivity);
assert (UX : U Ev (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) = x - 0)
by (apply U_sub_small2; [apply (U_atom Ev 15 x K15); lia | exact UF | lia | lia]);
assert (UR : U Ev (SAlu ALU_ADD (SOff 6 0) (SOff 27 0)) = y * Wd + Wd)
by (apply U_add_small2; [apply (U_atom Ev 6 (y * Wd) K6); lia | apply (U_atom Ev 27 Wd K27); lia | lia | lia | lia]);
assert (UZ : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SOff 6 0) (SOff 27 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32)) = y * Wd + Wd + (x - 0))
by (apply U_zext_sh; [apply U_add_small2; [exact UR | apply U_and16; [exact UX | lia] | lia | lia | lia] | lia | lia]);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (y * Wd + Wd + (x - 0))) (denot_of_U2 Ev _ _ UZ) Rg11;
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (x - 0)) (denot_of_U2 Ev _ _ UX) Rg15;
rreg_by HS (6%bv : bv 5) (Z_to_bv 64 (y * Wd + Wd)) (denot_of_U2 Ev _ _ UR) Rg6;
rreg_by HS (5%bv : bv 5) (Z_to_bv 64 (y + 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 5 y 1 K5 ltac:(lia) ltac:(lia))) Rg5 | st_ok _ ?Ev _ _ =>
assert (UY : U Ev (SAlu ALU_AND (SOff 5 1) (SLit 65535)) = y + 1) by (apply U_and16; [apply (U_atom_off Ev 5 y 1 K5); lia | lia]);
assert (UL : U Ev (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) = 1) by (apply U_sltu_lt; rewrite UY, (U_atom Ev 14 (bot + 1) K14) by lia; lia);
assert (UF : U Ev (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1)) = 0) by (rewrite (U_xor1_bit Ev _ 1 UL) by lia; reflexivity);
assert (UX : U Ev (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) = x - 0)
by (apply U_sub_small2; [apply (U_atom Ev 15 x K15); lia | exact UF | lia | lia]);
assert (UR : U Ev (SAlu ALU_ADD (SOff 6 0) (SOff 27 0)) = y * Wd + Wd)
by (apply U_add_small2; [apply (U_atom Ev 6 (y * Wd) K6); lia | apply (U_atom Ev 27 Wd K27); lia | lia | lia | lia]);
assert (UZ : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SOff 6 0) (SOff 27 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 15 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 5 1) (SLit 65535)) (SOff 14 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32)) = y * Wd + Wd + (x - 0))
by (apply U_zext_sh; [apply U_add_small2; [exact UR | apply U_and16; [exact UX | lia] | lia | lia | lia] | lia | lia]);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (y * Wd + Wd + (x - 0))) (denot_of_U2 Ev _ _ UZ) Rg11;
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (x - 0)) (denot_of_U2 Ev _ _ UX) Rg15;
rreg_by HS (6%bv : bv 5) (Z_to_bv 64 (y * Wd + Wd)) (denot_of_U2 Ev _ _ UR) Rg6;
rreg_by HS (5%bv : bv 5) (Z_to_bv 64 (y + 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 5 y 1 K5 ltac:(lia) ltac:(lia))) Rg5  end.
prreg HS (17%bv : bv 5) Rg17.
pmkst HS.
eapply (IH x (y + 1) c0 top bot left); [ clear - Hm Hc Hy Hbt Ht0; nia | lia | lia | lia | lia | lia | left; exact Hxc | exact HBDw
|   intros i' x0 Hi' HxW' Hd'; destruct (Z.eq_dec x0 x) as [-> | Hnx];
[ destruct (Z.eq_dec i' y) as [-> | Hny]; [exact HnBD | apply XACC; [exact Hi' | exact HxW' | right; split; [reflexivity | clear - Hd' Hny Hi' Hy Hc; lia]]]
| apply XACC; [exact Hi' | exact HxW' | left; clear - Hd' Hnx Hi'; lia] ]
| exact HJE | exact WK5
| intros r0 Hr0; transitivity (getr regsE r0); [apply HKr; cbv [WKEPT5 F4_KEPT In] in Hr0 |- *; tauto | apply HKE; exact Hr0]
| rewrite (HKr 29%bv ltac:(cbv; tauto)); exact E29r
| rewrite Rg11; f_equal; lia
| rewrite (HKr 12%bv ltac:(cbv; tauto)); exact E12r | rewrite (HKr 13%bv ltac:(cbv; tauto)); exact E13r | rewrite (HKr 14%bv ltac:(cbv; tauto)); exact E14r
| rewrite Rg15; f_equal; lia | rewrite (HKr 16%bv ltac:(cbv; tauto)); exact E16r | exact Rg17 | exact Rg5 | rewrite Rg6; f_equal; lia
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r ].
Qed.
Lemma fl_f4lX : forall m, f4_stmtX m.
Proof.
induction m as [|m IH]; [|exact (fl_f4l_stepX m IH)].
unfold f4_stmtX. intros x y c0 top bot left regsE memE mdE Hm Hx Hl Ht0 Hy Hbt Hxw. exfalso.
pose proof HGEO as (RW & RH & _). assert (0 <= (x - c0) * Hd) by nia. lia.
Qed.
Definition f4s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (29%nat, mkAF SB SB 0); (25%nat, HPTR 0);
(12%nat, mkAF 0 4294967295 0); (13%nat, mkAF 18446603336221196288 18446744073709551615 0); (26%nat, mkAF 0 65534 0); (27%nat, mkAF 1 65535 0) ] [] [].
Definition ss_f4s : sstate := mkSS 0x24e4 sr_atoms [] None f4s_facts.
Lemma fl_f4X : forall (c0 top bot left : Z) (regsF : bvmap 5 word) memF mdF,
0 <= left <= c0 -> c0 < Wd -> 0 <= top -> top <= bot < Hd -> BDp (top * Wd + c0) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 22 = Z_to_bv 64 left -> getr regsF 12 = Z_to_bv 64 (top * Wd) -> getr regsF 13 = Z_to_bv 64 (cplF fimg) -> getr regsF 14 = Z_to_bv 64 (bot + 1) ->
getr regsF 23 = Z_to_bv 64 (bot + 1 - top) -> getr regsF 25 = Z_to_bv 64 bimg -> getr regsF 26 = Z_to_bv 64 top -> getr regsF 27 = Z_to_bv 64 Wd ->
getr regsF 29 = Z_to_bv 64 SB ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x24e4)) memF (seg_rom SEGS)) mdF) (f4_postX top bot left).
Proof.
intros c0 top bot left regsF memF mdF Hl Hcw0 Ht0 Hbt HBDw HJF WK HKF E22r E12r E13r E14r E23r E25r E26r E27r E29r.
wctx_names. wprelude HJF. pose proof HJF as HJF0.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_imgP _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HtW : 0 <= top * Wd /\ top * Wd + Wd <= Nb) by (rewrite HN; clear - Hbt Ht0 RW RH; nia).
remember (Eimg (Ereg regsF [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsF []) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r0 : bv 5), Z.of_nat n = bv_unsigned r0 -> ew E n = getr regsF r0) by (intros n r0 Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22. pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite E13r in E13. pose proof (EE 14%nat 14%bv eq_refl) as E14. rewrite E14r in E14.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
pose proof (EE 29%nat 29%bv eq_refl) as E29. rewrite E29r in E29.
assert (HS : st_ok_pi SEGS VAL E ss_f4s (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 0x24e4)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f4s. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x24e4) _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [f4s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E29, E25, E12, E13, E26, E27, !unsigned_lit_small by (unfold SB, cplF; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB, cplF. repeat match goal with |- _ /\ _ => split end;
first [lia | match goal with |- ?g => idtac "FACT-LEFT4" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memF).
hei_havoc HS; paj_run_tok RUN HS HJF SHOK FLBspan.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR WK WK1 E9. clear HF HFr HG.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
1: { exfalso. match goal with Hb : branch_taken BC_LTU _ _ = true |- _ =>
rewrite branch_ltu_U in Hb;
rewrite (U_atom _ 13 (cplF fimg)) in Hb by (first [evE; exact E13 | unfold cplF; lia]);
apply Z.ltb_lt in Hb;
lazymatch type of Hb with _ < U ?Ex (SAlu ALU_SRL (SAlu ALU_SLL ?a _) _) => pose proof (U_zext32_lt Ex a) as Hz32 end; unfold cplF in Hb; lia end. }
clear Hc. reshok_bx HS 29%nat. pose proof (proj1 HJF) as HAR2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x2514.
1: { awrW E9 FFS. }
run_wkeptF HFr HG HAR2 WK1 WK2 E9. clear HF HFr HG.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (12%bv :: 13%bv :: 14%bv :: 22%bv :: 23%bv :: 25%bv :: 26%bv :: 27%bv :: 29%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
efact HS 12%nat E12 K12. efact HS 25%nat E25 K25. efact HS 27%nat E27 K27.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (UD : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 27 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Wd - 1) by (apply (U_dec_zext16 Ev 27 Wd K27); lia);
assert (UZ : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 27 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) (SLit 32)) (SLit 32)) = top * Wd + (Wd - 1))
by (apply U_zext_sh; [apply U_add_small2; [apply (U_atom Ev 12 (top * Wd) K12); lia | exact UD | lia | lia | lia] | lia | lia]);
assert (UN : U Ev (SAlu ALU_XOR (SOff 25 0) (SLit (-1))) = cplF bimg) by (rewrite (U_not_gen Ev _ bimg (U_atom Ev 25 bimg K25 ltac:(lia))) by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (top * Wd + (Wd - 1))) (denot_of_U2 Ev _ _ UZ) Rg11;
rreg_by HS (16%bv : bv 5) (Z_to_bv 64 (cplF bimg)) (denot_of_U2 Ev _ _ UN) Rg16;
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (Wd - 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 27 Wd (-1) K27 ltac:(lia) ltac:(lia))) Rg15 | st_ok _ ?Ev _ _ =>
assert (UD : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 27 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Wd - 1) by (apply (U_dec_zext16 Ev 27 Wd K27); lia);
assert (UZ : U Ev (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 27 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) (SLit 32)) (SLit 32)) = top * Wd + (Wd - 1))
by (apply U_zext_sh; [apply U_add_small2; [apply (U_atom Ev 12 (top * Wd) K12); lia | exact UD | lia | lia | lia] | lia | lia]);
assert (UN : U Ev (SAlu ALU_XOR (SOff 25 0) (SLit (-1))) = cplF bimg) by (rewrite (U_not_gen Ev _ bimg (U_atom Ev 25 bimg K25 ltac:(lia))) by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (top * Wd + (Wd - 1))) (denot_of_U2 Ev _ _ UZ) Rg11;
rreg_by HS (16%bv : bv 5) (Z_to_bv 64 (cplF bimg)) (denot_of_U2 Ev _ _ UN) Rg16;
rreg_by HS (15%bv : bv 5) (Z_to_bv 64 (Wd - 1)) (denot_of_U2 Ev _ _ (U_atom_off Ev 27 Wd (-1) K27 ltac:(lia) ltac:(lia))) Rg15  end.
prreg HS (17%bv : bv 5) Rg17. prreg HS (5%bv : bv 5) Rg5. prreg HS (6%bv : bv 5) Rg6.
pmkst HS.
eapply (fl_f4lX (Z.to_nat ((Wd - 1 - c0) * Hd + (bot + 1 - top))) (Wd - 1) top c0 top bot left); [ clear - Hcw0 RH Hbt Ht0; nia | lia | lia | lia | lia | lia | right; reflexivity | exact HBDw |   intros i' x0 Hi' HxW' Hd'; exfalso; clear - Hi' HxW' Hd'; lia | exact HJF | exact WK2
| intros r0 Hr0; transitivity (getr regsF r0); [apply HKr; cbv [WKEPT5 In] in Hr0 |- *; tauto | apply HKF; exact Hr0]
| rewrite (HKr 29%bv ltac:(cbv; tauto)); exact E29r
| exact Rg11
| rewrite (HKr 12%bv ltac:(cbv; tauto)); exact E12r | rewrite (HKr 13%bv ltac:(cbv; tauto)); exact E13r | rewrite (HKr 14%bv ltac:(cbv; tauto)); exact E14r
| exact Rg15 | exact Rg16 | exact Rg17 | rget Rg5 E26 | rget Rg6 E12
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r ].
Qed.
End f.
End e.
End d.
End c.
