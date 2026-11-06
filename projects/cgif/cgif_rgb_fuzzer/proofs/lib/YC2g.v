(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YC02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YC2v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YC19 YF8z YC1d YC1a YC2o YC0x YC17 YC1b YC2u YC1z YC1y YC29 YC2b YC2c YC2l YC2m YC2n YC2f.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_width2 : forall E A nl xx l, U E A = xx -> ew E nl = Z_to_bv 64 l -> 0 <= l <= xx -> xx + 1 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_SUB A (SOff nl 0)) (SLit 1)) = xx - l + 1.
Proof.
intros E A nl xx l HA Hl Rl Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite HA, (U_atom E nl l Hl), U_SLit by lia. change (zcanon 1) with 1.
rewrite (zcanon_id (xx - l)) by (rewrite M64_val; lia). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_width0 : forall E nx nl x l, ew E nx = Z_to_bv 64 x -> ew E nl = Z_to_bv 64 l -> 0 <= l <= x -> x < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nx 0) (SMd M_MUL (SOff nl 0) (SLit 18446744073709551615))) = x - l.
Proof.
intros E nx nl x l Hx Hl Rlx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E nx x Hx), (U_atom E nl l Hl), U_SLit by lia. change (zcanon 18446744073709551615) with (2 ^ 64 - 1).
unfold zcanon. rewrite M64_val. rewrite Zplus_mod_idemp_r. replace (x + l * (2 ^ 64 - 1)) with ((x - l) + l * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Section c.
Variable B : asyms.
Hypothesis TL : TraLib B.
Hypothesis LAWS : AR_laws trasegs B.
Hypothesis ABCMP : abcmp_realizes trasegs B A_bcmp_icpt.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section d.
Variables (W : world trasegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trasegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd a176 a184 : Z) (sv2 sv4 : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HRES : 0 <= a176 < 2 ^ 64 /\ 0 <= a184 < 2 ^ 64 /\
val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 144) 8 a176 /\ val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 176) 8 a184.
Hypothesis HFIMG : val_mem trasegs (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
Let BDp := BD W memc fimg bimg.
Let CALL := bcmp_callW B LAWS ABCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp);
pose proof HGEO as (RW & RH & HN & V200 & V112); pose proof HRES as (R176 & R184 & V176 & V184).
Ltac wprelude HJ :=
pose proof Hwx_tfa as Hwx; pose proof tra_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (HFB : FBAND = 8192) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Ltac noW := cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia|]); destruct Hr.
Ltac awrRO := repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]); try (match goal with |- ?g => idtac "AWR-LEFT" g end).
Definition F4_CLOB : list (bv 5) := [5; 6; 10; 11; 13; 14; 15; 16; 17]%bv.
Definition F4_KEPT : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Definition F4_KEPTX : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Ltac slot160 HS idx E9 E28 hv V :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth idx (ss_mem ssx) (YQ0b.mkRegion None 0 0 0 0 [])) in
let HR1 := fresh "HR1" in
pose proof (st_ok_region_nth Ex ssx msx idx r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SOff 40 0) hv HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; evE; rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V end; clear HR1 end;
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V.
Definition f4_regs := sr_set sr_atoms 14%bv (SLit 65535).
Definition f4_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 176 184 176 176 [YQ0b.mkChunk 176 (CVal 8 (SOff 38 0))];
YQ0b.mkRegion (Some 9%nat) 224 232 224 224 [YQ0b.mkChunk 224 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 33%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 34 0))];
YQ0b.mkRegion (Some 35%nat) 0 1 0 0 [YQ0b.mkChunk 0 (CVal 1 (SOff 36 0))];
YQ0b.mkRegion (Some 9%nat) 144 152 144 144 [YQ0b.mkChunk 144 (CVal 8 (SOff 37 0))];
YQ0b.mkRegion (Some 9%nat) 200 208 200 200 [YQ0b.mkChunk 200 (CVal 8 (SOff 39 0))];
YQ0b.mkRegion (Some 9%nat) 160 168 160 160 [YQ0b.mkChunk 160 (CVal 8 (SOff 40 0))] ].
Definition f4_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (15%nat, mkAF 0 65534 0); (13%nat, mkAF 1 65534 0); (23%nat, mkAF 0 65534 0);
(26%nat, mkAF 1 65535 0); (39%nat, mkAF 1 65535 0); (27%nat, mkAF 0 65534 0); (12%nat, mkAF 0 4294967295 0); (10%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0);
(32%nat, HPTR 0); (25%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, HPTR 0); (36%nat, mkAF 0 255 0);
(37%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_f4 : sstate := mkSS 0x87d90 f4_regs f4_mem None f4_facts.
Definition f4_post (c0 top bot left : Z) : world trasegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' right,
c' = mkCfg (mkst regs' (Z_to_bv 64 0x8755c) mem' (seg_rom trasegs)) md' /\
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
c0 <= right < Wd /\
getr regs' 26 = Z_to_bv 64 (right - left + 1) /\ val_mem trasegs (mrestrict (w_H W) mem') (sp1 + 160) 8 (bot + 1 - top) /\ getr regs' 27 = Z_to_bv 64 top /\ getr regs' 23 = Z_to_bv 64 left /\
getr regs' 10 = Z_to_bv 64 a184 /\ getr regs' 11 = Z_to_bv 64 a176 /\ getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4.
Definition f4_stmt (m : nat) : Prop :=
forall (x y c0 top bot left : Z) (regsE : bvmap 5 word) memE mdE,
(x - c0) * Hd + (bot - y) < Z.of_nat m -> c0 < x < Wd -> 0 <= left <= c0 -> 0 <= top -> top <= y <= bot -> bot < Hd -> BDp (top * Wd + c0) ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp -> getr regsE 14 = Z_to_bv 64 65535 ->
getr regsE 15 = Z_to_bv 64 y -> getr regsE 10 = Z_to_bv 64 (y * Wd) -> getr regsE 13 = Z_to_bv 64 x -> getr regsE 12 = Z_to_bv 64 (top * Wd) ->
getr regsE 26 = Z_to_bv 64 (bot + 1) -> getr regsE 27 = Z_to_bv 64 top -> getr regsE 25 = Z_to_bv 64 bimg ->
getr regsE 23 = Z_to_bv 64 left -> val_mem trasegs (mrestrict (w_H W) memE) (sp1 + 160) 8 (bot + 1 - top) ->
getr regsE 18 = Z_to_bv 64 sv2 -> getr regsE 20 = Z_to_bv 64 sv4 ->
SRr trasegs W (mkCfg (mkst regsE (Z_to_bv 64 0x87d90) memE (seg_rom trasegs)) mdE) (f4_post c0 top bot left).
Lemma fl_f4l_step : forall m, f4_stmt m -> f4_stmt (Datatypes.S m).
Proof.
intros m IH. unfold f4_stmt.
intros x y c0 top bot left regsE memE mdE Hm Hx Hl Ht0 Hy Hbt HBDw HJE WK HKE E6 E21r E22r E14r E15r E10r E13r E12r E26r E29r E25r E23r V160r E18s E20s.
wctx_names. wprelude HJE. pose proof HJE as HJE0.
pose proof (proj1 (proj2 HJE)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_img _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_img _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_img _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216E.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200E.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 144 a176 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 176 a184 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V184) as V184E.
set (x' := if y <? bot then x else x - 1). set (y' := if y <? bot then y + 1 else top).
assert (Hxy' : c0 <= x' < Wd /\ top <= y' <= bot) by (subst x' y'; destruct (Z.ltb_spec y bot); lia).
assert (HyW : 0 <= y' * Wd <= (Hd - 1) * Wd) by (clear - Hxy' Hbt Ht0 RW RH; nia).
assert (HW1 : (Hd - 1) * Wd = Hd * Wd - Wd) by (clear; lia).
assert (Hp : 0 <= y' * Wd + x' /\ y' * Wd + x' < Nb) by (rewrite HN; clear - Hxy' Hl HyW HW1 RW RH; nia).
assert (Hp32 : y' * Wd + x' < 2 ^ 32) by (clear - Hp HN RW RH; nia).
assert (HtW : 0 <= top * Wd <= y * Wd /\ y * Wd <= (Hd - 1) * Wd) by (clear - Hy Hbt Ht0 RW RH; nia).
set (p := y' * Wd + x') in *.
destruct (wimg_byteF B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as (VbC & RbC & AbC & SbC).
destruct (wimg_byteF B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as (VbB & RbB & AbB & SbB).
set (bC := bval (aview trasegs (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview trasegs (w_H W) memc) (bimg + p)) in *.
remember (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15. pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite E10r in E10.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite E13r in E13. pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E29. rewrite E29r in E29. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (fimg + p)) by (subst E; exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bimg + p)) by (subst E; exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bB) by (subst E; exact (ew_Ereg_extra regsE _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 a176) by (subst E; exact (ew_Ereg_extra regsE _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 a184) by (subst E; exact (ew_Ereg_extra regsE _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 Wd) by (subst E; exact (ew_Ereg_extra regsE _ 7)).
assert (E28 : ew E 40 = Z_to_bv 64 (bot + 1 - top)) by (subst E; exact (ew_Ereg_extra regsE _ 8)).
pose proof E39 as E7.
assert (HS : st_ok trasegs E ss_f4 (restrict (w_H W) (mkst regsE (Z_to_bv 64 0x87d90) memE (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f4, f4_regs.
apply (rn_st_ok_any E 0x87d90 _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite E14r; reflexivity].
- reflexivity.
- unfold f4_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216E]|]. apply Forall_nil.
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E35, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 160 8 _ (bot + 1 - top)); [cbn [sv_denot]; rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160r]|]. apply Forall_nil.
- unfold f4_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E9, E33, E35, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f4_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E15, E13, E23, E26, E7, E29, E12, E10, E28, E32, E25, E33, E34, E35, E36, E37, E38, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memE).
aj_run_tok tratbl_lib_ok HS HJE SHOK FLBspan.
1: { unfold f4_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 ltac:(unfold ss_f4, f4_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresE)) as WK1.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_and_ffff_off _ 15 y 1) in HGEU by (first [evE; exact E15 | lia]); rewrite (U_atom _ 26 (bot + 1)) in HGEU by (first [evE; exact E26 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 6%nat; pose proof (proj1 HJE) as HAR2.
-
assert (Ex' : x' = x - 1) by (subst x'; destruct (Z.ltb_spec y bot); lia). assert (Ey' : y' = top) by (subst y'; destruct (Z.ltb_spec y bot); lia).
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x87dd4.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SOff 12 0) = y' * Wd) by (rewrite (U_atom Ev 12 (top * Wd) ltac:(evE; exact E12)) by (clear - HtW HW1 HN HNb RW; lia); rewrite Ey'; reflexivity);
assert (HIDX : U Ev (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
assert (F33 : ew Ev 33 = Z_to_bv 64 (fimg + p)) by (evE; exact E33);
assert (UA : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32))) = fimg + p)
by (rewrite (U_add_atom_zext32 Ev 32 _ fimg ltac:(evE; exact E32)) by lia; rewrite HIDX, Z.mod_small by lia; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Ra0;
pose proof (st_ok_pin_rege Ev ssv msv 10%bv (SOff 33 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; clear HXQ HA6 HIDX UA Ra0 F33 end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJE) as HAR3.
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x87de8.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (fimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (fimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR3 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SOff 12 0) = y' * Wd) by (rewrite (U_atom Ev 12 (top * Wd) ltac:(evE; exact E12)) by (clear - HtW HW1 HN HNb RW; lia); rewrite Ey'; reflexivity);
assert (HIDX : U Ev (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
assert (G35 : ew Ev 35 = Z_to_bv 64 (bimg + p)) by (evE; exact E35);
assert (UB : U Ev (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32))) = bimg + p)
by (rewrite (U_add_atom_zext32 Ev 25 _ bimg ltac:(evE; exact E25)) by lia; rewrite HIDX, Z.mod_small by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Ra1;
pose proof (st_ok_pin_rege Ev ssv msv 11%bv (SOff 35 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra1; cbn [sv_denot]; rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; clear HXQ HA6 HIDX UB Ra1 G35 end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJE) as HAR4.
aj_run_tok tratbl_lib_ok HS HJE SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 35 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 35 (bimg + p) cc ltac:(evE; exact E35)) by lia | rewrite (U_atom Ex 35 (bimg + p) ltac:(evE; exact E35)) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR4 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HEQ end;
rewrite branch_eq_U in HEQ; rewrite (U_atom _ 34 bC) in HEQ by (first [evE; exact E34 | lia]); rewrite (U_atom _ 36 bB) in HEQ by (first [evE; exact E36 | lia]);
[apply Z.eqb_eq in HEQ | apply Z.eqb_neq in HEQ]; reshok_bx HS 6%nat; pose proof (proj1 HJE) as HAR5.
+
assert (Hxc' : c0 < x').
{ destruct (Z_lt_le_dec c0 x') as [Hl'|Hge]; [exact Hl'|]. exfalso. apply HBDw. unfold BD.
replace (top * Wd + c0) with p by (subst p; rewrite Ey'; f_equal; clear - Hge Hxy'; lia). fold bC in SbC. rewrite SbC, SbB. f_equal. exact HEQ. }
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x87d90.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
rreg HS (15%bv : bv 5) Rg15. rreg HS (14%bv : bv 5) Rg14. rreg HS (6%bv : bv 5) Rg6.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SOff 12 0) = y' * Wd) by (rewrite (U_atom Ev 12 (top * Wd) ltac:(evE; exact E12)) by (clear - HtW HW1 HN HNb RW; lia); rewrite Ey'; reflexivity);
assert (HIDX : U Ev (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
rreg_by HS (13%bv : bv 5) (Z_to_bv 64 x') (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HXQ)) Rg13;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (y' * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HA6)) Rg10 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (IH x' y' c0 top bot left); [ rewrite Ex', Ey'; clear - Hm Hx Hy Ht0 Hbt Hxc' Ex'; nia | lia | exact Hl | exact Ht0 | lia | exact Hbt | exact HBDw | exact HJE | exact WK5
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F4_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite Rg6; evE; exact F6 | rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| exact Rg14
| rewrite Rg15; evE; rewrite Ey'; exact E29
| exact Rg10 | exact Rg13
| rewrite (HKr 12%bv ltac:(cbv; tauto)); exact E12r | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r
| rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r | exact V160x
| rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s | rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s ].
+
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x8755c.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F4_KEPTX HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
rreg HS (6%bv : bv 5) Rg6. rreg HS (10%bv : bv 5) Rg10. rreg HS (11%bv : bv 5) Rg11.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (x' - left + 1))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width2 Ev _ 23 x' left HXQ ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) Rg14 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, x' end.
split; [reflexivity|]. split; [exact HJE|]. split; [exact WK5|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F4_KEPTX In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite Rg6; evE; exact F6|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [exact (proj1 Hxy')|]. split; [exact Rg14|].
split; [exact V160x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite Rg10; evE; exact E38|]. split; [rewrite Rg11; evE; exact E37|].
split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s | rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s].
-
assert (Ex' : x' = x) by (subst x'; destruct (Z.ltb_spec y bot); lia). assert (Ey' : y' = y + 1) by (subst y'; destruct (Z.ltb_spec y bot); lia).
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x87dd4.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) = y' * Wd) by (rewrite (U_add_atoms Ev 10 39 (y * Wd) Wd ltac:(evE; exact E10) ltac:(evE; exact E7)) by (clear - HtW HN HNb RW; lia); rewrite Ey'; clear; lia);
assert (HIDX : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
assert (F33 : ew Ev 33 = Z_to_bv 64 (fimg + p)) by (evE; exact E33);
assert (UA : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32))) = fimg + p)
by (rewrite (U_add_atom_zext32 Ev 32 _ fimg ltac:(evE; exact E32)) by lia; rewrite HIDX, Z.mod_small by lia; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Ra0;
pose proof (st_ok_pin_rege Ev ssv msv 10%bv (SOff 33 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; clear HXQ HA6 HIDX UA Ra0 F33 end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJE) as HAR3.
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x87de8.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (fimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (fimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR3 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) = y' * Wd) by (rewrite (U_add_atoms Ev 10 39 (y * Wd) Wd ltac:(evE; exact E10) ltac:(evE; exact E7)) by (clear - HtW HN HNb RW; lia); rewrite Ey'; clear; lia);
assert (HIDX : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
assert (G35 : ew Ev 35 = Z_to_bv 64 (bimg + p)) by (evE; exact E35);
assert (UB : U Ev (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) (SLit 32)) (SLit 32))) = bimg + p)
by (rewrite (U_add_atom_zext32 Ev 25 _ bimg ltac:(evE; exact E25)) by lia; rewrite HIDX, Z.mod_small by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Ra1;
pose proof (st_ok_pin_rege Ev ssv msv 11%bv (SOff 35 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra1; cbn [sv_denot]; rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; clear HXQ HA6 HIDX UB Ra1 G35 end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJE) as HAR4.
aj_run_tok tratbl_lib_ok HS HJE SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 35 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 35 (bimg + p) cc ltac:(evE; exact E35)) by lia | rewrite (U_atom Ex 35 (bimg + p) ltac:(evE; exact E35)) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR4 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HEQ end;
rewrite branch_eq_U in HEQ; rewrite (U_atom _ 34 bC) in HEQ by (first [evE; exact E34 | lia]); rewrite (U_atom _ 36 bB) in HEQ by (first [evE; exact E36 | lia]);
[apply Z.eqb_eq in HEQ | apply Z.eqb_neq in HEQ]; reshok_bx HS 6%nat; pose proof (proj1 HJE) as HAR5.
+
assert (Hxc' : c0 < x').
{ destruct (Z_lt_le_dec c0 x') as [Hl'|Hge]; [exact Hl'|]. exfalso. apply HBDw. unfold BD.
replace (top * Wd + c0) with p by (subst p; exfalso; clear - Hge Ex' Hx; lia). fold bC in SbC. rewrite SbC, SbB. f_equal. exact HEQ. }
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x87d90.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
rreg HS (15%bv : bv 5) Rg15. rreg HS (14%bv : bv 5) Rg14. rreg HS (6%bv : bv 5) Rg6.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) = y' * Wd) by (rewrite (U_add_atoms Ev 10 39 (y * Wd) Wd ltac:(evE; exact E10) ltac:(evE; exact E7)) by (clear - HtW HN HNb RW; lia); rewrite Ey'; clear; lia);
assert (HIDX : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
rreg_by HS (13%bv : bv 5) (Z_to_bv 64 x') (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HXQ)) Rg13;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (y' * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HA6)) Rg10 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply (IH x' y' c0 top bot left); [ rewrite Ex', Ey'; clear - Hm Hx Hy Ht0 Hbt Hxc' Ex'; nia | lia | exact Hl | exact Ht0 | lia | exact Hbt | exact HBDw | exact HJE | exact WK5
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F4_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite Rg6; evE; exact F6 | rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| exact Rg14
| rewrite Rg15; evE; rewrite E15, unsigned_lit_small by lia; rewrite Ey'; reflexivity
| exact Rg10 | exact Rg13
| rewrite (HKr 12%bv ltac:(cbv; tauto)); exact E12r | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r
| rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r | exact V160x
| rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s | rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s ].
+
aj_run_to_tok tratbl_lib_ok HS HJE SHOK FLBspan 0x8755c.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsE _ F4_KEPTX HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
rreg HS (6%bv : bv 5) Rg6. rreg HS (10%bv : bv 5) Rg10. rreg HS (11%bv : bv 5) Rg11.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (x' - left + 1))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width2 Ev _ 23 x' left HXQ ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) Rg14 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, x' end.
split; [reflexivity|]. split; [exact HJE|]. split; [exact WK5|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F4_KEPTX In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite Rg6; evE; exact F6|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [exact (proj1 Hxy')|]. split; [exact Rg14|].
split; [exact V160x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite Rg10; evE; exact E38|]. split; [rewrite Rg11; evE; exact E37|].
split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s | rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s].
Qed.
Lemma fl_f4l : forall m, f4_stmt m.
Proof. induction m as [|m IH]; [unfold f4_stmt; intros; exfalso; nia | exact (fl_f4l_step m IH)]. Qed.
Definition f4s_mem : smem := f4_mem.
Definition f4s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (23%nat, mkAF 0 65534 0); (12%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0);
(27%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0); (13%nat, mkAF 1 65535 0); (39%nat, mkAF 1 65535 0);
(32%nat, HPTR 0); (25%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, HPTR 0); (36%nat, mkAF 0 255 0);
(37%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_f4s : sstate := mkSS 0x87d20 sr_atoms f4s_mem None f4s_facts.
Lemma fl_f4 : forall (c0 top bot left : Z) (regsF : bvmap 5 word) memF mdF,
0 <= left <= c0 -> c0 < Wd -> 0 <= top <= bot -> bot < Hd -> BDp (top * Wd + c0) ->
ajournal trasegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 6 = Z_to_bv 64 SB -> getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp ->
getr regsF 23 = Z_to_bv 64 left -> getr regsF 12 = Z_to_bv 64 (top * Wd) -> val_mem trasegs (mrestrict (w_H W) memF) (sp1 + 160) 8 (bot + 1 - top) -> getr regsF 27 = Z_to_bv 64 top ->
getr regsF 26 = Z_to_bv 64 top -> getr regsF 13 = Z_to_bv 64 Wd -> getr regsF 25 = Z_to_bv 64 bimg -> getr regsF 18 = Z_to_bv 64 sv2 -> getr regsF 20 = Z_to_bv 64 sv4 ->
SRr trasegs W (mkCfg (mkst regsF (Z_to_bv 64 0x87d20) memF (seg_rom trasegs)) mdF) (f4_post c0 top bot left).
Proof.
intros c0 top bot left regsF memF mdF Hl Hc0 Htb Hbt HBDw HJF WK HKF E6 E21r E22r E23r E12r V160r E29r E26r E7r E25r E18s E20s.
wctx_names. wprelude HJF. pose proof HJF as HJF0.
pose proof (proj1 (proj2 HJF)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF fimg Nb HAR Hfi) as (Hf16 & Hf4096 & Hfceil & Hfh_ia & Hfpres & _). pose proof (proj1 Hfh_ia) as Hfh.
pose proof (blk_off_img _ _ _ _ _ _ fimg Nb HAR Hfi) as Hfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_img _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_img _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_img _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HW1 : (Hd - 1) * Wd = Hd * Wd - Wd) by (clear; lia).
assert (HtW : 0 <= top * Wd <= (Hd - 1) * Wd) by (clear - Htb Hbt RW RH; nia).
assert (Hp : 0 <= top * Wd + (Wd - 1) /\ top * Wd + (Wd - 1) < Nb) by (rewrite HN; clear - HtW HW1 RW RH Hc0 Hl; nia).
set (p := top * Wd + (Wd - 1)) in *.
assert (HSpresF : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 144 a176 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 176 a184 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V184) as V184F.
destruct (wimg_byteF B LAWS lyc Sc W sp1 memc memF mdF fimg Nb p WK HAR Hfi ltac:(lia)) as (VbC & RbC & AbC & SbC).
destruct (wimg_byteF B LAWS lyc Sc W sp1 memc memF mdF bimg Nb p WK HAR Hbi ltac:(lia)) as (VbB & RbB & AbB & SbB).
set (bC := bval (aview trasegs (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview trasegs (w_H W) memc) (bimg + p)) in *.
remember (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12.
pose proof (EE 27%nat 27%bv eq_refl) as E29. rewrite E29r in E29.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 13%nat 13%bv eq_refl) as E7. rewrite E7r in E7.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsF _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (fimg + p)) by (subst E; exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; exact (ew_Ereg_extra regsF _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bimg + p)) by (subst E; exact (ew_Ereg_extra regsF _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bB) by (subst E; exact (ew_Ereg_extra regsF _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 a176) by (subst E; exact (ew_Ereg_extra regsF _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 a184) by (subst E; exact (ew_Ereg_extra regsF _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 Wd) by (subst E; exact (ew_Ereg_extra regsF _ 7)).
assert (E28 : ew E 40 = Z_to_bv 64 (bot + 1 - top)) by (subst E; exact (ew_Ereg_extra regsF _ 8)).
assert (HS : st_ok trasegs E ss_f4s (restrict (w_H W) (mkst regsF (Z_to_bv 64 0x87d20) memF (seg_rom trasegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f4s.
apply (rn_st_ok_any E 0x87d20 _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Ereg.
- reflexivity.
- unfold f4s_mem, f4_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184F]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216F]|]. apply Forall_nil.
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E35, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val trasegs E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176F]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200F]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trasegs E _ sp1 160 8 _ (bot + 1 - top)); [cbn [sv_denot]; rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160r]|]. apply Forall_nil.
- unfold f4s_mem, f4_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val].
rewrite E9, E33, E35, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f4s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E23, E12, E28, E29, E26, E7, E39, E32, E25, E33, E34, E35, E36, E37, E38, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT3" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memF).
aj_run_to_tok tratbl_lib_ok HS HJF SHOK FLBspan 0x87d40.
1: { unfold f4s_mem, f4_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memF _ mdF sp1 HAR HFr1 HG1 ltac:(unfold ss_f4s, f4s_mem, f4_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresF)) as WK1.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
assert (HD : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Wd - 1) by (apply (U_dec_zext16 Ev 13 Wd ltac:(evE; exact E7)); lia);
assert (HI0 : U Ev (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) = p) by (rewrite U_SAlu; cbn [zalu_raw]; rewrite HD, (U_atom Ev 12 (top * Wd) ltac:(evE; exact E12)) by (clear - HtW HW1 HN HNb RW; lia); subst p; apply zcanon_id; rewrite M64_val; clear - HtW HW1 HN HNb RW; lia);
assert (F33 : ew Ev 33 = Z_to_bv 64 (fimg + p)) by (evE; exact E33);
assert (UA : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) (SLit 32)) (SLit 32))) = fimg + p)
by (rewrite (U_add_atom_zext32 Ev 32 _ fimg ltac:(evE; exact E32)) by lia; rewrite HI0, Z.mod_small by lia; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Ra0;
pose proof (st_ok_pin_rege Ev ssv msv 10%bv (SOff 33 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; clear HD HI0 UA Ra0 F33 end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJF) as HAR2.
aj_run_to_tok tratbl_lib_ok HS HJF SHOK FLBspan 0x87d54.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (fimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (fimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR2 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
assert (HD : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Wd - 1) by (apply (U_dec_zext16 Ev 13 Wd ltac:(evE; exact E7)); lia);
assert (HI0 : U Ev (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) = p) by (rewrite U_SAlu; cbn [zalu_raw]; rewrite HD, (U_atom Ev 12 (top * Wd) ltac:(evE; exact E12)) by (clear - HtW HW1 HN HNb RW; lia); subst p; apply zcanon_id; rewrite M64_val; clear - HtW HW1 HN HNb RW; lia);
assert (G35 : ew Ev 35 = Z_to_bv 64 (bimg + p)) by (evE; exact E35);
assert (UB : U Ev (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 13 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) (SLit 32)) (SLit 32))) = bimg + p)
by (rewrite (U_add_atom_zext32 Ev 25 _ bimg ltac:(evE; exact E25)) by lia; rewrite HI0, Z.mod_small by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Ra1;
pose proof (st_ok_pin_rege Ev ssv msv 11%bv (SOff 35 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra1; cbn [sv_denot]; rewrite G35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS; clear HD HI0 UB Ra1 G35 end.
norm_ss HS. reshok_bx HS 6%nat.
pose proof (proj1 HJF) as HAR3.
aj_run_tok tratbl_lib_ok HS HJF SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 35 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 35 (bimg + p) cc ltac:(evE; exact E35)) by lia | rewrite (U_atom Ex 35 (bimg + p) ltac:(evE; exact E35)) by lia];
eapply (obl_of_block trasegs _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR3 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
srr_branch_tok tratbl_lib_ok HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HNE end;
rewrite branch_ne_U in HNE; rewrite (U_atom _ 34 bC) in HNE by (first [evE; exact E34 | lia]); rewrite (U_atom _ 36 bB) in HNE by (first [evE; exact E36 | lia]);
[apply (proj1 (negb_true_iff _)) in HNE; apply Z.eqb_neq in HNE | apply (proj1 (negb_false_iff _)) in HNE; apply Z.eqb_eq in HNE];
reshok_bx HS 6%nat; pose proof (proj1 HJF) as HAR4.
-
aj_run_to_tok tratbl_lib_ok HS HJF SHOK FLBspan 0x8755c.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsF _ (6%bv :: 21%bv :: 22%bv :: 23%bv :: 27%bv :: 18%bv :: 20%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (10%bv : bv 5) Rg10. rreg HS (11%bv : bv 5) Rg11.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (Wd - left)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width0 Ev 13 23 Wd left ltac:(evE; exact E7) ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) Rg14 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (Wd - 1) end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK4|].
split; [intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]|].
split; [rewrite (HKr 6%bv ltac:(cbv; tauto)); exact E6|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [clear - Hc0 RW; lia|]. split; [rewrite Rg14; f_equal; lia|].
split; [exact V160x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite Rg10; evE; exact E38|]. split; [rewrite Rg11; evE; exact E37|].
split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s | rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s].
-
aj_run_to_tok tratbl_lib_ok HS HJF SHOK FLBspan 0x87d90.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
assert (Hcw : c0 < Wd - 1).
{ destruct (Z_lt_le_dec c0 (Wd - 1)) as [Hlt|Hge]; [exact Hlt|]. exfalso. apply HBDw. unfold BD.
replace (top * Wd + c0) with p by (subst p; clear - Hge Hc0; lia). fold bC in SbC. rewrite SbC, SbB. f_equal. exact HNE. }
pose proof (regs_kept_of_st_ok trasegs _ _ _ regsF _ (6%bv :: 21%bv :: 22%bv :: 23%bv :: 27%bv :: 18%bv :: 20%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
rreg HS (14%bv : bv 5) Rg14. rreg HS (15%bv : bv 5) Rg15. rreg HS (10%bv : bv 5) Rg10. rreg HS (13%bv : bv 5) Rg13. rreg HS (12%bv : bv 5) Rg12. rreg HS (25%bv : bv 5) Rg25.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (top + (bot + 1 - top))) (denot_add_atoms Ev 26 40 top (bot + 1 - top) ltac:(evE; exact E26) ltac:(evE; exact E28) ltac:(lia) ltac:(lia) ltac:(lia)) Rg26 end.
rewrite (st_ok_restrict_mkst trasegs _ _ _ _ HS eq_refl). cbn [ss_pc].
assert (HM0 : (Wd - 1 - c0) * Hd <= (Wd - 1) * Hd) by (apply Z.mul_le_mono_nonneg_r; clear - RH Hc0 Hl; lia).
assert (HM1 : (Wd - 1 - c0) * Hd + (bot - top) < Wd * Hd + Hd) by (clear - HM0 Htb Hbt RH RW; lia).
eapply (fl_f4l (Z.to_nat (Wd * Hd + Hd)) (Wd - 1) top c0 top bot left);
[ rewrite Z2Nat.id by (clear - RW RH; nia); exact HM1 | clear - Hcw RW; lia | exact Hl | lia | lia | exact Hbt | exact HBDw | exact HJF | exact WK4
| intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]
| rewrite (HKr 6%bv ltac:(cbv; tauto)); exact E6 | rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| exact Rg14
| rewrite Rg15; evE; exact E29
| rewrite Rg10; evE; rewrite E12; f_equal; subst p; clear; lia
| rewrite Rg13; evE; rewrite E7, unsigned_lit_small by lia; f_equal; lia
| rewrite Rg12; evE; exact E12
| rewrite Rg26; f_equal; lia
| rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r
| rewrite Rg25; evE; exact E25
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r
| exact V160x
| rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s | rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s ].
Qed.
End d.
End c.
End b.
