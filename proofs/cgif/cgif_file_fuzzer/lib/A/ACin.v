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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACjf ACjj.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
Lemma mod32_of_mod64 : forall x, (x mod 2 ^ 64) mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.rem_mul_r by lia. rewrite Z.add_mod by lia. rewrite Z.mod_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia. rewrite Z.add_0_r. apply Z.mod_mod. lia. Qed.
Lemma U_sext32_mod : forall E a, U E (SExt true 32 a) mod 2 ^ 32 = U E a mod 2 ^ 32.
Proof.
intros E a. rewrite U_SExt. unfold zcanon, M64. rewrite mod32_of_mod64.
change (Z.of_N 32) with 32. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (Z.of_N 32) with 32.
set (y := U E a mod 2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod. replace (y + 2 ^ 31 - 2 ^ 31) with y by lia. subst y. apply Z.mod_mod. lia.
Qed.
Lemma U_sub_mod32 : forall E a b, U E (SAlu ALU_SUB a b) mod 2 ^ 32 = (U E a - U E b) mod 2 ^ 32.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. apply mod32_of_mod64. Qed.
Lemma U_zext32_sh : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = U E a mod 2 ^ 32.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
change (zcanon 32) with 32. change (Z.land 32 63) with 32. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon, M64. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). lia.
Qed.
Lemma U_subw_mod32 : forall E a b, U E (SAluw ALU_SUB a b) mod 2 ^ 32 = (U E a - U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw].
unfold bv_wrap, bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
set (x := U E a). set (y := U E b).
rewrite (Z.mod_mod_divide _ (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity).
rewrite <- Zminus_mod_idemp_l. rewrite (Z.mod_mod_divide _ (2 ^ 32) (2 ^ 32)) by (exists 1; reflexivity).
rewrite Zminus_mod_idemp_l.
replace (x mod 2 ^ 32 - y mod 2 ^ 32 + 2 ^ 31 - 2 ^ 31) with (x mod 2 ^ 32 - y mod 2 ^ 32) by ring.
symmetry. apply Zminus_mod.
Qed.
Lemma U_and_ffff_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 16 ->
U E (SAlu ALU_AND (SOff n c) (SLit 65535)) = x + c.
Proof.
intros E n x c Hn Rx Rc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x c Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
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
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
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
Section h.
Variables (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd a176 a184 : Z) (sv2 sv4 : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 200) 8 Wd /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 208) 8 Hd.
Hypothesis HRES : 0 <= a176 < 2 ^ 64 /\ 0 <= a184 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 144) 8 a176 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 176) 8 a184.
Hypothesis HFIMG : val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
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
Ltac noW := cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr.
Ltac awrRO := repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]); try (match goal with |- ?g => idtac "AWR-LEFT" g end).
Definition F2_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 21; 28; 29; 30; 31]%bv.
Definition F2_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 20; 22; 23; 24; 25; 26; 27]%bv.

Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_ewset_other in Hw by lia;
rewrite ?E9, ?unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac awrW E9 FFS :=
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]).
Definition f2_postX (top i : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' bot,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2630)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
top <= bot < Hd /\
getr regs' 18 = Z_to_bv 64 bot /\ getr regs' 26 = Z_to_bv 64 top /\ getr regs' 19 = Z_to_bv 64 65535 /\
getr regs' 25 = Z_to_bv 64 bimg /\ getr regs' 27 = Z_to_bv 64 top /\ getr regs' 20 = Z_to_bv 64 top /\ getr regs' 24 = Z_to_bv 64 sv4 /\
(bot = top \/ exists c0, 0 <= c0 < Wd /\ BDp (bot * Wd + c0)) /\ (forall p, (bot + 1) * Wd <= p < (i + 1) * Wd -> ~ BDp p).
Definition f2_regs := sr_set sr_atoms 19%bv (SLit 65535).
Definition f2_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 224 232 224 224 [YP09.mkChunk 224 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 240 248 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 216 224 216 216 [YP09.mkChunk 216 (CVal 8 (SOff 34 0))] ].
Definition f2_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (33%nat, mkAF SB SB 0); (18%nat, mkAF 1 65534 0); (23%nat, mkAF 1 65535 0); (20%nat, mkAF 0 65533 0);
(32%nat, HPTR 0); (25%nat, HPTR 0); (34%nat, HPTR 4); (22%nat, HPTR 3); (27%nat, mkAF 0 65533 0); (26%nat, mkAF 0 65533 0) ] [] [].
Definition ss_f2 : sstate := mkSS 0x25f4 f2_regs f2_mem None f2_facts.
Definition f2_stmtX (m : nat) : Prop :=
forall (i top v : Z) (regsE : bvmap 5 word) memE mdE,
i - top <= Z.of_nat m -> 0 <= top -> top < i < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 22 = Z_to_bv 64 cfp -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 g -> getr regsE 19 = Z_to_bv 64 65535 ->
getr regsE 18 = Z_to_bv 64 i -> getr regsE 21 = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v mod 2 ^ 32 = i * Wd ->
getr regsE 23 = Z_to_bv 64 Wd -> getr regsE 25 = Z_to_bv 64 bimg -> getr regsE 20 = Z_to_bv 64 top -> getr regsE 27 = Z_to_bv 64 top -> getr regsE 26 = Z_to_bv 64 top -> getr regsE 24 = Z_to_bv 64 sv4 ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x25f4)) memE (seg_rom SEGS)) mdE) (f2_postX top i).
Lemma fl_f2l_stepX : forall m, f2_stmtX m -> f2_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold f2_stmtX.
intros i top v regsE memE mdE Hm Ht0 Hi HJE WK HKE E22r V216g E19r E18r E21r Rv Mv E24r E25r E20r E27r E26r E24s.
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
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi Ht0 RW RH; nia).
assert (HiW32 : i * Wd < 2 ^ 32) by (clear - Hi Ht0 RW RH; nia).
assert (HSpresE : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memE 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216E.
remember (Eimg (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 g])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 g]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite E18r in E18. pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21.
pose proof (EE 23%nat 23%bv eq_refl) as E24. rewrite E24r in E24. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20. pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. assert (E23 : ew E 34 = Z_to_bv 64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (HS : st_ok_pi SEGS VAL E ss_f2 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x25f4)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f2, f2_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x25f4) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E19r; reflexivity].
- reflexivity.
- unfold f2_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216E]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ g); [cbn [sv_denot]; rewrite E23, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216g]|]. apply Forall_nil.
- unfold f2_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f2_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E33, E18, E24, E20, E32, E25, E23, E22, E27, E26, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 33 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { unfold f2_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 ltac:(unfold ss_f2, f2_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresE)) as WK1.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 216) 8 g HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(unfold ss_f2, f2_mem; intros kk _; revert kk; noW) V216g) as V216a.
cbn [ms_mem restrict mkst] in V216a.
prreg HS (12%bv : bv 5) Qa2. prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
assert (F32 : ew Ev 32 = Z_to_bv 64 fimg) by (evE; exact E32); assert (F25 : ew Ev 25 = Z_to_bv 64 bimg) by (evE; exact E25); assert (F21 : ew Ev 21 = Z_to_bv 64 v) by (evE; exact E21);
assert (UA : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 32))) = fimg + i * Wd)
by (rewrite (U_add_atom_zext32 Ev 32 _ fimg F32) by lia; rewrite (U_atom Ev 21 v F21) by lia; rewrite Mv; reflexivity);
assert (UB : U Ev (SAlu ALU_ADD (SOff 25 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 32))) = bimg + i * Wd)
by (rewrite (U_add_atom_zext32 Ev 25 _ bimg F25) by lia; rewrite (U_atom Ev 21 v F21) by lia; rewrite Mv; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Qa0;
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Qa1  end.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX (i * Wd) Wd (Z_to_bv 64 (BASE + 0x2610)) HJE WK1) end.
- lia. - lia. - lia.
- unfold spZ. rewrite Qsp; evE. rewrite (EE 2%nat 2%bv eq_refl), (HKE 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite Qgp; evE. rewrite (EE 3%nat 3%bv eq_refl), (HKE 3%bv ltac:(cbv; tauto)). exact Hgp.
- rewrite Qtp; evE. rewrite (EE 4%nat 4%bv eq_refl), (HKE 4%bv ltac:(cbv; tauto)). exact Htp.
- exact Qa0. - exact Qa1. - rewrite Qa2; evE. exact E24.
- exact Qra. - apply ret_ok_codeptr_v; [lazymatch goal with |- _ <= ?k < _ => try unfold k end; lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vv & -> & HJ2 & HP2 & Hv & Hz & WK2 & Kc & Lc).
clear Qa0 Qa1 Qa2 Qra Qsp Qgp Qtp UA UB.
assert (HSpres2 : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) mem2 a).
{ intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 216) 8 _ Lc ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V216a) as V216b.
lazymatch type of HS with st_ok _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 33 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2]%nat HS2  end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 33%nat.
pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 g HFr4 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk _; revert kk; noW) V216b) as V216c.
cbn [ms_mem restrict mkst] in V216c.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpres2)) as WK5.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (Hwit : exists c0, 0 <= c0 < Wd /\ BDp (i * Wd + c0)).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
destruct (Classical_Prop.classic (exists c0, 0 <= c0 < Wd /\ BDp (i * Wd + c0))) as [Y | Y]; [exact Y | exfalso; apply Hc];
lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
evE; unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros j Hj D; apply Y; exists j; split; [exact Hj | exact D] end. }
clear Hc. reshok_bx HS 33%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x2630.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK5 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (6%bv : bv 5) R6. prreg HS (21%bv : bv 5) R21. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, i end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite R6; evE; exact E33|]. split; [rewrite R21; evE; exact E23|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|].
split; [rewrite R18; evE; exact E18|]. split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [exact R19|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r|]. split; [rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E24s|].
split; [right; exact Hwit | intros p Hp; exfalso; clear - Hp; lia].
-
assert (XNI : forall j, 0 <= j < Wd -> ~ BDp (i * Wd + j)).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
enough (Hvz : ew Ex n = getr regs2 10) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hc, U_SOff, Hvz, Z.add_0_r; symmetry; apply zcanon_id;
pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia);
evE; unfold CLOB; cbn [map nth]; reflexivity end. }
assert (XROW : forall p, i * Wd <= p < (i + 1) * Wd -> ~ BDp p).
{ intros p Hp. replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp. lia. }
reshok_bx HS 33%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK5 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
clear Hc. psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HLTU end;
rewrite branch_ltu_U in HLTU; rewrite (U_atom _ 20 top) in HLTU by (first [evE; exact E20 | lia]); rewrite (U_and_ffff_off _ 18 i (-1)) in HLTU by (first [evE; exact E18 | lia]);
[apply Z.ltb_lt in HLTU | apply Z.ltb_ge in HLTU]; reshok_bx HS 33%nat; pose proof (proj1 HJ2) as HAR6.
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x25f4.
1: { awrRO. }
rename HFr into HFr6. rename HG into HG6. clear HF.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 g HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk _; revert kk; noW) V216c) as V216d.
cbn [ms_mem restrict mkst] in V216d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 g HFr6 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk _; revert kk; noW) V216d) as V216e.
cbn [ms_mem restrict mkst] in V216e.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK6 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR6 HFr6 HG6 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK6 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK7.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (G21 : ew Ev 21 = Z_to_bv 64 v) by (evE; exact E21); assert (G24 : ew Ev 23 = Z_to_bv 64 Wd) by (evE; exact E24);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (U Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0)))) (denot_lit_U Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0))) R21;
assert (Mv' : U Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0)) mod 2 ^ 32 = (i - 1) * Wd)
by (rewrite U_subw_mod32, (U_atom Ev 21 v G21), (U_atom Ev 23 Wd G24) by lia;
rewrite <- Zminus_mod_idemp_l, Mv; replace (i * Wd - Wd) with ((i - 1) * Wd) by lia; apply Z.mod_small; clear - Hi Ht0 RW HiW32; nia);
pose proof (U_range Ev (SAluw ALU_SUB (SOff 21 0) (SOff 23 0))) as Rv'; rewrite M64_val in Rv'  end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i - 1) top); [ lia | exact Ht0 | lia | exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact V216e | exact R19
| rewrite R18; evE; rewrite E18, unsigned_lit_small by lia; f_equal; lia
| exact R21 | exact Rv' | exact Mv'
| rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E24r | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r
| rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E24s ]. }
cbv beta. intros W9 c9 _ (-> & regs9 & mem9 & md9 & bot9 & -> & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & XB9 & XN9).
split; [reflexivity|]. exists regs9, mem9, md9, bot9. split; [reflexivity|]. split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
split; [exact Y5|]. split; [exact Y6|]. split; [exact Y7|]. split; [exact Y8|]. split; [exact Y9|]. split; [exact Y10|]. split; [exact Y11|].
split; [exact Y12|]. split; [exact Y13|]. split; [exact Y14|]. split; [exact XB9|].
intros p Hp. destruct (Z_lt_le_dec p (i * Wd)) as [Hlo | Hhi]; [apply XN9; replace (i - 1 + 1) with i by (clear; lia); clear - Hp Hlo; lia | apply XROW; clear - Hp Hhi; lia].
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x2630.
1: { awrRO. }
rename HFr into HFr6. rename HG into HG6. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK6 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR6 HFr6 HG6 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK6 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK7.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F2_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (6%bv : bv 5) R6. prreg HS (21%bv : bv 5) R21. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, top end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK7|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F2_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite R6; evE; exact E33|]. split; [rewrite R21; evE; exact E23|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|].
split; [rewrite R18; evE; exact E27|]. split; [rewrite (HKr 26%bv ltac:(cbv; tauto)); exact E26r|]. split; [exact R19|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20r|]. split; [rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E24s|].
split; [left; reflexivity|].
intros p Hp. apply XROW. assert (Ei : i = top + 1) by (clear - HLTU Hi; lia). clear - Hp Ei. subst i. lia.
Qed.
Lemma fl_f2lX : forall m, f2_stmtX m.
Proof. induction m as [|m IH]; [unfold f2_stmtX; intros; exfalso; lia | exact (fl_f2l_stepX m IH)]. Qed.
Definition f2s_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 96 104 96 96 [YP09.mkChunk 96 (CVal 8 (SOff 35 0))];
YP09.mkRegion (Some 9%nat) 200 224 216 224 [YP09.mkChunk 200 (CVal 8 (SOff 36 0)); YP09.mkChunk 208 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 240 248 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 33 0))] ].
Definition f2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (33%nat, mkAF SB SB 0); (27%nat, mkAF 0 65534 0); (34%nat, mkAF 1 65535 0); (36%nat, mkAF 1 65535 0);
(25%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3) ] [] [].
Definition ss_f2s : sstate := mkSS 0x25a4 sr_atoms f2s_mem None f2s_facts.
Lemma fl_f2X : forall (top : Z) (regsF : bvmap 5 word) memF mdF,
0 <= top < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp ->
getr regsF 27 = Z_to_bv 64 top -> getr regsF 20 = Z_to_bv 64 sv4 -> getr regsF 25 = Z_to_bv 64 bimg ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x25a4)) memF (seg_rom SEGS)) mdF) (f2_postX top (Hd - 1)).
Proof.
intros top regsF memF mdF Htp1 HJF WK HKF E21r E22r E27r E20r E25r.
wctx_names. wprelude HJF. pose proof HJF as HJF0. pose proof HSAV2 as (Rsv2 & V96).
pose proof (proj1 (proj2 HJF)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HSpresF : forall a, sp1 - FBAND <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbF.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 208 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V112) as V208F.
pose proof (val_mem_wkeptF B lyc Sc W sp1 memc memF 96 sv2 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V96) as V96F.
remember (Eimg (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 Hd; Z_to_bv 64 sv2; Z_to_bv 64 Wd])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 SB; Z_to_bv 64 Hd; Z_to_bv 64 sv2; Z_to_bv 64 Wd]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27. pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Hd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 sv2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 4)).
assert (HS : st_ok_pi SEGS VAL E ss_f2s (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 0x25a4)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f2s. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x25a4) _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold f2s_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresF; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 96 8 _ sv2); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V96F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200F]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ Hd); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208F]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbF]|]. apply Forall_nil.
- unfold f2s_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f2s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E33, E27, E34, E36, E25, E21, E22, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT3" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 33 0) E (mrestrict (w_H W) memF).
hei_havoc HS; paj_run_tok RUN HS HJF SHOK FLBspan.
1: { unfold f2s_mem. awrW E9 FFS. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memF _ mdF sp1 HAR HFr1 HG1 ltac:(unfold ss_f2s, f2s_mem; wscr_windows E9) ltac:(lia) ltac:(lia) HSpresF)) as WK1.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
exfalso.
rewrite branch_eq_U in Hc. rewrite (U_atom _ 27 top) in Hc by (first [evE; exact E27 | lia]). rewrite (U_atom _ 34 Hd) in Hc by (first [evE; exact E34 | lia]).
apply Z.eqb_eq in Hc. clear - Hc Htp1. lia.
- clear Hc. reshok_bx HS 33%nat. pose proof (proj1 HJF) as HAR2.
hei_havoc HS; paj_run_tok RUN HS HJF SHOK FLBspan.
1: { awrW E9 FFS. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_and_ffff_off _ 27 top 0) in HGEU by (first [evE; exact E27 | lia]); rewrite (U_and_ffff_off _ 34 Hd (-1)) in HGEU by (first [evE; exact E34 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 33%nat; pose proof (proj1 HJF) as HAR3.
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x2630.
1: { awrW E9 FFS. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (21%bv :: 22%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (6%bv : bv 5) R6. prreg HS (18%bv : bv 5) R18. prreg HS (26%bv : bv 5) R26. prreg HS (19%bv : bv 5) R19. prreg HS (27%bv : bv 5) R27. prreg HS (24%bv : bv 5) R24.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (UT : U Ev (SAlu ALU_AND (SOff 27 0) (SLit 65535)) = top) by (rewrite (U_and_ffff_off Ev 27 top 0 ltac:(evE; exact E27)) by lia; lia);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 top) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UT)) R20 end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, top end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK3|].
split; [intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]|].
split; [rewrite R6; evE; exact E33|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|].
split; [rewrite R18; evE; rewrite E34, unsigned_lit_small by lia; f_equal; lia|]. split; [rewrite R26; evE; exact E27|]. split; [exact R19|].
split; [rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r|]. split; [rewrite R27; evE; exact E27|]. split; [exact R20|]. split; [rewrite R24; evE; exact E20|].
split; [left; reflexivity|].
intros p Hp; exfalso. assert (Et : top = Hd - 1) by (clear - HGEU Htp1; lia). rewrite Et in Hp. clear - Hp. lia.
+
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x25f4.
1: { awrW E9 FFS. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 216 8%N (SOff 21 0) g HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; evE; rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V216 end; clear HR1 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V216.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (22%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (23%bv : bv 5) R23. prreg HS (19%bv : bv 5) R19. prreg HS (18%bv : bv 5) R18. prreg HS (24%bv : bv 5) R24. prreg HS (27%bv : bv 5) R27. prreg HS (26%bv : bv 5) R26.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (G34 : ew Ev 34 = Z_to_bv 64 Hd) by (evE; exact E34); assert (G36 : ew Ev 36 = Z_to_bv 64 Wd) by (evE; exact E36); assert (G27 : ew Ev 27 = Z_to_bv 64 top) by (evE; exact E27);
assert (UT : U Ev (SAlu ALU_AND (SOff 27 0) (SLit 65535)) = top) by (rewrite (U_and_ffff_off Ev 27 top 0 G27) by lia; lia);
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 top) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UT)) R20;
assert (UH1 : U Ev (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Hd - 1) by (apply (U_dec_zext16 Ev 34 Hd G34); lia);
assert (UV : U Ev (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 34 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) (SOff 36 0)) = (Hd - 1) * Wd)
by (apply U_mul_small1; [exact UH1 | apply (U_atom Ev 36 Wd G36); lia | lia | lia | clear - RW RH; nia]);
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 ((Hd - 1) * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UV)) R21  end.
pmkst HS.
eapply (fl_f2lX (Z.to_nat Hd) (Hd - 1) top ((Hd - 1) * Wd));
[ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJF | exact WK3
| intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]
| rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r
| exact V216
| exact R19
| rewrite R18; evE; rewrite E34, unsigned_lit_small by lia; f_equal; lia
| exact R21 | clear - RW RH; nia | rewrite Z.mod_small; clear - RW RH; nia
| rewrite R23; evE; exact E36
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E25r
| exact R20
| rewrite R27; evE; exact E27 | rewrite R26; evE; exact E27
| rewrite R24; evE; exact E20 ].
Qed.
End h.
End f.
End e.
End d.
