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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACit.
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
Lemma U_and_ffff_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 16 ->
U E (SAlu ALU_AND (SOff n c) (SLit 65535)) = x + c.
Proof.
intros E n x c Hn Rx Rc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x c Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_zext32 : forall E a, U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32)) = U E a mod 2 ^ 32.
Proof.
intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SLit.
rewrite (zcanon_id 32) by (rewrite M64_val; lia). change (Z.land 32 63) with 32.
pose proof (U_range E a) as Hr. rewrite M64_val in Hr.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
unfold zcanon. rewrite M64_val. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). lia.
Qed.

Lemma U_mul_small : forall E a b, U E a * U E b < 2 ^ 64 -> U E (SMd M_MUL a b) = U E a * U E b.
Proof.
intros E a b H. rewrite U_SMd. cbn [zmd_raw]. pose proof (U_range E a). pose proof (U_range E b).
apply zcanon_id. rewrite M64_val. split; [apply Z.mul_nonneg_nonneg; lia | exact H].
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
Lemma U_add_lit0 : forall E a, U E (SAlu ALU_ADD a (SLit 0)) = U E a.
Proof. intros E a. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. apply U_range. Qed.
Lemma U_add_atom_zext32 : forall E nb a b, ew E nb = Z_to_bv 64 b -> 0 <= b -> b + 2 ^ 32 <= 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nb 0) (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 32)) (SLit 32))) = b + U E a mod 2 ^ 32.
Proof.
intros E nb a b Hb Rb Hhi. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_zext32, (U_atom E nb b Hb) by lia.
pose proof (Z.mod_pos_bound (U E a) (2 ^ 32) ltac:(lia)). apply zcanon_id. rewrite M64_val. lia.
Qed.
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
Ltac wscr_windows E9 :=
cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_ewset_other in Hw by lia;
rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia |]);
destruct Hr.
Ltac off_windows E9 :=
cbn [ss_mem]; let kk := fresh "kk" in let Hk := fresh "Hk" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros kk Hk (r & Hr & Hw); cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr];
[cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in Hw; rewrite ?ew_ewset_other in Hw by lia;
rewrite E9, unsigned_lit_small in Hw by lia; lia |]);
destruct Hr.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition s2o_regs := sr_set (sr_set (sr_set sr_atoms 12%bv (SOff 22 0)) 14%bv (SOff 22 1)) 27%bv (SLit 65535).
Definition s2o_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 88 88 [YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 152 160 152 160 [];
YP09.mkRegion (Some 9%nat) 160 168 160 160 [YP09.mkChunk 160 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 168 176 168 176 [];
YP09.mkRegion (Some 9%nat) 192 232 192 192 [YP09.mkChunk 200 (CVal 8 (SOff 11 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
YP09.mkChunk 224 (CVal 8 (SOff 36 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 240 256 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 35 0))] ].
Definition s2o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (11%nat, mkAF 1 65535 0); (22%nat, mkAF 1 65534 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 0); (36%nat, HPTR 0); (33%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0); (35%nat, HPTR 3) ] [] [].
Definition ss_s2o : sstate := mkSS 0x1c5c s2o_regs s2o_mem None s2o_facts.
Definition s2t_regs := sr_set sr_atoms 27%bv (SLit 65535).
Definition s2t_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 88 88 [YP09.mkChunk 88 (CVal 8 (SOff 34 0))];
YP09.mkRegion (Some 9%nat) 160 168 160 160 [YP09.mkChunk 160 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SOff 22 0))];
YP09.mkRegion (Some 9%nat) 192 232 192 192 [YP09.mkChunk 200 (CVal 8 (SOff 37 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
YP09.mkChunk 224 (CVal 8 (SOff 36 0)); YP09.mkChunk 216 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 9%nat) 240 256 240 240 [YP09.mkChunk 240 (CVal 8 (SOff 6 0)); YP09.mkChunk 248 (CVal 8 (SOff 35 0))] ].
Definition s2t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (22%nat, mkAF 1 65534 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 0); (36%nat, HPTR 0); (33%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0); (35%nat, HPTR 3);
(37%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2t : sstate := mkSS 0x1d00 s2t_regs s2t_mem None s2t_facts.
Definition s2o_postX (top r : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' bot,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x1dd8)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\ getr regs' 27 = Z_to_bv 64 65535 /\
getr regs' 19 = Z_to_bv 64 top /\ getr regs' 15 = Z_to_bv 64 (bot + 1) /\ top <= bot < Hd /\
val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 216) 8 bimg /\ val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 184) 8 top /\
(bot = top \/ exists c0, 0 <= c0 < Wd /\ PDp (bot * Wd + c0)) /\ (forall p, (bot + 1) * Wd <= p < (r + 1) * Wd -> ~ PDp p).
Definition s2o_stmtX (m : nat) : Prop :=
forall (i top v18 : Z) (regsE : bvmap 5 word) memE mdE,
i - top <= Z.of_nat m -> 0 <= top -> top < i < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 25 = Z_to_bv 64 g -> getr regsE 24 = Z_to_bv 64 cfp -> getr regsE 27 = Z_to_bv 64 65535 ->
getr regsE 14 = Z_to_bv 64 (i + 1) -> getr regsE 12 = Z_to_bv 64 i -> getr regsE 11 = Z_to_bv 64 Wd -> getr regsE 22 = Z_to_bv 64 i ->
getr regsE 18 = Z_to_bv 64 v18 -> 0 <= v18 < 2 ^ 64 -> v18 mod 2 ^ 32 = i * Wd ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 top ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 192) 8 top -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 88) 8 (top + 1) ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 184) 8 top ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1c5c)) memE (seg_rom SEGS)) mdE) (s2o_postX top i).
Lemma fl_s2o_stepX : forall m, s2o_stmtX m -> s2o_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold s2o_stmtX.
intros i top v18 regsE memE mdE Hm Ht0 Hi HJE WK HKE E6 E25r E22r E27r E20r E12r E11r E24r E18r Rv18 Mv18 V224 V120 V208 V24 V192.
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
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi Ht0 RW RH; nia).
assert (HiW32 : i * Wd < 2 ^ 32) by (clear - Hi Ht0 RW RH; nia).
assert (HSpresE : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 248 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216E.
remember (Eimg (Ereg regsE [Z_to_bv 64 bimg; Z_to_bv 64 top; Z_to_bv 64 (top + 1); Z_to_bv 64 bfp; Z_to_bv 64 fimg])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 bimg; Z_to_bv 64 top; Z_to_bv 64 (top + 1); Z_to_bv 64 bfp; Z_to_bv 64 fimg]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite E11r in E11. pose proof (EE 22%nat 22%bv eq_refl) as E24. rewrite E24r in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25. pose proof (EE 24%nat 24%bv eq_refl) as E22. rewrite E22r in E22.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite E18r in E18.
assert (E32 : ew E 32 = Z_to_bv 64 bimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 top) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (top + 1)) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 bfp) by (subst E; exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (HS : st_ok_pi SEGS VAL E ss_s2o (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1c5c)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2o, s2o_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1c5c) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E12r; cbn [sv_denot]; rewrite (ew_Eimg_Ereg_nat regsE _ 22 22%bv eq_refl), E24r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity] | intros X; discriminate X | rewrite E20r; cbn [sv_denot]; rewrite (ew_Eimg_Ereg_nat regsE _ 22 22%bv eq_refl), E24r, unsigned_lit_small by lia; reflexivity] | intros X; discriminate X | rewrite E27r; reflexivity].
- reflexivity.
- unfold s2o_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresE; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 88 8 _ (top + 1)); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V24]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ top); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V120]|]. apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 192 8 _ top); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 216 8 _ bimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V224]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite F6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|]. apply Forall_nil.
- unfold s2o_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2o_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E11, E24, E25, E22, E32, E36, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1c8c.
1: { unfold s2o_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr1. rename HG into HG1. clear HF.
assert (W1 : forall a, in_wrange E (ss_mem ss_s2o) a -> wscr sp1 a).
{ unfold ss_s2o, s2o_mem; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite E9, unsigned_lit_small in Hw by lia; unfold wscr; lia. }
assert (O1 : forall kk, (sp1 + 88 <= kk < sp1 + 96 \/ sp1 + 160 <= kk < sp1 + 168 \/ sp1 + 184 <= kk < sp1 + 232) -> ~ in_wrange E (ss_mem ss_s2o) kk).
{ unfold ss_s2o, s2o_mem; cbn [ss_mem]. intros kk Hk (r & Hr & Hw); cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite E9, unsigned_lit_small in Hw by lia; lia. }
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 W1 ltac:(lia) ltac:(lia) HSpresE)) as WK1.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 216) 8 bimg HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V224) as V224a.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 160) 8 top HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V120) as V120a.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 192) 8 top HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V208) as V208a.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 88) 8 (top + 1) HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V24) as V24a.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 184) 8 top HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(intros kk Hk; apply O1; cbn [Z.of_nat] in Hk; lia) V192) as V192a.
cbn [ms_mem restrict mkst] in V224a, V120a, V208a, V24a, V192a.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SOff 22 1) (i + 1) HR1
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E24, unsigned_lit_small by lia; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V56a end; clear HR1;
let r3 := eval vm_compute in (nth 3 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 3 r3 HS ltac:(vm_compute; reflexivity)) as HR3; cbn [ms_mem restrict mkst] in HR3;
lazymatch type of HR3 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 168 8%N (SOff 22 0) i HR3
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160a end; clear HR3 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V56a, V160a.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ (18%bv :: 24%bv :: 22%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr1. cbn [ms_regs restrict] in HKr1.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F32 : ew Ev 32 = Z_to_bv 64 bimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E32);
assert (F36 : ew Ev 36 = Z_to_bv 64 fimg) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E36);
assert (F18 : ew Ev 18 = Z_to_bv 64 v18) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E18);
assert (F11 : ew Ev 11 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E11);
assert (UB : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32))) = bimg + i * Wd)
by (rewrite (U_add_atom_zext32 Ev 32 _ bimg F32) by lia; rewrite (U_atom Ev 18 v18 F18) by lia; rewrite Mv18; reflexivity);
assert (UF : U Ev (SAlu ALU_ADD (SOff 36 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32))) = fimg + i * Wd)
by (rewrite (U_add_atom_zext32 Ev 36 _ fimg F36) by lia; rewrite (U_atom Ev 18 v18 F18) by lia; rewrite Mv18; reflexivity);
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) R19;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (eq_trans (U_add_lit0 Ev _) UB))) R26;
rreg_by HS (20%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UF)) R20;
rreg_by HS (23%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (eq_trans (U_add_lit0 Ev _) UF))) R23 end.
prreg HS (6%bv : bv 5) R6. prreg HS (21%bv : bv 5) R21. prreg HS (27%bv : bv 5) R27.
pmkst HS.
eapply SRr_bind.
{ pose proof (fl_s2iX B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO (Z.to_nat Wd)) as S2I. unfold s2i_stmtX in S2I.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (S2I 0 (ms_regs msX) (ms_mem msX) mdX i top) end;
[ rewrite Z2Nat.id by lia; lia | lia | lia | lia | exact HJE | exact WK1
| intros r Hr; transitivity (getr regsE r); [apply HKr1; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite R6, ?ew_ewset_other by lia; exact F6
| rewrite (HKr1 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite (HKr1 24%bv ltac:(cbv; tauto)); exact E22r
| rewrite R23; f_equal; lia
| rewrite R20; f_equal; lia
| rewrite R26; f_equal; lia
| rewrite R19; f_equal; lia
| rewrite R21, ?ew_ewset_other by lia; rewrite E11; f_equal; lia
| exact V208a | exact V56a ]. }
cbv beta. intros W2 c2 _ (-> & regsI & memI & mdI & pcI & -> & HJI & WKI & LI & HKI & H6I & HexI).
assert (HSpresI : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memI a).
{ intros a Ha. pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
assert (HK5I : forall r : bv 5, In r WKEPT5 -> getr regsI r = getr regs r).
{ intros r Hr. rewrite (HKI r) by (cbv [WKEPT5 In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr).
transitivity (getr regsE r); [apply HKr1; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]. }
assert (I27 : getr regsI 27 = Z_to_bv 64 65535) by (rewrite (HKI 27%bv eq_refl); exact R27).
assert (I22 : getr regsI 24 = Z_to_bv 64 cfp) by (rewrite (HKI 24%bv eq_refl), (HKr1 24%bv ltac:(cbv; tauto)); exact E22r).
assert (I25 : getr regsI 25 = Z_to_bv 64 g) by (rewrite (HKI 25%bv eq_refl), (HKr1 25%bv ltac:(cbv; tauto)); exact E25r).
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 216) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V224a) as V224b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 184) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V192a) as V192b.
destruct HexI as [(-> & H22I & XNI) | (-> & Hwit & H11I & H14I & H21I & H22cI)].
2: {
apply SRr_ret. split; [reflexivity|]. exists regsI, memI, mdI, i. split; [reflexivity|]. split; [exact HJI|]. split; [exact WKI|].
split; [exact HK5I|]. split; [exact H6I|]. split; [exact H21I|]. split; [exact H22cI|]. split; [exact I27|].
split; [exact H11I|]. split; [exact H14I|]. split; [lia|]. split; [exact V224b|]. split; [exact V192b|].
split; [right; exact Hwit | intros p Hp; exfalso; clear - Hp; lia]. }
assert (I9 : getr regsI 9 = Z_to_bv 64 sp1) by (rewrite (HKI 9%bv eq_refl), (HKr1 9%bv ltac:(cbv; tauto)); exact (eq_trans (HKE 9%bv ltac:(cbv; tauto)) H9)).
prreg HS (22%bv : bv 5) R24h. prreg HS (18%bv : bv 5) R18h.
assert (I24 : getr regsI 22 = Z_to_bv 64 i) by (rewrite H22I, R24h, ?ew_ewset_other by lia; exact E24).
assert (I18 : getr regsI 18 = Z_to_bv 64 v18) by (rewrite (HKI 18%bv eq_refl), R18h, ?ew_ewset_other by lia; exact E18).
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 160) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V120a) as V120b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 192) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V208a) as V208b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 88) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V24a) as V24b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 168) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V160a) as V160b.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 240 SB WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 248 bfp WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 200 Wd WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 224 fimg WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as V216I.
clear HS HS0 SHOK R19 R26 R20 R23 R6 R21 R27 R24h R18h UB UF F32 F36 F18 F11.
remember (Eimg (Ereg regsI [Z_to_bv 64 bimg; Z_to_bv 64 top; Z_to_bv 64 (top + 1); Z_to_bv 64 bfp; Z_to_bv 64 fimg; Z_to_bv 64 Wd])) as Et eqn:HEt. assert (HEIt : img_env VAL A_LIM Et) by (subst Et; apply Eimg_env).
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 bimg; Z_to_bv 64 top; Z_to_bv 64 (top + 1); Z_to_bv 64 bfp; Z_to_bv 64 fimg; Z_to_bv 64 Wd]) Et) by (rewrite HEt; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9. pose proof (EEt 6%nat 6%bv eq_refl) as T6. rewrite H6I in T6.
pose proof (EEt 22%nat 22%bv eq_refl) as T24. rewrite I24 in T24. pose proof (EEt 18%nat 18%bv eq_refl) as T18. rewrite I18 in T18.
pose proof (EEt 25%nat 25%bv eq_refl) as T25. rewrite I25 in T25. pose proof (EEt 24%nat 24%bv eq_refl) as T22. rewrite I22 in T22.
assert (T32 : ew Et 32 = Z_to_bv 64 bimg) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 top) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 (top + 1)) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 bfp) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 3)).
assert (T36 : ew Et 36 = Z_to_bv 64 fimg) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 4)).
assert (T37 : ew Et 37 = Z_to_bv 64 Wd) by (subst Et; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsI _ 5)).
assert (HS : st_ok_pi SEGS VAL Et ss_s2t (restrict (w_H W) (mkst regsI (Z_to_bv 64 (BASE + 0x1d00)) memI (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2t, s2t_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any Et (BASE + 0x1d00) _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite I27; reflexivity].
- reflexivity.
- unfold s2t_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite T9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresI; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 88 8 _ (top + 1)); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V24b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 160 8 _ top); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V120b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 168 8 _ i); [cbn [sv_denot]; rewrite T24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite T37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200I]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 192 8 _ top); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208b]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite T36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216I]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 216 8 _ bimg); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V224b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite T6, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbI]|].
apply Forall_cons; [apply (chunk_ok_val SEGS Et _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpI]|]. apply Forall_nil.
- unfold s2t_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite T9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2t_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite T9, T6, T24, T25, T22, T32, T36, T33, T34, T35, T37, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT2" g end]. }
clear HEt. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) Et (mrestrict (w_H W) memI).
pose proof (proj1 HJI) as HARI.
hei_havoc HS; paj_run_tok RUN HS HJI SHOK FLBspan.
1: { unfold s2t_mem. repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]). }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (val_mem_run_out Et _ W memI _ (sp1 + 216) 8 bimg HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V224b) as V224c.
pose proof (val_mem_run_out Et _ W memI _ (sp1 + 160) 8 top HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V120b) as V120c.
pose proof (val_mem_run_out Et _ W memI _ (sp1 + 192) 8 top HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V208b) as V208c.
pose proof (val_mem_run_out Et _ W memI _ (sp1 + 88) 8 (top + 1) HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V24b) as V24c.
pose proof (val_mem_run_out Et _ W memI _ (sp1 + 184) 8 top HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V192b) as V192c.
cbn [ms_mem restrict mkst] in V224c, V120c, V208c, V24c, V192c.
assert (W2 : forall a, in_wrange Et (ss_mem ss_s2t) a -> wscr sp1 a) by (unfold ss_s2t, s2t_mem; wscr_windows T9).
pose proof (wkept_trans B _ _ _ _ _ _ _ WKI (wkept_of_run B LAWS Et _ lyc Sc W memI _ mdI sp1 HARI HFr2 HG2 W2 ltac:(lia) ltac:(lia) HSpresI)) as WK2.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_ltu_U in Hc. rewrite (U_atom _ 33 top) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | lia]).
rewrite (U_and_ffff_off _ 22 i (-1)) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T24 | lia]).
apply Z.ltb_lt in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x1c5c.
1: { unfold s2t_mem. repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]). }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HARb HFrb HGb ltac:(wscr_windows T9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (6%bv :: 24%bv :: 25%bv :: WKEPT5) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr3. cbn [ms_regs restrict] in HKr3.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V224c) as V224d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 top HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V120c) as V120d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 192) 8 top HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V208c) as V208d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 88) 8 (top + 1) HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V24c) as V24d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 184) 8 top HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V192c) as V192d.
cbn [ms_mem restrict mkst] in V224d, V120d, V208d, V24d, V192d.
prreg HS (14%bv : bv 5) Q20. prreg HS (12%bv : bv 5) Q12. prreg HS (11%bv : bv 5) Q11. prreg HS (22%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (G24 : ew Ev 22 = Z_to_bv 64 i) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T24);
assert (G18 : ew Ev 18 = Z_to_bv 64 v18) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T18);
assert (G37 : ew Ev 37 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T37);
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (U Ev (SAluw ALU_SUB (SOff 18 0) (SOff 37 0)))) (denot_lit_U Ev (SAluw ALU_SUB (SOff 18 0) (SOff 37 0))) Q18;
assert (Mv : U Ev (SAluw ALU_SUB (SOff 18 0) (SOff 37 0)) mod 2 ^ 32 = (i - 1) * Wd)
by (rewrite U_subw_mod32, (U_atom Ev 18 v18 G18), (U_atom Ev 37 Wd G37) by lia;
rewrite <- Zminus_mod_idemp_l, Mv18; replace (i * Wd - Wd) with ((i - 1) * Wd) by lia; apply Z.mod_small; clear - Hi Ht0 RW HiW32; nia);
pose proof (U_range Ev (SAluw ALU_SUB (SOff 18 0) (SOff 37 0))) as Rv; rewrite M64_val in Rv end.
pmkst HS.
eapply SRr_mono.
{ eapply (IH (i - 1) top); [ lia | exact Ht0 | lia | exact HJI | exact WK3
| intros r Hr; transitivity (getr regsI r); [apply HKr3; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]
| rewrite (HKr3 6%bv ltac:(cbv; tauto)); exact H6I
| rewrite (HKr3 25%bv ltac:(cbv; tauto)); exact I25
| rewrite (HKr3 24%bv ltac:(cbv; tauto)); exact I22
| exact Q27
| rewrite Q20, ?ew_ewset_other by lia; rewrite T24; f_equal; lia
| rewrite Q12, ?ew_ewset_other by lia; rewrite T24, unsigned_lit_small by lia; f_equal; lia
| rewrite Q11, ?ew_ewset_other by lia; exact T37
| rewrite Q24, ?ew_ewset_other by lia; rewrite T24, unsigned_lit_small by lia; f_equal; lia
| exact Q18 | exact Rv | exact Mv
| exact V224d | exact V120d | exact V208d | exact V24d | exact V192d ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & bot3 & -> & HJ3 & WK6 & HK3 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & XB9 & XN9).
split; [reflexivity|]. exists regs3, mem3, md3, bot3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK6|]. split; [exact HK3|].
split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|]. split; [exact Y5|]. split; [exact Y6|]. split; [exact Y7|]. split; [exact Y8|].
split; [exact Y9|]. split; [exact XB9|].
intros p Hp. destruct (Z_lt_le_dec p (i * Wd)) as [Hlo | Hhi]; [apply XN9; replace (i - 1 + 1) with i by (clear; lia); clear - Hp Hlo; lia|].
replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp Hhi. lia.
-
rewrite branch_ltu_U in Hc. rewrite (U_atom _ 33 top) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | lia]).
rewrite (U_and_ffff_off _ 22 i (-1)) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T24 | lia]).
apply Z.ltb_ge in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJI) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJI SHOK FLBspan 0x1dd8.
1: { unfold s2t_mem. repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]). }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HARb HFrb HGb ltac:(wscr_windows T9) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsI _ (6%bv :: 24%bv :: WKEPT5) HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr3. cbn [ms_regs restrict] in HKr3.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V224c) as V224d.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 184) 8 top HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows T9) V192c) as V192d.
cbn [ms_mem restrict mkst] in V224d, V192d.
prreg HS (21%bv : bv 5) Q21. prreg HS (27%bv : bv 5) Q27. prreg HS (19%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q14. prreg HS (22%bv : bv 5) Q22x.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, top end.
split; [reflexivity|]. split; [exact HJI|]. split; [exact WK3|].
split; [intros r Hr; transitivity (getr regsI r); [apply HKr3; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]|].
split; [rewrite (HKr3 6%bv ltac:(cbv; tauto)); exact H6I|].
split; [rewrite Q21, ?ew_ewset_other by lia; exact T25|]. split; [rewrite Q22x, ?ew_ewset_other by lia; exact T22|]. split; [exact Q27|].
split; [rewrite Q11, ?ew_ewset_other by lia; exact T33|]. split; [rewrite Q14, ?ew_ewset_other by lia; exact T34|]. split; [lia|].
split; [exact V224d|]. split; [exact V192d|]. split; [left; reflexivity|].
intros p Hp. assert (Hti : top = i - 1) by lia. rewrite Hti in Hp.
replace p with (i * Wd + (p - i * Wd)) by (clear; lia). apply XNI. clear - Hp. lia.
Qed.
Lemma fl_s2oX : forall m, s2o_stmtX m.
Proof. induction m as [|m IH]; [unfold s2o_stmtX; intros; exfalso; lia | exact (fl_s2o_stepX m IH)]. Qed.
Definition s2s_regs := sr_set sr_atoms 10%bv (SOff 19 0).
Definition s2s_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
YP09.mkRegion (Some 9%nat) 160 168 160 168 [];
YP09.mkRegion (Some 9%nat) 192 216 192 200 [YP09.mkChunk 200 (CVal 8 (SOff 35 0)); YP09.mkChunk 208 (CVal 8 (SOff 15 0))] ].
Definition s2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (19%nat, mkAF 0 65534 0); (15%nat, mkAF 1 65535 0);
(21%nat, HPTR 4); (22%nat, HPTR 3); (35%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2s : sstate := mkSS 0x1c1c s2s_regs s2s_mem None s2s_facts.
Lemma fl_s2X : forall (top : Z) (regsF : bvmap 5 word) memF mdF,
0 <= top < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkept B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 6 = Z_to_bv 64 SB -> getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp -> getr regsF 24 = Z_to_bv 64 cfp ->
getr regsF 19 = Z_to_bv 64 top -> getr regsF 10 = Z_to_bv 64 top -> getr regsF 15 = Z_to_bv 64 Hd ->
val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 184) 8 top -> val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 216) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x1c1c)) memF (seg_rom SEGS)) mdF) (s2o_postX top (Hd - 1)).
Proof.
intros top regsF memF mdF Htp1 HJF WK HKF E6 E21r E22r E24r E11r E10r E20r V192 V224.
wctx_names. wprelude HJF. pose proof HJF as HJF0.
pose proof (proj1 (proj2 HJF)) as HLY. destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF g CGIF_SIZE HAR Hg) as (Hg16 & Hg4096 & Hgceil & Hgh_ia & _ & _). pose proof (proj1 Hgh_ia) as Hgh.
pose proof (blk_off_imgP _ _ _ _ _ _ g CGIF_SIZE HAR Hg) as Hgh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF cfp FRAME_SIZE HAR Hcf) as (Hc16 & Hc4096 & Hcceil & Hcfh_ia & _ & _). pose proof (proj1 Hcfh_ia) as Hcfh.
pose proof (blk_off_imgP _ _ _ _ _ _ cfp FRAME_SIZE HAR Hcf) as Hcfh_img.
destruct (al_blocks _ _ LAWS lyc Sc W memF mdF bimg Nb HAR Hbi) as (Hb16 & Hb4096 & Hbiceil & Hbih_ia & Hbipres & _). pose proof (proj1 Hbih_ia) as Hbih.
pose proof (blk_off_imgP _ _ _ _ _ _ bimg Nb HAR Hbi) as Hbih_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HSpresF : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memF a) by (intros a Ha; apply HSpres; lia).
pose proof (val_mem_wkept B lyc Sc W sp1 memc memF 200 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V200) as V200F.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memF 208 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V112) as V208F.
remember (Eimg (Ereg regsF [Z_to_bv 64 bimg; Z_to_bv 64 bfp; Z_to_bv 64 fimg; Z_to_bv 64 Wd])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 bimg; Z_to_bv 64 bfp; Z_to_bv 64 fimg; Z_to_bv 64 Wd]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 19%nat 19%bv eq_refl) as E11. rewrite E11r in E11. pose proof (EE 15%nat 15%bv eq_refl) as E20. rewrite E20r in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E35 : ew E 35 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 3)).
assert (HS : st_ok_pi SEGS VAL E ss_s2s (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 0x1c1c)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s2s, s2s_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1c1c) _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E10r; cbn [sv_denot]; rewrite (ew_Eimg_Ereg_nat regsF _ 19 19%bv eq_refl), E11r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
- reflexivity.
- unfold s2s_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite E9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable SEGS); apply HSpresF; lia]|]).
+ apply Forall_nil.
+ apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200F]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 208 8 _ Hd); [cbn [sv_denot]; rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V208F]|]. apply Forall_nil.
- unfold s2s_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s2s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E11, E20, E21, E22, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT3" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memF).
hei_havoc HS; paj_run_tok RUN HS HJF SHOK FLBspan.
1: { unfold s2s_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr1. rename HG into HG1. clear HF.
assert (W1 : forall a, in_wrange E (ss_mem ss_s2s) a -> wscr sp1 a) by (unfold ss_s2s, s2s_mem; wscr_windows E9).
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memF _ mdF sp1 HAR HFr1 HG1 W1 ltac:(lia) ltac:(lia) HSpresF)) as WK1.
pose proof (val_mem_run_out E _ W memF _ (sp1 + 216) 8 bimg HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(unfold ss_s2s, s2s_mem; off_windows E9) V224) as V224a.
pose proof (val_mem_run_out E _ W memF _ (sp1 + 184) 8 top HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(unfold ss_s2s, s2s_mem; off_windows E9) V192) as V192a.
cbn [ms_mem restrict mkst] in V224a, V192a.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
rewrite branch_geu_U in Hc. rewrite (U_and_ffff_off _ 19 top 0) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E11 | lia]).
rewrite (U_and_ffff_off _ 15 Hd (-1)) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E20 | lia]).
apply (proj1 (negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJF) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x1dd8.
1: { unfold s2s_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK1 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HARb HFrb HGb ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (6%bv :: 21%bv :: 22%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr2. cbn [ms_regs restrict] in HKr2.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows E9) V224a) as V224b.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 184) 8 top HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows E9) V192a) as V192b.
cbn [ms_mem restrict mkst] in V224b, V192b.
prreg HS (27%bv : bv 5) Q27. prreg HS (19%bv : bv 5) Q11. prreg HS (15%bv : bv 5) Q14.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, top end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK2|].
split; [intros r Hr; transitivity (getr regsF r); [apply HKr2; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]|].
split; [rewrite (HKr2 6%bv ltac:(cbv; tauto)); exact E6|]. split; [rewrite (HKr2 21%bv ltac:(cbv; tauto)); exact E21r|].
split; [rewrite (HKr2 22%bv ltac:(cbv; tauto)); exact E22r|]. split; [exact Q27|].
split; [rewrite Q11, ?ew_ewset_other by lia; exact E11|]. split; [rewrite Q14, ?ew_ewset_other by lia; rewrite E20; f_equal; lia|]. split; [lia|].
split; [exact V224b|]. split; [exact V192b|]. split; [left; reflexivity|].
intros p Hp; exfalso. assert (Htd : top = Hd - 1) by lia. rewrite Htd in Hp. clear - Hp. lia.
-
rewrite branch_geu_U in Hc. rewrite (U_and_ffff_off _ 19 top 0) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E11 | lia]).
rewrite (U_and_ffff_off _ 15 Hd (-1)) in Hc by (first [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E20 | lia]).
apply (proj1 (negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc.
reshok_bx HS 6%nat. pose proof (proj1 HJF) as HARb.
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x1c5c.
1: { unfold s2s_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFrb. rename HG into HGb. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK1 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HARb HFrb HGb ltac:(wscr_windows E9) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (6%bv :: 24%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr2. cbn [ms_regs restrict] in HKr2.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows E9) V224a) as V224b.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 184) 8 top HFrb ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(off_windows E9) V192a) as V192b.
cbn [ms_mem restrict mkst] in V224b, V192b.
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
assert (G11 : ew Ex 19 = Z_to_bv 64 top) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E11);
assert (G20 : ew Ex 15 = Z_to_bv 64 Hd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E20);
assert (G35 : ew Ex 35 = Z_to_bv 64 Wd) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E35);
assert (G9 : ew Ex 9 = Z_to_bv 64 sp1) by (cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact E9);
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0; cbn [ms_mem restrict mkst] in HR0;
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 88 8%N (SOff 19 1) (top + 1) HR0
ltac:(rewrite G9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite G11, unsigned_lit_small by lia; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V24b end; clear HR0;
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SAlu ALU_AND (SOff 19 0) (SLit 65535)) top HR1
ltac:(rewrite G9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite denot_lit_U, (U_and_ffff_off Ex 19 top 0 G11) by lia; f_equal; lia)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V120b end; clear HR1;
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_pi_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 192 8%N (SOff 19 0) top HR2
ltac:(rewrite G9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite G11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V208b end; clear HR2;
assert (U24 : U Ex (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Hd - 1) by (apply (U_dec_zext16 Ex 15 Hd G20); lia);
assert (U18 : U Ex (SMd M_MUL (SOff 35 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) = Wd * (Hd - 1))
by (rewrite U_mul_small; rewrite (U_atom Ex 35 Wd G35), U24 by lia; [reflexivity | clear - RW RH; nia]);
rreg_by HS (22%bv : bv 5) (Z_to_bv 64 (Hd - 1)) (eq_trans (denot_lit_U Ex _) (f_equal (Z_to_bv 64) U24)) Q24;
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (Wd * (Hd - 1))) (eq_trans (denot_lit_U Ex _) (f_equal (Z_to_bv 64) U18)) Q18 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V24b, V120b, V208b.
prreg HS (27%bv : bv 5) Q27. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (14%bv : bv 5) Q20. prreg HS (25%bv : bv 5) Q25.
pmkst HS.
eapply (fl_s2oX (Z.to_nat Hd) (Hd - 1) top (Wd * (Hd - 1)));
[ rewrite Z2Nat.id by lia; lia | lia | lia | exact HJF | exact WK2
| intros r Hr; transitivity (getr regsF r); [apply HKr2; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]
| rewrite (HKr2 6%bv ltac:(cbv; tauto)); exact E6
| rewrite Q25, ?ew_ewset_other by lia; exact E21
| rewrite (HKr2 24%bv ltac:(cbv; tauto)); exact E24r
| exact Q27
| rewrite Q20, ?ew_ewset_other by lia; rewrite E20; f_equal; lia
| rewrite Q12, ?ew_ewset_other by lia; rewrite E20, unsigned_lit_small by lia; f_equal; lia
| rewrite Q11, ?ew_ewset_other by lia; exact E35
| exact Q24 | exact Q18
| clear - RW RH; nia
| rewrite Z.mod_small; clear - RW RH; nia
| exact V224b | exact V120b | exact V208b | exact V24b | exact V192b ].
Qed.
End f.
End d.
End c.
End b.
