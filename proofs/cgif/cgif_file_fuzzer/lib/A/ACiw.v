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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACjj ACjk.
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
Lemma U_width : forall E nx nl x l, ew E nx = Z_to_bv 64 x -> ew E nl = Z_to_bv 64 l -> 0 <= l <= x -> x + 1 < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff nx 1) (SMd M_MUL (SOff nl 0) (SLit 18446744073709551615))) = x - l + 1.
Proof.
intros E nx nl x l Hx Hl Rlx Rx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom_off E nx x 1 Hx), (U_atom E nl l Hl), U_SLit by lia. change (zcanon 18446744073709551615) with (2 ^ 64 - 1).
unfold zcanon. rewrite M64_val. rewrite Zplus_mod_idemp_r. replace (x + 1 + l * (2 ^ 64 - 1)) with ((x - l + 1) + l * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma U_sub_not_ltu' : forall E nx na nb x a b c, ew E nx = Z_to_bv 64 x -> ew E na = Z_to_bv 64 a -> ew E nb = Z_to_bv 64 b ->
0 <= x - (if a + c <? b then 0 else 1) -> x < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> 0 <= a + c < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
U E (SAlu ALU_SUB (SOff nx 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SOff na c) (SOff nb 0)) (SLit 1))) = x - (if a + c <? b then 0 else 1).
Proof.
intros E nx na nb x a b c Hx Ha Hb Rx Rx1 Ra Rac Rb.
assert (Ht : 0 <= (if a + c <? b then 0 else 1) <= 1) by (destruct (a + c <? b); lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E nx x Hx), (U_atom_off E na a c Ha), (U_atom E nb b Hb), U_SLit by lia. change (zcanon 1) with 1.
destruct (a + c <? b); [change (zcanon 1) with 1; change (Z.lxor 1 1) with 0; change (zcanon 0) with 0 | change (zcanon 0) with 0; change (Z.lxor 0 1) with 1; change (zcanon 1) with 1];
apply zcanon_id; rewrite M64_val; lia.
Qed.
Lemma U_idx16 : forall E ny nw nx y w x, ew E ny = Z_to_bv 64 y -> ew E nw = Z_to_bv 64 w -> ew E nx = Z_to_bv 64 x ->
0 <= y < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= x < 2 ^ 16 ->
U E (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff ny 0) (SLit 65535)) (SOff nw 0)) (SAlu ALU_AND (SOff nx 0) (SLit 65535))) = y * w + x.
Proof.
intros E ny nw nx y w x Hy Hw Hx Ry Rw Rx.
apply U_add_small2; [apply U_mul_small1; [apply U_and16; [apply (U_atom E ny y Hy); lia | lia] | apply (U_atom E nw w Hw); lia | lia | lia | nia]
| apply U_and16; [apply (U_atom E nx x Hx); lia | lia] | nia | lia | nia].
Qed.
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
Hypothesis HFIMG : val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 224) 8 fimg.
Hypothesis HSAV : 0 <= sv2 < 2 ^ 64 /\ 0 <= sv4 < 2 ^ 64 /\
val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 96) 8 sv2 /\ val_mem SEGS (mrestrict (w_H W) memc) (sp1 + 104) 8 sv4.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Let CALL := cmp_callW B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx HC.
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
Ltac evE := rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia.
Ltac evE_in H := rewrite ?ew_havoc_old in H by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub] in H; rewrite ?ew_ewset_other in H by lia.
Ltac noW := cbn [ss_mem]; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr.
Ltac noWk := cbn [ss_mem]; let kk := fresh "kk" in let Hk := fresh "Hk" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros kk Hk (r & Hr & Hw); cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr.
Ltac awrRO := repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]); try (match goal with |- ?g => idtac "AWR-LEFT" g end).
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition S4_CLOB : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 26; 28; 29; 30; 31]%bv.
Definition S4_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 21; 22; 23; 24; 25; 27]%bv.
Lemma s4_clob_cases : forall r : bv 5, reg_in r S4_CLOB = false -> r = 0%bv \/ In r S4_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]). destruct Hin.
Qed.
Definition s4_regs := sr_set (sr_set sr_atoms 19%bv (SLit 65535)) 14%bv (SOff 38 0).
Definition s4_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 160 168 160 160 [YP09.mkChunk 160 (CVal 8 (SOff 41 0))];
YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 39 0))];
YP09.mkRegion (Some 9%nat) 224 256 224 224 [YP09.mkChunk 224 (CVal 8 (SOff 32 0)); YP09.mkChunk 240 (CVal 8 (SOff 38 0)); YP09.mkChunk 248 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))];
YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 37 0))];
YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SOff 40 0))];
YP09.mkRegion (Some 9%nat) 96 112 96 96 [YP09.mkChunk 96 (CVal 8 (SOff 42 0)); YP09.mkChunk 104 (CVal 8 (SOff 43 0))] ].
Definition s4_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (38%nat, mkAF SB SB 0); (20%nat, mkAF 0 65534 0); (18%nat, mkAF 0 65534 0); (27%nat, mkAF 0 65534 0);
(26%nat, mkAF 1 65535 0); (25%nat, mkAF 1 65535 0); (24%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3); (23%nat, mkAF 0 65534 0);
(32%nat, HPTR 0); (33%nat, HPTR 3); (34%nat, HPTR 0); (35%nat, mkAF 0 255 0); (36%nat, HPTR 0); (37%nat, mkAF 0 255 0);
(39%nat, mkAF 0 18446744073709551615 0); (40%nat, mkAF 0 18446744073709551615 0); (41%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s4 : sstate := mkSS 0x1ec8 s4_regs s4_mem None s4_facts.
Definition s4_postX (c0 top bot left : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' right,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x1f8c)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
c0 <= right < Wd /\
getr regs' 26 = Z_to_bv 64 (right - left + 1) /\ val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 (bot + 1 - top) /\ getr regs' 27 = Z_to_bv 64 top /\ getr regs' 23 = Z_to_bv 64 left /\
getr regs' 10 = Z_to_bv 64 a184 /\ getr regs' 11 = Z_to_bv 64 a176 /\ getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4 /\
(exists y', top <= y' < bot + 1 /\ PDp (y' * Wd + right)) /\ (forall i x', top <= i < bot + 1 -> right < x' < Wd -> ~ PDp (i * Wd + x')).
Definition s4_stmtX (m : nat) : Prop :=
forall (x y c0 top bot left : Z) (regsE : bvmap 5 word) memE mdE,
(x - c0) * Hd + (bot - y) < Z.of_nat m -> c0 <= x < Wd -> 0 <= left <= c0 -> 0 <= top -> top <= y <= bot -> bot < Hd -> (c0 < x \/ y = top) -> PDp (top * Wd + c0) ->
(forall i x', top <= i < bot + 1 -> x' < Wd -> (x < x' \/ (x' = x /\ i < y)) -> ~ PDp (i * Wd + x')) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp -> getr regsE 19 = Z_to_bv 64 65535 ->
getr regsE 20 = Z_to_bv 64 y -> getr regsE 18 = Z_to_bv 64 x -> getr regsE 27 = Z_to_bv 64 top -> getr regsE 26 = Z_to_bv 64 (bot + 1) ->
getr regsE 25 = Z_to_bv 64 Wd -> getr regsE 24 = Z_to_bv 64 bimg -> getr regsE 23 = Z_to_bv 64 left -> getr regsE 14 = Z_to_bv 64 SB ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 (bot + 1 - top) ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1ec8)) memE (seg_rom SEGS)) mdE) (s4_postX c0 top bot left).
Lemma fl_s4l_stepX : forall m, s4_stmtX m -> s4_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold s4_stmtX.
intros x y c0 top bot left regsE memE mdE Hm Hx Hl Ht0 Hy Hbt Hxw HPDw XACC HJE WK HKE E21r E22r E19r E20r E18r E27r E26r E24r E25r E23r E14r V224 V120.
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
assert (Hp : 0 <= y * Wd + x /\ y * Wd + x < Nb) by (rewrite HN; clear - Hx Hl HyW HW1 RW RH; nia).
assert (Hp32 : y * Wd + x < 2 ^ 32) by (clear - Hp HN RW RH; nia).
set (p := y * Wd + x) in *.
assert (HSpresE : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memE a) by (intros a Ha; apply HSpres; lia).
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi ltac:(lia)) as [VbC RbC].
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi ltac:(lia)) as [VbB RbB].
set (bC := bval (aview SEGS (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 240 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 248 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 144 a176 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 a184 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V184) as V184E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 224 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) HFIMG) as VfimgE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 96 sv2 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V96) as V96E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 104 sv4 WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V104) as V104E.
remember (Eimg (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 bfp; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 SB; Z_to_bv 64 a184; Z_to_bv 64 a176; Z_to_bv 64 (bot + 1 - top); Z_to_bv 64 sv2; Z_to_bv 64 sv4])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 bfp; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 SB; Z_to_bv 64 a184; Z_to_bv 64 a176; Z_to_bv 64 (bot + 1 - top); Z_to_bv 64 sv2; Z_to_bv 64 sv4]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite E18r in E18. pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite E20r in E20. pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 25%nat 25%bv eq_refl) as E24. rewrite E24r in E24. pose proof (EE 24%nat 24%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 bfp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (fimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 bC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (bimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 bB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 a184) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 a176) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 (bot + 1 - top)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 sv2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 10)).
assert (E43 : ew E 43 = Z_to_bv 64 sv4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 11)).
assert (HS : st_ok_pi SEGS VAL E ss_s4 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x1ec8)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_s4, s4_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x1ec8) _ regsE _ _ (mrestrict (w_H W) memE)).
- apply regs_ok_pin; [subst E; apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E19r; reflexivity] | intros X; discriminate X
| rewrite E14r; cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
- reflexivity.
- unfold s4_mem. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]]]; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ (bot + 1 - top)); [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V120]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VfimgE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 240 8 _ SB); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 248 8 _ bfp); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_nil.
+ rewrite E34, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E36, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 96 8 _ sv2); [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V96E]|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 104 8 _ sv4); [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V104E]|]. apply Forall_nil.
- unfold s4_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E9, E34, E36, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s4_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, E38, E20, E18, E27, E26, E24, E25, E21, E22, E23, E32, E33, E34, E35, E36, E37, E39, E40, E41, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 38 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1ee8.
1: { unfold s4_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 ltac:(unfold ss_s4, s4_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresE)) as WK1.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 216) 8 bimg HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(unfold ss_s4, s4_mem; noWk) V224) as V224a.
pose proof (val_mem_run_out E _ W memE _ (sp1 + 160) 8 (bot + 1 - top) HFr1 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(unfold ss_s4, s4_mem; noWk) V120) as V120a.
cbn [ms_mem restrict mkst] in V224a, V120a.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
assert (F25 : ew Ev 32 = Z_to_bv 64 fimg) by (evE; exact E32);
assert (F20 : ew Ev 20 = Z_to_bv 64 y) by (evE; exact E20); assert (F24 : ew Ev 25 = Z_to_bv 64 Wd) by (evE; exact E24); assert (F18 : ew Ev 18 = Z_to_bv 64 x) by (evE; exact E18);
assert (F34 : ew Ev 34 = Z_to_bv 64 (fimg + p)) by (evE; exact E34);
assert (UI : U Ev (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 20 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 18 0) (SLit 65535))) = p) by (apply (U_idx16 Ev 20 25 18 y Wd x F20 F24 F18); lia);
assert (UA : U Ev (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 20 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 18 0) (SLit 65535))) (SLit 32)) (SLit 32))) = fimg + p)
by (rewrite (U_add_atom_zext32 Ev 32 _ fimg F25) by lia; rewrite UI, Z.mod_small by lia; reflexivity);
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (fimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UA)) Ra0;
pose proof (st_ok_pin_rege Ev ssv msv 10%bv (SOff 34 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra0; cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 38%nat.
pose proof (proj1 HJE) as HAR2.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1efc.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 34 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 34 (fimg + p) cc ltac:(evE; exact E34)) by lia | rewrite (U_atom Ex 34 (fimg + p) ltac:(evE; exact E34)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 38 0) _ len fimg Nb HAR2 Hfi); [rewrite (U_atom Ex 38 SB ltac:(evE; exact E38)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK1 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V224a) as V224b.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 (bot + 1 - top) HFr2 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V120a) as V120b.
cbn [ms_mem restrict mkst] in V224b, V120b.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
assert (G32 : ew Ev 24 = Z_to_bv 64 bimg) by (evE; exact E25);
assert (G20 : ew Ev 20 = Z_to_bv 64 y) by (evE; exact E20); assert (G24 : ew Ev 25 = Z_to_bv 64 Wd) by (evE; exact E24); assert (G18 : ew Ev 18 = Z_to_bv 64 x) by (evE; exact E18);
assert (G36 : ew Ev 36 = Z_to_bv 64 (bimg + p)) by (evE; exact E36);
assert (UI2 : U Ev (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 20 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 18 0) (SLit 65535))) = p) by (apply (U_idx16 Ev 20 25 18 y Wd x G20 G24 G18); lia);
assert (UB : U Ev (SAlu ALU_ADD (SOff 24 0) (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 20 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 18 0) (SLit 65535))) (SLit 32)) (SLit 32))) = bimg + p)
by (rewrite (U_add_atom_zext32 Ev 24 _ bimg G32) by lia; rewrite UI2, Z.mod_small by lia; reflexivity);
rreg_by HS (11%bv : bv 5) (Z_to_bv 64 (bimg + p)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) UB)) Ra1;
pose proof (st_ok_pin_rege Ev ssv msv 11%bv (SOff 36 0) HS ltac:(intros X; discriminate X)
ltac:(cbn [ms_regs restrict mkst]; rewrite Ra1; cbn [sv_denot]; rewrite G36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 38%nat.
pose proof (proj1 HJE) as HAR3.
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan AF_asan3_cmpPixel.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 36 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 36 (bimg + p) cc ltac:(evE; exact E36)) by lia | rewrite (U_atom Ex 36 (bimg + p) ltac:(evE; exact E36)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 38 0) _ len bimg Nb HAR3 Hbi); [rewrite (U_atom Ex 38 SB ltac:(evE; exact E38)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK2 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr3 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V224b) as V224c.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 (bot + 1 - top) HFr3 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V120b) as V120c.
cbn [ms_mem restrict mkst] in V224c, V120c.
prreg HS (10%bv : bv 5) Qa0. prreg HS (11%bv : bv 5) Qa1. prreg HS (12%bv : bv 5) Qa2. prreg HS (13%bv : bv 5) Qa3. prreg HS (14%bv : bv 5) Qa4.
prreg HS (1%bv : bv 5) Qra. prreg HS (2%bv : bv 5) Qsp. prreg HS (3%bv : bv 5) Qgp. prreg HS (4%bv : bv 5) Qtp. prreg HS (8%bv : bv 5) Qs0.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (CALL (ms_regs msX) (ms_mem msX) mdX p (Z_to_bv 64 (BASE + 0x1f24)) HJE WK3) end.
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
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 160) 8 _ Lc ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V120c) as V120d.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
let kk := eval vm_compute in (run_K A_LIM (SOff 38 0) [] ssx) in
jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 5; 6]%nat HS2 end.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q); [ cbn [ms_mem restrict]; apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]] | specialize (HS2 HQ); clear HQ ] end.
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
{ eapply (region_kept_stack_aj SEGS _); [exact Kc | exact HJ2 | evE; rewrite E9; apply unsigned_lit_small; lia | lia | rewrite FFS; lia | lia | lia | lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
reshok_bx HS 38%nat.
pose proof (proj1 HJ2) as HAR4.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK4 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpres2)) as WK5.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr4 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V224d) as V224e.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 (bot + 1 - top) HFr4 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V120d) as V120e.
cbn [ms_mem restrict mkst] in V224e, V120e.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan.
-
assert (HPD : PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = true =>
apply (proj1 (negb_true_iff _)) in Hc; apply Z.eqb_neq in Hc; rewrite U_lit in Hc by lia;
intros HZ; apply Hc; lazymatch goal with |- U ?Ey (SOff n 0) = 0 =>
enough (Hvz : ew Ey n = w64 0) by (rewrite (U_atom Ey n 0 Hvz) by lia; reflexivity) end;
evE; unfold CLOB; cbn [map nth]; rewrite Hv; apply (proj2 Hz); intros HP; exact (HP HZ) end. }
reshok_bx HS 38%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1f8c.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK5 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 (bot + 1 - top) HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V120e) as V120x. cbn [ms_mem restrict mkst] in V120x.
prreg HS (6%bv : bv 5) R6. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (18%bv : bv 5) R18x. prreg HS (20%bv : bv 5) R20x.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (x - left + 1))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width Ev 18 23 x left ltac:(evE; exact E18) ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) R14 end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, x end.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact WK6|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 S4_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite R6; evE; exact E38|].
split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [lia|]. split; [exact R14|].
split; [exact V120x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite R10; evE; exact E39|]. split; [rewrite R11; evE; exact E40|].
split; [rewrite R18x; evE; exact E42|]. split; [rewrite R20x; evE; exact E43|].
split; [exists y; split; [clear - Hy; lia | exact HPD] | intros i' x' Hi' Hx'; apply XACC; [exact Hi' | clear - Hx'; lia | left; clear - Hx'; lia]].
-
assert (HnPD : ~ PDp p).
{ rewrite branch_ne_U in Hc. lazymatch type of Hc with negb (U ?Ex (SOff ?n 0) =? U _ (SLit 0)) = false =>
apply (proj1 (negb_false_iff _)) in Hc; apply Z.eqb_eq in Hc; rewrite U_lit in Hc by lia; apply (proj1 Hz); rewrite <- Hv;
lazymatch goal with |- getr regs2 10 = w64 0 =>
enough (Hvz : U Ex (SOff n 0) = bv_unsigned (getr regs2 10)) by (apply bv_eq; unfold w64; rewrite unsigned_lit_small by lia; rewrite <- Hvz; exact Hc) end;
rewrite U_SOff; evE; unfold CLOB; cbn [map nth]; rewrite Z.add_0_r; apply zcanon_id; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq; rewrite M64_val; change (bv_modulus 64) with (2 ^ 64) in Hq; lia end. }
assert (Hxc : c0 < x).
{ destruct Hxw as [Hl' | Hyt]; [exact Hl'|]. destruct (Z_lt_le_dec c0 x) as [Hl'|Hge]; [exact Hl'|]. exfalso. apply HnPD.
replace p with (top * Wd + c0) by (subst p; rewrite Hyt; f_equal; lia). exact HPDw. }
reshok_bx HS 38%nat. pose proof (proj1 HJ2) as HAR5.
hei_havoc HS; paj_run_tok RUN HS HJ2 SHOK FLBspan.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK5 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK5 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK6.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V224e) as V224f.
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 (bot + 1 - top) HFr5 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V120e) as V120f.
cbn [ms_mem restrict mkst] in V224f, V120f.
clear Hc. hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_atom_off _ 20 y 1) in HGEU by (first [evE; exact E20 | lia]); rewrite (U_atom _ 26 (bot + 1)) in HGEU by (first [evE; exact E26 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 38%nat; pose proof (proj1 HJ2) as HAR6;
(hei_havoc HS; paj_run_to_tok RUNTO HS HJ2 SHOK FLBspan 0x1ec8; [ awrRO | ]);
rename HFr into HFr6; rename HG into HG6; clear HF;
pose proof (wkept_trans B _ _ _ _ _ _ _ WK6 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR6 HFr6 HG6 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK6 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK7;
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 216) 8 bimg HFr6 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V224f) as V224g;
pose proof (val_mem_run_out _ _ W _ _ (sp1 + 160) 8 (bot + 1 - top) HFr6 ltac:(lia) ltac:(cbn [Z.of_nat]; lia) ltac:(noWk) V120f) as V120g;
cbn [ms_mem restrict mkst] in V224g, V120g;
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ S4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr; cbn [ms_regs restrict] in HKr;
prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20; prreg HS (26%bv : bv 5) R26x; prreg HS (14%bv : bv 5) R14x;
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (18%bv : bv 5) (Z_to_bv 64 (x - (if y + 1 <? bot + 1 then 0 else 1)))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_sub_not_ltu' Ev 18 20 26 x y (bot + 1) 1 ltac:(evE; exact E18) ltac:(evE; exact E20) ltac:(evE; exact E26)
ltac:(destruct (Z.ltb_spec (y + 1) (bot + 1)); lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))) R18 end;
pmkst HS.
+
eapply (IH (x - 1) top c0 top bot left); [ clear - Hm Hx Hy Ht0 Hbt Hxc HGEU; nia | lia | exact Hl | exact Ht0 | lia | exact Hbt | right; reflexivity | exact HPDw
|   intros i' x' Hi' HxW' Hd'; destruct (Z.eq_dec x' x) as [-> | Hnx];
[ destruct (Z.eq_dec i' y) as [-> | Hny]; [exact HnPD | apply XACC; [exact Hi' | exact HxW' | right; split; [reflexivity | clear - Hny Hi' Hy HGEU; lia]]]
| apply XACC; [exact Hi' | exact HxW' | left; clear - Hd' Hnx Hi'; lia] ]
| exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 S4_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact R19
| rewrite R20; evE; exact E27
| rewrite R18; f_equal; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia
| rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r | rewrite R26x; evE; exact E26
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E24r | rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E25r | rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r
| rewrite R14x; evE; exact E38
| exact V224g | exact V120g ].
+
eapply (IH x (y + 1) c0 top bot left); [ clear - Hm Hx Hy Ht0 Hbt Hxc HGEU; nia | lia | exact Hl | exact Ht0 | lia | exact Hbt | left; exact Hxc | exact HPDw
|   intros i' x' Hi' HxW' Hd'; destruct (Z.eq_dec x' x) as [-> | Hnx];
[ destruct (Z.eq_dec i' y) as [-> | Hny]; [exact HnPD | apply XACC; [exact Hi' | exact HxW' | right; split; [reflexivity | clear - Hd' Hny; lia]]]
| apply XACC; [exact Hi' | exact HxW' | left; clear - Hd' Hnx Hi'; lia] ]
| exact HJ2 | exact WK7
| intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 S4_KEPT In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r | exact R19
| rewrite R20; evE; rewrite E20, unsigned_lit_small by lia; reflexivity
| rewrite R18; f_equal; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia
| rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E27r | rewrite R26x; evE; exact E26
| rewrite (HKr 25%bv ltac:(cbv; tauto)); exact E24r | rewrite (HKr 24%bv ltac:(cbv; tauto)); exact E25r | rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r
| rewrite R14x; evE; exact E38
| exact V224g | exact V120g ].
Qed.
Lemma fl_s4lX : forall m, s4_stmtX m.
Proof. induction m as [|m IH]; [unfold s4_stmtX; intros; exfalso; nia | exact (fl_s4l_stepX m IH)]. Qed.
Lemma fl_s4X : forall (c0 top bot left : Z) (regsE : bvmap 5 word) memE mdE,
0 <= left <= c0 -> c0 < Wd -> 0 <= top <= bot -> bot < Hd -> PDp (top * Wd + c0) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp -> getr regsE 19 = Z_to_bv 64 65535 ->
getr regsE 20 = Z_to_bv 64 top -> getr regsE 18 = Z_to_bv 64 (Wd - 1) -> getr regsE 27 = Z_to_bv 64 top -> getr regsE 26 = Z_to_bv 64 (bot + 1) ->
getr regsE 25 = Z_to_bv 64 Wd -> getr regsE 24 = Z_to_bv 64 bimg -> getr regsE 23 = Z_to_bv 64 left -> getr regsE 14 = Z_to_bv 64 SB ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 (bot + 1 - top) ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x1ec8)) memE (seg_rom SEGS)) mdE) (s4_postX c0 top bot left).
Proof.
intros c0 top bot left regsE memE mdE Hl Hc0 Htb Hbt HPDw HJE WK HKE E21r E22r E19r E20r E18r E27r E26r E24r E25r E23r E14r V224 V120.
pose proof HGEO as (RW & RH & _).
eapply (fl_s4lX (Z.to_nat (Wd * Hd + Hd)) (Wd - 1) top c0 top bot left);
[ rewrite Z2Nat.id by (clear - RW RH; nia); clear - Hl Hc0 Htb Hbt RW RH; nia | lia | exact Hl | lia | lia | exact Hbt | | exact HPDw
| intros i' x' Hi' Hx' Hd'; exfalso; clear - Hi' Hx' Hd'; lia | exact HJE | exact WK | exact HKE
| exact E21r | exact E22r | exact E19r | exact E20r | exact E18r | exact E27r | exact E26r | exact E24r | exact E25r | exact E23r | exact E14r | exact V224 | exact V120 ].
destruct (Z_lt_le_dec c0 (Wd - 1)); [left; lia | right; reflexivity].
Qed.
End e.
End d.
End c.
End b.
