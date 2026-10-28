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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACjf ACjj ACjk ACjl ACjg.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Notation SB := YC81.SB.
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
Lemma U_add_and16 : forall E a b, U E b < 2 ^ 16 -> U E a + U E b < 2 ^ 64 -> U E (SAlu ALU_ADD a (SAlu ALU_AND b (SLit 65535))) = U E a + U E b.
Proof.
intros E a b Hb Hab. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 65535) with (Z.ones 16).
pose proof (U_range E a). pose proof (U_range E b). rewrite Z.land_ones by lia. rewrite (Z.mod_small (U E b)) by lia.
rewrite (zcanon_id (U E b)) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma U_sub_not_ltu2 : forall E nx A nb x a b, ew E nx = Z_to_bv 64 x -> U E A = a -> ew E nb = Z_to_bv 64 b ->
0 <= x - (if a <? b then 0 else 1) -> x < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
U E (SAlu ALU_SUB (SOff nx 0) (SAlu ALU_XOR (SAlu ALU_SLTU A (SOff nb 0)) (SLit 1))) = x - (if a <? b then 0 else 1).
Proof.
intros E nx A nb x a b Hx HA Hb Rx Rx1 Rb.
assert (Ht : 0 <= (if a <? b then 0 else 1) <= 1) by (destruct (a <? b); lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E nx x Hx), HA, (U_atom E nb b Hb), U_SLit by lia. change (zcanon 1) with 1.
destruct (a <? b); [change (zcanon 1) with 1; change (Z.lxor 1 1) with 0; change (zcanon 0) with 0 | change (zcanon 0) with 0; change (Z.lxor 0 1) with 1; change (zcanon 1) with 1];
apply zcanon_id; rewrite M64_val; lia.
Qed.
Lemma U_add_atoms : forall E n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
U E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = a + b.
Proof. intros E n1 n2 a b H1 H2 Ha Hb Hab. unfold U. rewrite (denot_add_atoms E n1 n2 a b H1 H2 Ha Hb Hab). apply unsigned_lit_small. lia. Qed.
Lemma U_and_ffff_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 16 ->
U E (SAlu ALU_AND (SOff n c) (SLit 65535)) = x + c.
Proof.
intros E n x c Hn Rx Rc. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E n x c Hn), U_SLit by lia.
change (zcanon 65535) with (Z.ones 16). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
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
Section e.
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
Section f.
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
Let BDp := BD W memc fimg bimg.
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
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia|]); destruct Hr.
Ltac awrRO := repeat (first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn; lia|] ]); try (match goal with |- ?g => idtac "AWR-LEFT" g end).
Definition F4_KEPT : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition F4_KEPTX : list (bv 5) := [1; 2; 3; 4; 7; 8; 9; 12; 18; 19; 20; 21; 22; 23; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Ltac slot160 HS idx E9 E28 hv V :=
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth idx (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
let HR1 := fresh "HR1" in
pose proof (st_ok_pi_region_nth Ex ssx msx idx r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SOff 40 0) hv HR1
ltac:(evE; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; evE; rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V end; clear HR1 end;
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V.
Definition f4_regs := sr_set sr_atoms 14%bv (SLit 65535).
Definition f4_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 176 184 176 176 [YP09.mkChunk 176 (CVal 8 (SOff 38 0))];
YP09.mkRegion (Some 9%nat) 224 232 224 224 [YP09.mkChunk 224 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 33%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))];
YP09.mkRegion (Some 35%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))];
YP09.mkRegion (Some 9%nat) 144 152 144 144 [YP09.mkChunk 144 (CVal 8 (SOff 37 0))];
YP09.mkRegion (Some 9%nat) 200 208 200 200 [YP09.mkChunk 200 (CVal 8 (SOff 39 0))];
YP09.mkRegion (Some 9%nat) 160 168 160 160 [YP09.mkChunk 160 (CVal 8 (SOff 40 0))] ].
Definition f4_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (15%nat, mkAF 0 65534 0); (13%nat, mkAF 1 65534 0); (23%nat, mkAF 0 65534 0);
(26%nat, mkAF 1 65535 0); (39%nat, mkAF 1 65535 0); (27%nat, mkAF 0 65534 0); (12%nat, mkAF 0 4294967295 0); (10%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0);
(32%nat, HPTR 0); (25%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, HPTR 0); (36%nat, mkAF 0 255 0);
(37%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_f4 : sstate := mkSS 0x27c0 f4_regs f4_mem None f4_facts.
Definition f4_postX (c0 top bot left : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' right,
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x1f8c)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
wkeptF B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
c0 <= right < Wd /\
getr regs' 26 = Z_to_bv 64 (right - left + 1) /\ val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 (bot + 1 - top) /\ getr regs' 27 = Z_to_bv 64 top /\ getr regs' 23 = Z_to_bv 64 left /\
getr regs' 10 = Z_to_bv 64 a184 /\ getr regs' 11 = Z_to_bv 64 a176 /\ getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4 /\
(exists y', top <= y' <= bot /\ BDp (y' * Wd + right)) /\ (forall i x0, top <= i <= bot -> right < x0 < Wd -> ~ BDp (i * Wd + x0)).
Definition f4_stmtX (m : nat) : Prop :=
forall (x y c0 top bot left : Z) (regsE : bvmap 5 word) memE mdE,
(x - c0) * Hd + (bot - y) < Z.of_nat m -> c0 < x < Wd -> 0 <= left <= c0 -> 0 <= top -> top <= y <= bot -> bot < Hd -> BDp (top * Wd + c0) ->
(forall i x0, top <= i <= bot -> x0 < Wd -> (x < x0 \/ (x0 = x /\ i <= y)) -> ~ BDp (i * Wd + x0)) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k -> wkeptF B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 6 = Z_to_bv 64 SB -> getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp -> getr regsE 14 = Z_to_bv 64 65535 ->
getr regsE 15 = Z_to_bv 64 y -> getr regsE 10 = Z_to_bv 64 (y * Wd) -> getr regsE 13 = Z_to_bv 64 x -> getr regsE 12 = Z_to_bv 64 (top * Wd) ->
getr regsE 26 = Z_to_bv 64 (bot + 1) -> getr regsE 27 = Z_to_bv 64 top -> getr regsE 25 = Z_to_bv 64 bimg ->
getr regsE 23 = Z_to_bv 64 left -> val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 (bot + 1 - top) ->
getr regsE 18 = Z_to_bv 64 sv2 -> getr regsE 20 = Z_to_bv 64 sv4 ->
SRr SEGS W (mkCfg (mkst regsE (Z_to_bv 64 (BASE + 0x27c0)) memE (seg_rom SEGS)) mdE) (f4_postX c0 top bot left).
Lemma fl_f4l_stepX : forall m, f4_stmtX m -> f4_stmtX (Datatypes.S m).
Proof.
intros m IH. unfold f4_stmtX.
intros x y c0 top bot left regsE memE mdE Hm Hx Hl Ht0 Hy Hbt HBDw XACC HJE WK HKE E6 E21r E22r E14r E15r E10r E13r E12r E26r E29r E25r E23r V160r E18s E20s.
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
set (bC := bval (aview SEGS (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
remember (Eimg (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15. pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite E10r in E10.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite E13r in E13. pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E29. rewrite E29r in E29. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (fimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 a176) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 a184) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 7)).
assert (E28 : ew E 40 = Z_to_bv 64 (bot + 1 - top)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsE _ 8)).
pose proof E39 as E7.
assert (HS : st_ok_pi SEGS VAL E ss_f4 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 0x27c0)) memE (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f4, f4_regs. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x27c0) _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | rewrite E14r; reflexivity].
- reflexivity.
- unfold f4_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216E]|]. apply Forall_nil.
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E35, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200E]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ (bot + 1 - top)); [cbn [sv_denot]; rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160r]|]. apply Forall_nil.
- unfold f4_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E9, E33, E35, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f4_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E15, E13, E23, E26, E7, E29, E12, E10, E28, E32, E25, E33, E34, E35, E36, E37, E38, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memE).
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
1: { unfold f4_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memE _ mdE sp1 HAR HFr1 HG1 ltac:(unfold ss_f4, f4_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresE)) as WK1.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HGEU end;
rewrite branch_geu_U in HGEU; rewrite (U_and_ffff_off _ 15 y 1) in HGEU by (first [evE; exact E15 | lia]); rewrite (U_atom _ 26 (bot + 1)) in HGEU by (first [evE; exact E26 | lia]);
[apply (proj1 (negb_true_iff _)) in HGEU; apply Z.ltb_ge in HGEU | apply (proj1 (negb_false_iff _)) in HGEU; apply Z.ltb_lt in HGEU];
reshok_bx HS 6%nat; pose proof (proj1 HJE) as HAR2.
-
assert (Ex' : x' = x - 1) by (subst x'; destruct (Z.ltb_spec y bot); lia). assert (Ey' : y' = top) by (subst y'; destruct (Z.ltb_spec y bot); lia).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2804.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
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
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2818.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (fimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (fimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR3 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
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
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 35 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 35 (bimg + p) cc ltac:(evE; exact E35)) by lia | rewrite (U_atom Ex 35 (bimg + p) ltac:(evE; exact E35)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR4 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HEQ end;
rewrite branch_eq_U in HEQ; rewrite (U_atom _ 34 bC) in HEQ by (first [evE; exact E34 | lia]); rewrite (U_atom _ 36 bB) in HEQ by (first [evE; exact E36 | lia]);
[apply Z.eqb_eq in HEQ | apply Z.eqb_neq in HEQ]; reshok_bx HS 6%nat; pose proof (proj1 HJE) as HAR5.
+
assert (Hxc' : c0 < x').
{ destruct (Z_lt_le_dec c0 x') as [Hl'|Hge]; [exact Hl'|]. exfalso. apply HBDw. unfold BD.
replace (top * Wd + c0) with p by (subst p; rewrite Ey'; f_equal; clear - Hge Hxy'; lia). fold bC in SbC. rewrite SbC, SbB. f_equal. exact HEQ. }
assert (HnBD : ~ BDp p) by (intros HD; apply HD; rewrite SbC, SbB; fold bC bB; rewrite HEQ; reflexivity).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x27c0.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
prreg HS (15%bv : bv 5) Rg15. prreg HS (14%bv : bv 5) Rg14. prreg HS (6%bv : bv 5) Rg6.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SOff 12 0) = y' * Wd) by (rewrite (U_atom Ev 12 (top * Wd) ltac:(evE; exact E12)) by (clear - HtW HW1 HN HNb RW; lia); rewrite Ey'; reflexivity);
assert (HIDX : U Ev (SAlu ALU_ADD (SOff 12 0) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
rreg_by HS (13%bv : bv 5) (Z_to_bv 64 x') (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HXQ)) Rg13;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (y' * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HA6)) Rg10 end.
pmkst HS.
eapply (IH x' y' c0 top bot left); [ rewrite Ex', Ey'; clear - Hm Hx Hy Ht0 Hbt Hxc' Ex'; nia | lia | exact Hl | exact Ht0 | lia | exact Hbt | exact HBDw
|   intros i' x0 Hi' Hx0' Hd'; destruct (Z.eq_dec x0 x') as [Ex0 | Hnx]; [destruct (Z.eq_dec i' y') as [Ei | Hni]; [rewrite Ex0, Ei; exact HnBD |] |];
(apply XACC; [exact Hi' | exact Hx0' | first [clear - Hd' Hi' Hy HGEU Ex' Ey' Ex0 Hni; lia | clear - Hd' Hi' Hy HGEU Ex' Ey' Hnx; lia]])
| exact HJE | exact WK5
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
assert (HBD : BDp p) by (intros HD; apply HEQ; rewrite SbC, SbB in HD; fold bC bB in HD; injection HD as HD; exact HD).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1f8c.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPTX HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
prreg HS (6%bv : bv 5) Rg6. prreg HS (10%bv : bv 5) Rg10. prreg HS (11%bv : bv 5) Rg11.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (x' - left + 1))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width2 Ev _ 23 x' left HXQ ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) Rg14 end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, x' end.
split; [reflexivity|]. split; [exact HJE|]. split; [exact WK5|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F4_KEPTX In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite Rg6; evE; exact F6|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [exact (proj1 Hxy')|]. split; [exact Rg14|].
split; [exact V160x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite Rg10; evE; exact E38|]. split; [rewrite Rg11; evE; exact E37|].
split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s|].
split; [exists y'; split; [exact (proj2 Hxy') | exact HBD] | intros i' x0 Hi' Hx0; apply XACC; [exact Hi' | clear - Hx0; lia | clear - Hx0 Hi' Hy HGEU Ex'; lia]].
-
assert (Ex' : x' = x) by (subst x'; destruct (Z.ltb_spec y bot); lia). assert (Ey' : y' = y + 1) by (subst y'; destruct (Z.ltb_spec y bot); lia).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2804.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
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
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x2818.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (fimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (fimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR3 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
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
hei_havoc HS; paj_run_tok RUN HS HJE SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 35 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 35 (bimg + p) cc ltac:(evE; exact E35)) by lia | rewrite (U_atom Ex 35 (bimg + p) ltac:(evE; exact E35)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR4 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HEQ end;
rewrite branch_eq_U in HEQ; rewrite (U_atom _ 34 bC) in HEQ by (first [evE; exact E34 | lia]); rewrite (U_atom _ 36 bB) in HEQ by (first [evE; exact E36 | lia]);
[apply Z.eqb_eq in HEQ | apply Z.eqb_neq in HEQ]; reshok_bx HS 6%nat; pose proof (proj1 HJE) as HAR5.
+
assert (Hxc' : c0 < x').
{ destruct (Z_lt_le_dec c0 x') as [Hl'|Hge]; [exact Hl'|]. exfalso. apply HBDw. unfold BD.
replace (top * Wd + c0) with p by (subst p; exfalso; clear - Hge Ex' Hx; lia). fold bC in SbC. rewrite SbC, SbB. f_equal. exact HEQ. }
assert (HnBD : ~ BDp p) by (intros HD; apply HD; rewrite SbC, SbB; fold bC bB; rewrite HEQ; reflexivity).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x27c0.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPT HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
prreg HS (15%bv : bv 5) Rg15. prreg HS (14%bv : bv 5) Rg14. prreg HS (6%bv : bv 5) Rg6.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
assert (HA6 : U Ev (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) = y' * Wd) by (rewrite (U_add_atoms Ev 10 39 (y * Wd) Wd ltac:(evE; exact E10) ltac:(evE; exact E7)) by (clear - HtW HN HNb RW; lia); rewrite Ey'; clear; lia);
assert (HIDX : U Ev (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) (SOff 39 0)) (SAlu ALU_AND (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) (SLit 65535))) = p) by (rewrite U_add_and16 by (rewrite ?HXQ, ?HA6; clear - Hxy' RW HyW HW1 HN HNb; lia); rewrite HA6, HXQ; subst p; reflexivity);
rreg_by HS (13%bv : bv 5) (Z_to_bv 64 x') (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HXQ)) Rg13;
rreg_by HS (10%bv : bv 5) (Z_to_bv 64 (y' * Wd)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) HA6)) Rg10 end.
pmkst HS.
eapply (IH x' y' c0 top bot left); [ rewrite Ex', Ey'; clear - Hm Hx Hy Ht0 Hbt Hxc' Ex'; nia | lia | exact Hl | exact Ht0 | lia | exact Hbt | exact HBDw
|   intros i' x0 Hi' Hx0' Hd'; destruct (Z.eq_dec x0 x') as [Ex0 | Hnx]; [destruct (Z.eq_dec i' y') as [Ei | Hni]; [rewrite Ex0, Ei; exact HnBD |] |];
(apply XACC; [exact Hi' | exact Hx0' | first [clear - Hd' Hi' Hy HGEU Ex' Ey' Ex0 Hni; lia | clear - Hd' Hi' Hy HGEU Ex' Ey' Hnx; lia]])
| exact HJE | exact WK5
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
assert (HBD : BDp p) by (intros HD; apply HEQ; rewrite SbC, SbB in HD; fold bC bB in HD; injection HD as HD; exact HD).
hei_havoc HS; paj_run_to_tok RUNTO HS HJE SHOK FLBspan 0x1f8c.
1: { awrRO. }
rename HFr into HFr5. rename HG into HG5. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK4 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsE _ F4_KEPTX HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
prreg HS (6%bv : bv 5) Rg6. prreg HS (10%bv : bv 5) Rg10. prreg HS (11%bv : bv 5) Rg11.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (HXQ : U Ev (SAlu ALU_SUB (SOff 13 0) (SAlu ALU_XOR (SAlu ALU_SLTU (SAlu ALU_AND (SOff 15 1) (SLit 65535)) (SOff 26 0)) (SLit 1))) = x')
by (rewrite (U_sub_not_ltu2 Ev 13 _ 26 x (y + 1) (bot + 1) ltac:(evE; exact E13) ltac:(apply (U_and_ffff_off Ev 15 y 1); [evE; exact E15 | lia | lia]) ltac:(evE; exact E26));
[rewrite Ex'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | rewrite Ex' in Hxy'; destruct (Z.ltb_spec (y + 1) (bot + 1)); lia | lia | lia]);
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (x' - left + 1))
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width2 Ev _ 23 x' left HXQ ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) Rg14 end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, x' end.
split; [reflexivity|]. split; [exact HJE|]. split; [exact WK5|].
split; [intros r Hr; transitivity (getr regsE r); [apply HKr; cbv [WKEPT5 F4_KEPTX In] in Hr |- *; tauto | apply HKE; exact Hr]|].
split; [rewrite Rg6; evE; exact F6|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [exact (proj1 Hxy')|]. split; [exact Rg14|].
split; [exact V160x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite Rg10; evE; exact E38|]. split; [rewrite Rg11; evE; exact E37|].
split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s|].
split; [exists y'; split; [exact (proj2 Hxy') | exact HBD] | intros i' x0 Hi' Hx0; apply XACC; [exact Hi' | clear - Hx0; lia | clear - Hx0 Hi' Hy HGEU Ex'; lia]].
Qed.
Lemma fl_f4lX : forall m, f4_stmtX m.
Proof. induction m as [|m IH]; [unfold f4_stmtX; intros; exfalso; nia | exact (fl_f4l_stepX m IH)]. Qed.
Definition f4s_mem : smem := f4_mem.
Definition f4s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (23%nat, mkAF 0 65534 0); (12%nat, mkAF 0 4294967295 0); (40%nat, mkAF 1 65535 0);
(27%nat, mkAF 0 65534 0); (26%nat, mkAF 0 65534 0); (13%nat, mkAF 1 65535 0); (39%nat, mkAF 1 65535 0);
(32%nat, HPTR 0); (25%nat, HPTR 0); (33%nat, HPTR 0); (34%nat, mkAF 0 255 0); (35%nat, HPTR 0); (36%nat, mkAF 0 255 0);
(37%nat, mkAF 0 18446744073709551615 0); (38%nat, mkAF 0 18446744073709551615 0) ] [] [].
Definition ss_f4s : sstate := mkSS 0x2750 sr_atoms f4s_mem None f4s_facts.
Lemma fl_f4X : forall (c0 top bot left : Z) (regsF : bvmap 5 word) memF mdF,
0 <= left <= c0 -> c0 < Wd -> 0 <= top <= bot -> bot < Hd -> BDp (top * Wd + c0) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkeptF B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 6 = Z_to_bv 64 SB -> getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp ->
getr regsF 23 = Z_to_bv 64 left -> getr regsF 12 = Z_to_bv 64 (top * Wd) -> val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 160) 8 (bot + 1 - top) -> getr regsF 27 = Z_to_bv 64 top ->
getr regsF 26 = Z_to_bv 64 top -> getr regsF 13 = Z_to_bv 64 Wd -> getr regsF 25 = Z_to_bv 64 bimg -> getr regsF 18 = Z_to_bv 64 sv2 -> getr regsF 20 = Z_to_bv 64 sv4 ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x2750)) memF (seg_rom SEGS)) mdF) (f4_postX c0 top bot left).
Proof.
intros c0 top bot left regsF memF mdF Hl Hc0 Htb Hbt HBDw HJF WK HKF E6 E21r E22r E23r E12r V160r E29r E26r E7r E25r E18s E20s.
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
set (bC := bval (aview SEGS (w_H W) memc) (fimg + p)) in *. set (bB := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
remember (Eimg (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsF [Z_to_bv 64 fimg; Z_to_bv 64 (fimg + p); Z_to_bv 64 bC; Z_to_bv 64 (bimg + p); Z_to_bv 64 bB; Z_to_bv 64 a176; Z_to_bv 64 a184; Z_to_bv 64 Wd; Z_to_bv 64 (bot + 1 - top)]) E) by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsF r) by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKF 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 6%nat 6%bv eq_refl) as F6. rewrite E6 in F6.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite E23r in E23. pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite E12r in E12.
pose proof (EE 27%nat 27%bv eq_refl) as E29. rewrite E29r in E29.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 13%nat 13%bv eq_refl) as E7. rewrite E7r in E7.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite E21r in E21. pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite E22r in E22.
assert (E32 : ew E 32 = Z_to_bv 64 fimg) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (fimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bC) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (bimg + p)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 bB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 a176) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 a184) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 Wd) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 7)).
assert (E28 : ew E 40 = Z_to_bv 64 (bot + 1 - top)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsF _ 8)).
assert (HS : st_ok_pi SEGS VAL E ss_f4s (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 0x2750)) memF (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_f4s. unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts].
apply (rn_st_ok_any E (BASE + 0x2750) _ regsF _ _ (mrestrict (w_H W) memF)).
- subst E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- unfold f4s_mem, f4_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 176 8 _ a184); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V184F]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 224 8 _ fimg); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V216F]|]. apply Forall_nil.
+ rewrite E33, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (fimg + p) 0 1 _ bC); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbC].
+ rewrite E35, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_nil]. apply (chunk_ok_val SEGS E _ (bimg + p) 0 1 _ bB); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact VbB].
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 144 8 _ a176); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176F]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 200 8 _ Wd); [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V200F]|]. apply Forall_nil.
+ rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val SEGS E _ sp1 160 8 _ (bot + 1 - top)); [cbn [sv_denot]; rewrite E28, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160r]|]. apply Forall_nil.
- unfold f4s_mem, f4_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite E9, E33, E35, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [f4s_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F6, E23, E12, E28, E29, E26, E7, E39, E32, E25, E33, E34, E35, E36, E37, E38, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT3" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 6 0) E (mrestrict (w_H W) memF).
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x2770.
1: { unfold f4s_mem, f4_mem. awrRO. }
rename HFr into HFr1. rename HG into HG1. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK (wkeptF_of_run B LAWS E _ lyc Sc W memF _ mdF sp1 HAR HFr1 HG1 ltac:(unfold ss_f4s, f4s_mem, f4_mem; intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) HSpresF)) as WK1.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
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
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x2784.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 33 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 33 (fimg + p) cc ltac:(evE; exact E33)) by lia | rewrite (U_atom Ex 33 (fimg + p) ltac:(evE; exact E33)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len fimg Nb HAR2 Hfi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr2. rename HG into HG2. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK1 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR2 HFr2 HG2 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK1 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
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
hei_havoc HS; paj_run_tok RUN HS HJF SHOK FLBspan.
all: try (lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 35 ?cc)) ?len =>
first [rewrite (U_atom_off Ex 35 (bimg + p) cc ltac:(evE; exact E35)) by lia | rewrite (U_atom Ex 35 (bimg + p) ltac:(evE; exact E35)) by lia];
eapply (obl_of_block SEGS _ LAWS _ _ _ _ _ Ex (SOff 6 0) _ len bimg Nb HAR3 Hbi); [rewrite (U_atom Ex 6 SB ltac:(evE; exact F6)); [reflexivity | unfold SB; lia] | lia | lia] end).
all: match goal with |- range_addressable _ _ _ _ => match goal with |- ?g => idtac "OBL-LEFT" g end | _ => idtac end.
1: { awrRO. }
rename HFr into HFr3. rename HG into HG3. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK2 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR3 HFr3 HG3 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK2 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK3.
hei_havoc HS; psrr_branch_tok RUN BR HS SHOK FLBspan; lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into HNE end;
rewrite branch_ne_U in HNE; rewrite (U_atom _ 34 bC) in HNE by (first [evE; exact E34 | lia]); rewrite (U_atom _ 36 bB) in HNE by (first [evE; exact E36 | lia]);
[apply (proj1 (negb_true_iff _)) in HNE; apply Z.eqb_neq in HNE | apply (proj1 (negb_false_iff _)) in HNE; apply Z.eqb_eq in HNE];
reshok_bx HS 6%nat; pose proof (proj1 HJF) as HAR4.
-
assert (HBD0 : BDp p) by (intros HD; apply HNE; rewrite SbC, SbB in HD; fold bC bB in HD; injection HD as HD; exact HD).
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x1f8c.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (6%bv :: 21%bv :: 22%bv :: 23%bv :: 27%bv :: 18%bv :: 20%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (10%bv : bv 5) Rg10. prreg HS (11%bv : bv 5) Rg11.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (Wd - left)) (eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_width0 Ev 13 23 Wd left ltac:(evE; exact E7) ltac:(evE; exact E23) ltac:(lia) ltac:(lia)))) Rg14 end.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, (Wd - 1) end.
split; [reflexivity|]. split; [exact HJF|]. split; [exact WK4|].
split; [intros r Hr; transitivity (getr regsF r); [apply HKr; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKF; exact Hr]|].
split; [rewrite (HKr 6%bv ltac:(cbv; tauto)); exact E6|]. split; [rewrite (HKr 21%bv ltac:(cbv; tauto)); exact E21r|]. split; [rewrite (HKr 22%bv ltac:(cbv; tauto)); exact E22r|].
split; [clear - Hc0 RW; lia|]. split; [rewrite Rg14; f_equal; lia|].
split; [exact V160x|]. split; [rewrite (HKr 27%bv ltac:(cbv; tauto)); exact E29r|]. split; [rewrite (HKr 23%bv ltac:(cbv; tauto)); exact E23r|].
split; [rewrite Rg10; evE; exact E38|]. split; [rewrite Rg11; evE; exact E37|].
split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact E18s|]. split; [rewrite (HKr 20%bv ltac:(cbv; tauto)); exact E20s|].
split; [exists top; split; [clear - Htb; lia | exact HBD0] | intros i' x0 Hi' Hx0; exfalso; clear - Hx0; lia].
-
hei_havoc HS; paj_run_to_tok RUNTO HS HJF SHOK FLBspan 0x27c0.
1: { awrRO. }
rename HFr into HFr4. rename HG into HG4. clear HF.
pose proof (wkeptF_trans B _ _ _ _ _ _ _ WK3 (wkeptF_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR4 HFr4 HG4 ltac:(intros a Ha; exfalso; revert a Ha; noW) ltac:(lia) ltac:(lia) ltac:(pose proof WK3 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK4.
assert (Hcw : c0 < Wd - 1).
{ destruct (Z_lt_le_dec c0 (Wd - 1)) as [Hlt|Hge]; [exact Hlt|]. exfalso. apply HBDw. unfold BD.
replace (top * Wd + c0) with p by (subst p; clear - Hge Hc0; lia). fold bC in SbC. rewrite SbC, SbB. f_equal. exact HNE. }
assert (HnBD0 : ~ BDp p) by (intros HD; apply HD; rewrite SbC, SbB; fold bC bB; rewrite HNE; reflexivity).
pose proof (regs_kept_of_st_ok_pi _ _ _ regsF _ (6%bv :: 21%bv :: 22%bv :: 23%bv :: 27%bv :: 18%bv :: 20%bv :: WKEPT5) HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr. cbn [ms_regs restrict] in HKr.
prreg HS (14%bv : bv 5) Rg14. prreg HS (15%bv : bv 5) Rg15. prreg HS (10%bv : bv 5) Rg10. prreg HS (13%bv : bv 5) Rg13. prreg HS (12%bv : bv 5) Rg12. prreg HS (25%bv : bv 5) Rg25.
slot160 HS 6%nat E9 E28 (bot + 1 - top) V160x.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (top + (bot + 1 - top))) (denot_add_atoms Ev 26 40 top (bot + 1 - top) ltac:(evE; exact E26) ltac:(evE; exact E28) ltac:(lia) ltac:(lia) ltac:(lia)) Rg26 end.
pmkst HS.
assert (HM0 : (Wd - 1 - c0) * Hd <= (Wd - 1) * Hd) by (apply Z.mul_le_mono_nonneg_r; clear - RH Hc0 Hl; lia).
assert (HM1 : (Wd - 1 - c0) * Hd + (bot - top) < Wd * Hd + Hd) by (clear - HM0 Htb Hbt RH RW; lia).
eapply (fl_f4lX (Z.to_nat (Wd * Hd + Hd)) (Wd - 1) top c0 top bot left);
[ rewrite Z2Nat.id by (clear - RW RH; nia); exact HM1 | clear - Hcw RW; lia | exact Hl | lia | lia | exact Hbt | exact HBDw
| intros i' x0 Hi' Hx0 Hd'; destruct Hd' as [Hlt | [Ex0 Hle]]; [exfalso; clear - Hlt Hx0; lia|];
assert (Ei : i' = top) by (clear - Hi' Hle; lia); rewrite Ex0, Ei; exact HnBD0
| exact HJF | exact WK4
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
End f.
End e.
End d.
End c.
