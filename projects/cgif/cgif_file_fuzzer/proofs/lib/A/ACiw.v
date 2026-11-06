(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0d YP0c YI0w YI0x YC4a.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC44.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACj2 ACjm.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YC20.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje ACjj ACjk.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Ltac noW :=
lazymatch goal with
| |- forall _ : Z, not (in_wrange _ _ _) => unfold not; noW
| |- forall _ : Z, in_wrange _ _ _ -> _ =>
    let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
    intros a [r [Hin Hr]]; vm_compute in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [r_wlo r_whi] in Hr; lia | ]); destruct Hin
| Hs : st_ok_pi _ _ _ ?ss (restrict _ ?ms) |- getr (ms_regs ?ms) ?r = _ =>
    rewrite (st_ok_pi_restrict_reg _ _ _ _ r Hs);
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
end.
Ltac noWk :=
lazymatch goal with
| Hk : wkept _ _ _ _ _ ?m0 ?m1 |- val_mem _ (mrestrict _ ?m1) (_ + ?o) 8 _ =>
    eapply (val_mem_wkept _ _ _ _ _ m0 m1 o); [exact Hk | lia | lia | lia | lia | lia | intros ? ?; unfold wscr; lia | eassumption]
end.
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
[ {| r_base := Some 9%nat; r_lo := 0; r_hi := 256; r_wlo := 0; r_whi := 0;
     r_chunks := [ {| c_off := 96; YP09.c_val := CVal 8 (SOff 42 0) |}; {| c_off := 104; YP09.c_val := CVal 8 (SOff 43 0) |};
                   {| c_off := 144; YP09.c_val := CVal 8 (SOff 40 0) |}; {| c_off := 160; YP09.c_val := CVal 8 (SOff 41 0) |};
                   {| c_off := 176; YP09.c_val := CVal 8 (SOff 39 0) |}; {| c_off := 224; YP09.c_val := CVal 8 (SOff 34 0) |};
                   {| c_off := 240; YP09.c_val := CVal 8 (SOff 38 0) |}; {| c_off := 248; YP09.c_val := CVal 8 (SOff 33 0) |} ] |};
  reg8 32 35 false; reg8 36 37 false ].
Definition s4_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (38%nat, mkAF SB SB 0); (20%nat, mkAF 0 65534 0); (18%nat, mkAF 0 65534 0); (27%nat, mkAF 0 65534 0);
(26%nat, mkAF 1 65535 0); (25%nat, mkAF 1 65535 0); (24%nat, HPTR 0); (21%nat, HPTR 4); (22%nat, HPTR 3); (23%nat, mkAF 0 65534 0);
(32%nat, HPTR 0); (33%nat, HPTR 3); (34%nat, HPTR 0); (35%nat, mkAF 0 255 0); (36%nat, HPTR 0); (37%nat, mkAF 0 255 0);
(39%nat, mkAF 0 18446744073709551615 0); (40%nat, mkAF 0 18446744073709551615 0); (41%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s4 : sstate := mkSS 7880 s4_regs s4_mem None s4_facts.
Definition s4_postX (c0 top bot left : Z) : world SEGS -> config -> Prop :=
fun W' c' => W' = W /\ exists (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (right : Z),
  c' = {| cfg_ms := mkst regs' (Z_to_bv 64 (BASE + 8076)) mem' (seg_rom SEGS); cfg_model := md' |} /\
  ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mem' md' k /\
  wkept B lyc Sc W sp1 memc mem' /\
  (forall r : Prelude.reg, In r WKEPT5 -> getr regs' r = getr regs r) /\
  getr regs' 6 = Z_to_bv 64 SB /\ getr regs' 21 = Z_to_bv 64 g /\ getr regs' 22 = Z_to_bv 64 cfp /\
  c0 <= right < Wd /\
  getr regs' 26 = Z_to_bv 64 (right - left + 1) /\
  val_mem SEGS (mrestrict (w_H W) mem') (sp1 + 160) 8 (bot + 1 - top) /\
  getr regs' 27 = Z_to_bv 64 top /\ getr regs' 23 = Z_to_bv 64 left /\
  getr regs' 10 = Z_to_bv 64 a184 /\ getr regs' 11 = Z_to_bv 64 a176 /\
  getr regs' 18 = Z_to_bv 64 sv2 /\ getr regs' 20 = Z_to_bv 64 sv4 /\
  (exists y, top <= y <= bot /\ PDp (y * Wd + right)) /\
  (forall x y, top <= y <= bot -> right < x < Wd -> ~ PDp (y * Wd + x)).
Definition s4_stmtX (m : nat) : Prop :=
forall (x y c0 top bot left : Z) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model),
(x - c0) * (bot + 1 - top) + (bot - y) < Z.of_nat m ->
0 <= left <= c0 -> c0 <= x < Wd -> 0 <= top <= y -> y <= bot -> bot < Hd ->
PDp (top * Wd + c0) ->
(forall x' y', x < x' < Wd -> top <= y' <= bot -> ~ PDp (y' * Wd + x')) ->
(forall y', top <= y' < y -> ~ PDp (y' * Wd + x)) ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k ->
wkept B lyc Sc W sp1 memc memE ->
(forall r : Prelude.reg, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 21 = Z_to_bv 64 g -> getr regsE 22 = Z_to_bv 64 cfp -> getr regsE 19 = Z_to_bv 64 65535 ->
getr regsE 20 = Z_to_bv 64 y -> getr regsE 18 = Z_to_bv 64 x -> getr regsE 27 = Z_to_bv 64 top ->
getr regsE 26 = Z_to_bv 64 (bot + 1) -> getr regsE 25 = Z_to_bv 64 Wd -> getr regsE 24 = Z_to_bv 64 bimg ->
getr regsE 23 = Z_to_bv 64 left -> getr regsE 14 = Z_to_bv 64 SB ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg ->
val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 (bot + 1 - top) ->
SRr SEGS W {| cfg_ms := mkst regsE (Z_to_bv 64 (BASE + 7880)) memE (seg_rom SEGS); cfg_model := mdE |} (s4_postX c0 top bot left).
Lemma fl_s4l_stepX : forall m, s4_stmtX m -> s4_stmtX (Datatypes.S m).
Proof.
intros m Hind. unfold s4_stmtX.
intros x y c0 top bot left regsE memE mdE Lmeas Lleft Lx Lty Lyb Lbh Pc0 Nright Nabove
  AJ WK KEEP5 G21 G22 G19 G20 G18 G27 G26 G25 G24 G23 G14 M216 M160.
wctx_names. wprelude AJ.
set (p := y * Wd + x).
assert (Rp : 0 <= p < Nb) by (subst p; nia).
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE fimg Nb p WK HAR Hfi Rp) as [Vfp Rfp].
destruct (wimg_byte B LAWS lyc Sc W sp1 memc memE mdE bimg Nb p WK HAR Hbi Rp) as [Vbp Rbp].
set (bf := bval (aview SEGS (w_H W) memc) (fimg + p)) in *.
set (bb := bval (aview SEGS (w_H W) memc) (bimg + p)) in *.
pose proof (al_blocks SEGS B LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as (Afi16 & Afi4 & Afiu & _).
pose proof (al_blocks SEGS B LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as (Abi16 & Abi4 & Abiu & _).
pose proof (al_blocks SEGS B LAWS lyc Sc W memE mdE bfp FRAME_SIZE HAR Hbf) as (Abf16 & Abf4 & Abfu & _).
pose proof (al_blocks SEGS B LAWS lyc Sc W memE mdE g CGIF_SIZE HAR Hg) as (Ag16 & Ag4 & Agu & _).
pose proof (al_blocks SEGS B LAWS lyc Sc W memE mdE cfp FRAME_SIZE HAR Hcf) as (Acf16 & Acf4 & Acfu & _).
pose proof (req_size_pos Nb ltac:(lia)) as RqN.
pose proof (req_size_pos FRAME_SIZE ltac:(cbv; discriminate)) as RqF.
pose proof (req_size_pos CGIF_SIZE ltac:(cbv; discriminate)) as RqG.
assert (Lsp : alloc_ceiling + 17000 <= sp1 /\ sp1 + 384 <= 2 ^ 47) by lia.
assert (Sm96 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 96) 8 sv2) by noWk.
assert (Sm104 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 104) 8 sv4) by noWk.
assert (Sm144 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 144) 8 a176) by noWk.
assert (Sm176 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 176) 8 a184) by noWk.
assert (Sm224 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 224) 8 fimg) by noWk.
assert (Sm240 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 240) 8 SB) by noWk.
assert (Sm248 : val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 248) 8 bfp) by noWk.
pose (E := Eimg (Ereg regsE [Z_to_bv 64 (fimg + p); Z_to_bv 64 bfp; Z_to_bv 64 fimg; Z_to_bv 64 bf;
  Z_to_bv 64 (bimg + p); Z_to_bv 64 bb; Z_to_bv 64 SB; Z_to_bv 64 a184; Z_to_bv 64 a176;
  Z_to_bv 64 (bot + 1 - top); Z_to_bv 64 sv2; Z_to_bv 64 sv4])).
assert (Rg9 : getr regsE 9 = Z_to_bv 64 sp1) by (rewrite (KEEP5 9%bv) by (cbv; tauto); exact H9).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite <- Rg9; reflexivity).
assert (E14 : ew E 14 = Z_to_bv 64 SB) by (rewrite <- G14; reflexivity).
assert (E18 : ew E 18 = Z_to_bv 64 x) by (rewrite <- G18; reflexivity).
assert (E19 : ew E 19 = Z_to_bv 64 65535) by (rewrite <- G19; reflexivity).
assert (E20 : ew E 20 = Z_to_bv 64 y) by (rewrite <- G20; reflexivity).
assert (E21 : ew E 21 = Z_to_bv 64 g) by (rewrite <- G21; reflexivity).
assert (E22 : ew E 22 = Z_to_bv 64 cfp) by (rewrite <- G22; reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 left) by (rewrite <- G23; reflexivity).
assert (E24 : ew E 24 = Z_to_bv 64 bimg) by (rewrite <- G24; reflexivity).
assert (E25 : ew E 25 = Z_to_bv 64 Wd) by (rewrite <- G25; reflexivity).
assert (E26 : ew E 26 = Z_to_bv 64 (bot + 1)) by (rewrite <- G26; reflexivity).
assert (E27 : ew E 27 = Z_to_bv 64 top) by (rewrite <- G27; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (fimg + p)) by reflexivity.
assert (E33 : ew E 33 = Z_to_bv 64 bfp) by reflexivity.
assert (E34 : ew E 34 = Z_to_bv 64 fimg) by reflexivity.
assert (E35 : ew E 35 = Z_to_bv 64 bf) by reflexivity.
assert (E36 : ew E 36 = Z_to_bv 64 (bimg + p)) by reflexivity.
assert (E37 : ew E 37 = Z_to_bv 64 bb) by reflexivity.
assert (E38 : ew E 38 = Z_to_bv 64 SB) by reflexivity.
assert (E39 : ew E 39 = Z_to_bv 64 a184) by reflexivity.
assert (E40 : ew E 40 = Z_to_bv 64 a176) by reflexivity.
assert (E41 : ew E 41 = Z_to_bv 64 (bot + 1 - top)) by reflexivity.
assert (E42 : ew E 42 = Z_to_bv 64 sv2) by reflexivity.
assert (E43 : ew E 43 = Z_to_bv 64 sv4) by reflexivity.
assert (SBv : SB = 2147450880) by reflexivity.
assert (ST0 : st_ok_pi SEGS VAL E ss_s4 (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 7880)) memE (seg_rom SEGS)))).
{ unfold st_ok_pi, abs_ss, ss_s4. cbn [setpc ss_pc ss_regs ss_mem ss_facts ss_resv ss_fregs].
  change (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 7880)) memE (seg_rom SEGS)))
    with (mkst regsE (Z_to_bv 64 (BASE + 7880)) (mrestrict (w_H W) memE) (seg_rom SEGS)).
  apply rn_st_ok_any.
  - unfold s4_regs. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | | ] | | ].
    + intro Hz; apply (f_equal bv_unsigned) in Hz; vm_compute in Hz; discriminate Hz.
    + rewrite G19; reflexivity.
    + intro Hz; apply (f_equal bv_unsigned) in Hz; vm_compute in Hz; discriminate Hz.
    + rewrite G14; cbn [sv_denot]; rewrite E38, u_Z2bv by lia; f_equal; lia.
  - reflexivity.
  - change (ss_mem (mkSS 7880 s4_regs s4_mem None s4_facts)) with s4_mem. unfold s4_mem.
    constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok; cbn [base_val r_base r_lo r_hi r_wlo r_whi r_chunks]. rewrite E9, u_Z2bv by lia.
      split; [lia|]. split; [lia|]. split; [intros; lia|].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ sv2); [cbn [sv_denot]; rewrite E42, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm96] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ sv4); [cbn [sv_denot]; rewrite E43, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm104] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ a176); [cbn [sv_denot]; rewrite E40, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm144] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ (bot + 1 - top)); [cbn [sv_denot]; rewrite E41, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact M160] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ a184); [cbn [sv_denot]; rewrite E39, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm176] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ fimg); [cbn [sv_denot]; rewrite E34, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm224] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ SB); [cbn [sv_denot]; rewrite E38, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm240] |].
      constructor; [apply (chunk_ok_val _ _ _ _ _ _ _ bfp); [cbn [sv_denot]; rewrite E33, u_Z2bv by lia; f_equal; lia | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | compute; discriminate | exact Sm248] |].
      constructor.

    + apply (region_ok_reg8 _ _ _ 32 35 false (fimg + p) bf E32 E35); [lia | lia | lia | exact Vfp | discriminate].
    + apply (region_ok_reg8 _ _ _ 36 37 false (bimg + p) bb E36 E37); [lia | lia | lia | exact Vbp | discriminate].
  - change (ss_mem (mkSS 7880 s4_regs s4_mem None s4_facts)) with s4_mem. unfold s4_mem, reg8.
    cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, base_val. cbn [r_base r_lo r_hi].
    rewrite E9, E32, E36, !u_Z2bv by lia. lia.
  - change (ss_facts (mkSS 7880 s4_regs s4_mem None s4_facts)) with s4_facts.
    unfold facts_ok, s4_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite E9, E38, E20, E18, E27, E26, E25, E24, E21, E22, E23, E32, E33, E34, E35, E36, E37, E39, E40, E41.
    rewrite SBv. rewrite !u_Z2bv by lia.
    change (2 ^ 0) with 1; change (2 ^ 4) with 16; change (2 ^ 3) with 8. rewrite !Z.mod_1_r.
    repeat split; try lia; try assumption; apply mod16_mod8; assumption. }
pose (IDXi := SAlu ALU_ADD (SMd M_MUL (SAlu ALU_AND (SOff 20 0) (SLit 65535)) (SOff 25 0)) (SAlu ALU_AND (SOff 18 0) (SLit 65535))).
pose (IDXs := SAlu ALU_SRL (SAlu ALU_SLL IDXi (SLit 32)) (SLit 32)).
assert (UI : U E IDXi = p) by (apply (U_idx16 E 20 25 18 y Wd x E20 E25 E18); lia).
assert (AL1 : sv_denot E (SAlu ALU_ADD (SOff 34 0) IDXs) = sv_denot E (SOff 32 0)).
{ rewrite (denot_of_U2 E _ (fimg + p)).
  - cbn [sv_denot]. rewrite E32, u_Z2bv by lia. f_equal; lia.
  - unfold IDXs. rewrite (U_add_atom_zext32 E 34 IDXi fimg E34) by lia. rewrite UI, Z.mod_small by lia. reflexivity. }
assert (AL2 : sv_denot E (SAlu ALU_ADD (SOff 24 0) IDXs) = sv_denot E (SOff 36 0)).
{ rewrite (denot_of_U2 E _ (bimg + p)).
  - cbn [sv_denot]. rewrite E36, u_Z2bv by lia. f_equal; lia.
  - unfold IDXs. rewrite (U_add_atom_zext32 E 24 IDXi bimg E24) by lia. rewrite UI, Z.mod_small by lia. reflexivity. }
pose proof (st_ok_pi_add_alias E _ _ _ _ ST0 AL1) as ST1.
pose proof (st_ok_pi_add_alias E _ _ _ _ ST1 AL2) as ST2.
clear ST0 ST1.
eapply (RUNTO W 100 5400 E 512 (SOff 38 0) (SB, SB + 2 ^ 44 - 1) [] _ _ _ _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc mdE k);
  [ cbv [A_LIM]; lia | apply Eimg_env | exact ST2 | constructor | vm_compute; reflexivity
  | lazymatch goal with |- ?lhs = _ => let v := eval vm_compute in lhs in exact (@eq_refl _ v <: lhs = v) end
  | exact AJ
  | cbn [sh_obls ms_mem mkst]; repeat constructor; unfold ob_holds; cbn [ob_x ob_n]
  | cbn [set_facts ss_mem]; unfold ss_s4, s4_mem, reg8; cbn [ss_mem]; awrRO | ].
1: { rewrite (U_atom E 36 (bimg + p) E36) by lia.
     apply (obl_of_block SEGS B LAWS lyc Sc W memE mdE E (SOff 38 0) (bimg + p) 1 bimg Nb HAR Hbi); [ | lia | lia].
     rewrite (U_atom E 38 SB E38) by (rewrite SBv; lia). reflexivity. }
1: { rewrite (U_atom E 32 (fimg + p) E32) by lia.
     apply (obl_of_block SEGS B LAWS lyc Sc W memE mdE E (SOff 38 0) (fimg + p) 1 fimg Nb HAR Hfi); [ | lia | lia].
     rewrite (U_atom E 38 SB E38) by (rewrite SBv; lia). reflexivity. }
intros ws ms1 mat1 Hlen1 Himg1 Hst1 Hsh1 HJ1 Hfr1 Hfr1' Hgr1.
assert (EA1 : forall n, (n < 512)%nat -> ew (extK E 512 ws) n = ew E n) by (intros n Hn; apply (proj1 (env_agree_extK E 512 ws)); exact Hn).
pose proof (st_ok_pi_restrict_mkst _ _ _ _ Hst1 eq_refl) as Hms1. cbn [ss_pc sh_ss] in Hms1.
assert (K2 : getr regsE 2 = getr regs 2) by (apply KEEP5; cbv; tauto).
assert (K3 : getr regsE 3 = getr regs 3) by (apply KEEP5; cbv; tauto).
assert (K4 : getr regsE 4 = getr regs 4) by (apply KEEP5; cbv; tauto).
assert (K8 : getr regsE 8 = getr regs 8) by (apply KEEP5; cbv; tauto).
cbn [ms_mem mkst] in Hfr1, Hfr1', Hgr1.
assert (T1 : getr (ms_regs ms1) 1 = Z_to_bv 64 (BASE + 7972)) by (noW; cbn [sv_denot]; apply (img_env_codeptr _ Himg1)).
assert (T2 : getr (ms_regs ms1) 2 = getr regs 2) by (noW; cbn [sv_denot]; rewrite EA1 by lia; change (ew E 2) with (getr regsE 2); rewrite K2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (T3 : getr (ms_regs ms1) 3 = getr regs 3) by (noW; cbn [sv_denot]; rewrite EA1 by lia; change (ew E 3) with (getr regsE 3); rewrite K3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (T4 : getr (ms_regs ms1) 4 = getr regs 4) by (noW; cbn [sv_denot]; rewrite EA1 by lia; change (ew E 4) with (getr regsE 4); rewrite K4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (T8 : getr (ms_regs ms1) 8 = getr regs 8) by (noW; cbn [sv_denot]; rewrite EA1 by lia; change (ew E 8) with (getr regsE 8); rewrite K8, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (T10 : getr (ms_regs ms1) 10 = Z_to_bv 64 g) by (noW; cbn [sv_denot]; rewrite EA1 by lia; rewrite E21, u_Z2bv by lia; f_equal; lia).
assert (T11 : getr (ms_regs ms1) 11 = Z_to_bv 64 cfp) by (noW; cbn [sv_denot]; rewrite EA1 by lia; rewrite E22, u_Z2bv by lia; f_equal; lia).
assert (T12 : getr (ms_regs ms1) 12 = Z_to_bv 64 bfp) by (noW; cbn [sv_denot]; rewrite EA1 by lia; rewrite E33, u_Z2bv by lia; f_equal; lia).
assert (T13 : getr (ms_regs ms1) 13 = Z_to_bv 64 bf) by (noW; cbn [sv_denot]; rewrite EA1 by lia; rewrite E35, u_Z2bv by lia; f_equal; lia).
assert (T14 : getr (ms_regs ms1) 14 = Z_to_bv 64 bb) by (noW; cbn [sv_denot]; rewrite EA1 by lia; rewrite E37, u_Z2bv by lia; f_equal; lia).
rewrite Hms1.
eapply SRr_bind.
{ change (BASE + 5400) with (BASE + AF_asan3_cmpPixel).
  apply (CALL (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy mdE) mat1 mdE) p (Z_to_bv 64 (BASE + 7972))).
  - exact HJ1.
  - apply (wkept_trans _ _ _ _ _ memc memE); [exact WK | ].
    eapply (wkept_of_run B LAWS E _ lyc Sc W memE (ms_mem ms1) mdE sp1 HAR Hfr1' Hgr1); [noW | lia | lia | intros; apply HSpres; lia].
  - exact Rp.
  - unfold spZ. rewrite T2. exact Hsp.
  - rewrite T3; exact Hgp.
  - rewrite T4; exact Htp.
  - unfold s0Z. rewrite T8. exact Hs0.
  - exact T10.
  - exact T11.
  - exact T12.
  - exact T13.
  - exact T14.
  - exact T1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite u_Z2bv by lia. lia. }
intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & v & -> & HJ2 & Hpres2 & Hv2 & Hvd2 & WK2 & HK2 & LK2).
unfold st_ok_pi in Hst1.
pose (Rstk := hd (regw 0 0) s4_mem).
assert (KEPT3 : Forall (region_kept SEGS (extK E 512 ws) (ms_mem (restrict (w_H W) ms1)) (mrestrict (w_H W) mem2)) [Rstk]).
{ constructor; [ | constructor]. unfold Rstk. cbn [hd s4_mem ms_mem restrict].
  apply (region_kept_stack_aj SEGS B (extK E 512 ws) lyc Sc W (ms_mem ms1) W mem2 (sp1 - TCMP_STK) sp1 (fun _ => False) 9 0 256 0 0 _
           sp0 sp1 TFLUSH_STK FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc md2 k HK2 HJ2); try lia.
  rewrite EA1 by lia. rewrite E9, u_Z2bv by lia. reflexivity. }
assert (SUB3 : forall ss, ss_mem ss = s4_mem -> submem [Rstk] (ss_mem ss)).
{ intros ss Hm. rewrite Hm. unfold Rstk, s4_mem. cbn [hd]. apply submem_keep; [apply subregion_refl | apply submem_nil]. }
pose proof (st_ok_pi_after_call 44 _ _ _ regs2 (mrestrict (w_H W) mem2) [Rstk] 7972 Himg1 ltac:(lia) Hst1) as ST3.
specialize (ST3 eq_refl ltac:(cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(apply SUB3; vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hpres2 KEPT3).
set (E3 := havoc (extK E 512 ws) 44 (map (getr regs2) CLOB)) in ST3.
assert (EA3 : forall n, (n < 44)%nat -> ew E3 n = ew E n) by (intros n Hn; unfold E3; rewrite ew_havoc_old by lia; apply EA1; lia).
assert (E48 : ew E3 48 = v) by (rewrite <- Hv2; reflexivity).
assert (AR2 : AR SEGS B lyc Sc W mem2 md2) by exact (proj1 HJ2).
pose proof WK2 as [[_ [_ [_ [_ [_ Wpres2]]]]] Wlow2].
apply (BR W E3 _ (mkst regs2 (Z_to_bv 64 (BASE + 7972)) mem2 (seg_rom SEGS)) md2 _ BC_NE (SOff 48 0) (SLit 0) ST3).
- intros Htk ST4.
  assert (Vnz : v <> w64 0) by (intro Hz; revert Htk; cbn [branch_taken sv_denot]; rewrite E48, Hz; vm_compute; discriminate).
  assert (Ppx : PDp p) by (unfold PDp, PD; intro Hz; apply Vnz; apply Hvd2; intro Hpd; exact (Hpd Hz)).
  eapply (RUNTOP W 100 8076 E3 _ _ _ _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc md2 k);
    [ unfold E3; apply img_env_havoc; [exact Himg1 | cbv; lia]
    | exact ST4
    | lazymatch goal with |- ?lhs = _ => let v := eval vm_compute in lhs in exact (@eq_refl _ v <: lhs = v) end
    | exact I
    | exact HJ2
    | cbn; awrRO
    | intros ms5 mat5 Hst5 HJ5 Hfr5 Hfr5' Hgr5 ].
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ Hst5 eq_refl) as Hms5. cbn [ss_pc] in Hms5.
  cbn [ms_mem mkst] in Hfr5, Hfr5', Hgr5.
  assert (K9 : getr regsE 9 = getr regs 9) by (apply KEEP5; cbv; tauto).
  assert (X2 : getr (ms_regs ms5) 2 = getr regs 2) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 2) with (getr regsE 2); rewrite K2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (X3 : getr (ms_regs ms5) 3 = getr regs 3) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 3) with (getr regsE 3); rewrite K3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (X4 : getr (ms_regs ms5) 4 = getr regs 4) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 4) with (getr regsE 4); rewrite K4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (X8 : getr (ms_regs ms5) 8 = getr regs 8) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 8) with (getr regsE 8); rewrite K8, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (X9 : getr (ms_regs ms5) 9 = getr regs 9) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 9) with (getr regsE 9); rewrite K9, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (X6 : getr (ms_regs ms5) 6 = Z_to_bv 64 SB) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E38, u_Z2bv by lia; f_equal; lia).
  assert (X21 : getr (ms_regs ms5) 21 = Z_to_bv 64 g) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E21, u_Z2bv by lia; f_equal; lia).
  assert (X22 : getr (ms_regs ms5) 22 = Z_to_bv 64 cfp) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E22, u_Z2bv by lia; f_equal; lia).
  assert (X27 : getr (ms_regs ms5) 27 = Z_to_bv 64 top) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E27, u_Z2bv by lia; f_equal; lia).
  assert (X23 : getr (ms_regs ms5) 23 = Z_to_bv 64 left) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E23, u_Z2bv by lia; f_equal; lia).
  assert (X10 : getr (ms_regs ms5) 10 = Z_to_bv 64 a184) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E39, u_Z2bv by lia; f_equal; lia).
  assert (X11 : getr (ms_regs ms5) 11 = Z_to_bv 64 a176) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E40, u_Z2bv by lia; f_equal; lia).
  assert (X18 : getr (ms_regs ms5) 18 = Z_to_bv 64 sv2) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E42, u_Z2bv by lia; f_equal; lia).
  assert (X20 : getr (ms_regs ms5) 20 = Z_to_bv 64 sv4) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E43, u_Z2bv by lia; f_equal; lia).
  assert (X26 : getr (ms_regs ms5) 26 = Z_to_bv 64 (x - left + 1)).
  { noW. apply denot_of_U2. apply U_width; [rewrite EA3 by lia; exact E18 | rewrite EA3 by lia; exact E23 | lia | lia]. }
  assert (V160T : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sp1 + 160) 8 (bot + 1 - top)).
  { eapply (val_mem_run_out E _ W memE (ms_mem ms1)); [exact Hfr1' | lia | lia | intros k0 _; revert k0; noW | exact M160]. }
  assert (V160b : val_mem SEGS (mrestrict (w_H W) mem2) (sp1 + 160) 8 (bot + 1 - top)).
  { apply (val_mem_lkept W sp1 (ms_mem ms1) mem2); [exact LK2 | lia | lia | exact V160T]. }
  apply SRr_ret. unfold s4_postX. split; [reflexivity | ].
  exists (ms_regs ms5), (ms_mem ms5), (with_vm_backing (m_vm_lazy md2) mat5 md2), x.
  split; [f_equal; exact Hms5 | ].
  split; [exact HJ5 | ].
  split.
  { apply (wkept_trans _ _ _ _ _ memc mem2); [exact WK2 | ].
    eapply (wkept_of_run B LAWS E3 _ lyc Sc W mem2 (ms_mem ms5) md2 sp1 AR2 Hfr5' Hgr5); [noW | lia | lia | exact Wpres2]. }
  split.
  { intros r Hr. cbv [WKEPT5 In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; assumption. }
  split; [exact X6 | ]. split; [exact X21 | ]. split; [exact X22 | ].
  split; [exact Lx | ]. split; [exact X26 | ].
  split.
  { eapply (val_mem_run_out E3 _ W mem2 (ms_mem ms5)); [exact Hfr5' | lia | lia | intros k0 _; revert k0; noW | exact V160b]. }
  split; [exact X27 | ]. split; [exact X23 | ]. split; [exact X10 | ]. split; [exact X11 | ].
  split; [exact X18 | ]. split; [exact X20 | ].
  split.
  { exists y. split; [lia | exact Ppx]. }
  intros x' y' Ry' Rx'. exact (Nright x' y' Rx' Ry').

- intros Hnt ST4.
  assert (Vz : v = w64 0).
  { revert Hnt. cbn [branch_taken sv_denot]. rewrite E48, Z.add_0_r, Z_to_bv_bv_unsigned.
    intro Hb. apply Bool.negb_false_iff in Hb. apply bv_eqb_eq in Hb. exact Hb. }
  assert (NPp : ~ PDp p) by exact (proj1 Hvd2 Vz).
  assert (Xgt : c0 < x).
  { destruct (Z.eq_dec x c0) as [Exc | Exc]; [ | lia]. exfalso.
    destruct (Z.eq_dec y top) as [Eyt | Eyt].
    - apply NPp. unfold p. rewrite Eyt, Exc. exact Pc0.
    - apply (Nabove top ltac:(lia)). rewrite Exc. exact Pc0. }
  assert (F18 : ew E3 18 = Z_to_bv 64 x) by (rewrite EA3 by lia; exact E18).
  assert (F20 : ew E3 20 = Z_to_bv 64 y) by (rewrite EA3 by lia; exact E20).
  assert (F26 : ew E3 26 = Z_to_bv 64 (bot + 1)) by (rewrite EA3 by lia; exact E26).
  assert (K9 : getr regsE 9 = getr regs 9) by (apply KEEP5; cbv; tauto).
  assert (V216T : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sp1 + 216) 8 bimg).
  { eapply (val_mem_run_out E _ W memE (ms_mem ms1)); [exact Hfr1' | lia | lia | intros k0 _; revert k0; noW | exact M216]. }
  assert (V216b : val_mem SEGS (mrestrict (w_H W) mem2) (sp1 + 216) 8 bimg).
  { apply (val_mem_lkept W sp1 (ms_mem ms1) mem2); [exact LK2 | lia | lia | exact V216T]. }
  assert (V160T : val_mem SEGS (mrestrict (w_H W) (ms_mem ms1)) (sp1 + 160) 8 (bot + 1 - top)).
  { eapply (val_mem_run_out E _ W memE (ms_mem ms1)); [exact Hfr1' | lia | lia | intros k0 _; revert k0; noW | exact M160]. }
  assert (V160b : val_mem SEGS (mrestrict (w_H W) mem2) (sp1 + 160) 8 (bot + 1 - top)).
  { apply (val_mem_lkept W sp1 (ms_mem ms1) mem2); [exact LK2 | lia | lia | exact V160T]. }
  eapply (RUNTOP W 100 7880 E3 _ _ _ _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc md2 k);
    [ unfold E3; apply img_env_havoc; [exact Himg1 | cbv; lia]
    | exact ST4
    | lazymatch goal with |- ?lhs = _ => let v := eval vm_compute in lhs in exact (@eq_refl _ v <: lhs = v) end
    | exact I
    | exact HJ2
    | cbn; awrRO
    | intros ms5 mat5 Hst5 HJ5 Hfr5 Hfr5' Hgr5 ].
  cbn [ms_mem mkst] in Hfr5, Hfr5', Hgr5.
  assert (WK5 : wkept B lyc Sc W sp1 memc (ms_mem ms5)).
  { apply (wkept_trans _ _ _ _ _ memc mem2); [exact WK2 | ].
    eapply (wkept_of_run B LAWS E3 _ lyc Sc W mem2 (ms_mem ms5) md2 sp1 AR2 Hfr5' Hgr5); [noW | lia | lia | exact Wpres2]. }
  pose proof WK5 as [[_ [_ [_ [_ [_ Wpres5]]]]] _].
  assert (V216s5 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms5)) (sp1 + 216) 8 bimg).
  { eapply (val_mem_run_out E3 _ W mem2 (ms_mem ms5)); [exact Hfr5' | lia | lia | intros k0 _; revert k0; noW | exact V216b]. }
  assert (V160s5 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms5)) (sp1 + 160) 8 (bot + 1 - top)).
  { eapply (val_mem_run_out E3 _ W mem2 (ms_mem ms5)); [exact Hfr5' | lia | lia | intros k0 _; revert k0; noW | exact V160b]. }
  apply (BR W E3 _ ms5 _ _ BC_GEU (SOff 20 1) (SOff 26 0) Hst5).
  + intros Hge ST6.
    assert (Hif : (y + 1 <? bot + 1) = false).
    { revert Hge. unfold branch_taken. rewrite bv_ltu_unsigned.
      change (bv_unsigned (sv_denot E3 (SOff 20 1))) with (U E3 (SOff 20 1)).
      change (bv_unsigned (sv_denot E3 (SOff 26 0))) with (U E3 (SOff 26 0)).
      rewrite (U_atom_off E3 20 y 1 F20), (U_atom E3 26 (bot + 1) F26) by lia.
      intro Hb. apply Bool.negb_true_iff in Hb. exact Hb. }
    pose proof (proj1 (Z.ltb_ge _ _) Hif) as Ybot.
    eapply (RUNTOP W 100 7880 E3 _ _ _ _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k);
      [ unfold E3; apply img_env_havoc; [exact Himg1 | cbv; lia]
      | exact ST6
      | lazymatch goal with |- ?lhs = _ => let v := eval vm_compute in lhs in exact (@eq_refl _ v <: lhs = v) end
      | exact I
      | exact HJ5
      | cbn; awrRO
      | intros ms7 mat7 Hst7 HJ7 Hfr7 Hfr7' Hgr7 ].
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ Hst7 eq_refl) as Hms7. cbn [ss_pc] in Hms7.
    cbn [ms_mem mkst] in Hfr7, Hfr7', Hgr7.
    assert (Y2 : getr (ms_regs ms7) 2 = getr regs 2) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 2) with (getr regsE 2); rewrite K2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y3 : getr (ms_regs ms7) 3 = getr regs 3) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 3) with (getr regsE 3); rewrite K3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y4 : getr (ms_regs ms7) 4 = getr regs 4) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 4) with (getr regsE 4); rewrite K4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y8 : getr (ms_regs ms7) 8 = getr regs 8) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 8) with (getr regsE 8); rewrite K8, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y9 : getr (ms_regs ms7) 9 = getr regs 9) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 9) with (getr regsE 9); rewrite K9, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y21 : getr (ms_regs ms7) 21 = Z_to_bv 64 g) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E21, u_Z2bv by lia; f_equal; lia).
    assert (Y22 : getr (ms_regs ms7) 22 = Z_to_bv 64 cfp) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E22, u_Z2bv by lia; f_equal; lia).
    assert (Y27 : getr (ms_regs ms7) 27 = Z_to_bv 64 top) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E27, u_Z2bv by lia; f_equal; lia).
    assert (Y26 : getr (ms_regs ms7) 26 = Z_to_bv 64 (bot + 1)) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E26, u_Z2bv by lia; f_equal; lia).
    assert (Y25 : getr (ms_regs ms7) 25 = Z_to_bv 64 Wd) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E25, u_Z2bv by lia; f_equal; lia).
    assert (Y24 : getr (ms_regs ms7) 24 = Z_to_bv 64 bimg) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E24, u_Z2bv by lia; f_equal; lia).
    assert (Y23 : getr (ms_regs ms7) 23 = Z_to_bv 64 left) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E23, u_Z2bv by lia; f_equal; lia).
    assert (Y14 : getr (ms_regs ms7) 14 = Z_to_bv 64 SB) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E38, u_Z2bv by lia; f_equal; lia).
    assert (Y19 : getr (ms_regs ms7) 19 = Z_to_bv 64 65535) by (noW; reflexivity).
    assert (Y20 : getr (ms_regs ms7) 20 = Z_to_bv 64 top) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E27, u_Z2bv by lia; f_equal; lia).
    assert (Y18 : getr (ms_regs ms7) 18 = Z_to_bv 64 (x - 1)).
    { noW. apply denot_of_U2. rewrite (U_sub_not_ltu' E3 18 20 26 x y (bot + 1) 1 F18 F20 F26) by (rewrite ?Hif; lia). rewrite Hif. lia. }
    assert (AR5 : AR SEGS B lyc Sc W (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat5 md2)) by exact (proj1 HJ5).
    assert (WK7 : wkept B lyc Sc W sp1 memc (ms_mem ms7)).
    { apply (wkept_trans _ _ _ _ _ memc (ms_mem ms5)); [exact WK5 | ].
      eapply (wkept_of_run B LAWS E3 _ lyc Sc W (ms_mem ms5) (ms_mem ms7) _ sp1 AR5 Hfr7' Hgr7); [noW | lia | lia | exact Wpres5]. }
    assert (V216c : val_mem SEGS (mrestrict (w_H W) (ms_mem ms7)) (sp1 + 216) 8 bimg).
    { eapply (val_mem_run_out E3 _ W (ms_mem ms5) (ms_mem ms7)); [exact Hfr7' | lia | lia | intros k0 _; revert k0; noW | exact V216s5]. }
    assert (V160c : val_mem SEGS (mrestrict (w_H W) (ms_mem ms7)) (sp1 + 160) 8 (bot + 1 - top)).
    { eapply (val_mem_run_out E3 _ W (ms_mem ms5) (ms_mem ms7)); [exact Hfr7' | lia | lia | intros k0 _; revert k0; noW | exact V160s5]. }
    rewrite Hms7.
    apply (Hind (x - 1) top c0 top bot left (ms_regs ms7) (ms_mem ms7) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat7 (with_vm_backing (m_vm_lazy md2) mat5 md2))).
    * rewrite Nat2Z.inj_succ in Lmeas. nia.
    * exact Lleft.
    * lia.
    * lia.
    * lia.
    * exact Lbh.
    * exact Pc0.
    * intros x2 y2 Rx2 Ry2. destruct (Z.eq_dec x2 x) as [-> | Nx2].
      -- destruct (Z.eq_dec y2 y) as [-> | Ny2]; [exact NPp | apply Nabove; lia].
      -- apply Nright; lia.
    * intros y2 Ry2. lia.
    * exact HJ7.
    * exact WK7.
    * intros r Hr. cbv [WKEPT5 In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; assumption.
    * exact Y21.
    * exact Y22.
    * exact Y19.
    * exact Y20.
    * exact Y18.
    * exact Y27.
    * exact Y26.
    * exact Y25.
    * exact Y24.
    * exact Y23.
    * exact Y14.
    * exact V216c.
    * exact V160c.
  + intros Hlt ST6.
    assert (Hif : (y + 1 <? bot + 1) = true).
    { revert Hlt. unfold branch_taken. rewrite bv_ltu_unsigned.
      change (bv_unsigned (sv_denot E3 (SOff 20 1))) with (U E3 (SOff 20 1)).
      change (bv_unsigned (sv_denot E3 (SOff 26 0))) with (U E3 (SOff 26 0)).
      rewrite (U_atom_off E3 20 y 1 F20), (U_atom E3 26 (bot + 1) F26) by lia.
      intro Hb. apply Bool.negb_false_iff in Hb. exact Hb. }
    pose proof (proj1 (Z.ltb_lt _ _) Hif) as Ylt.
    eapply (RUNTOP W 100 7880 E3 _ _ _ _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k);
      [ unfold E3; apply img_env_havoc; [exact Himg1 | cbv; lia]
      | exact ST6
      | lazymatch goal with |- ?lhs = _ => let v := eval vm_compute in lhs in exact (@eq_refl _ v <: lhs = v) end
      | exact I
      | exact HJ5
      | cbn; awrRO
      | intros ms7 mat7 Hst7 HJ7 Hfr7 Hfr7' Hgr7 ].
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ Hst7 eq_refl) as Hms7. cbn [ss_pc] in Hms7.
    cbn [ms_mem mkst] in Hfr7, Hfr7', Hgr7.
    assert (Y2 : getr (ms_regs ms7) 2 = getr regs 2) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 2) with (getr regsE 2); rewrite K2, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y3 : getr (ms_regs ms7) 3 = getr regs 3) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 3) with (getr regsE 3); rewrite K3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y4 : getr (ms_regs ms7) 4 = getr regs 4) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 4) with (getr regsE 4); rewrite K4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y8 : getr (ms_regs ms7) 8 = getr regs 8) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 8) with (getr regsE 8); rewrite K8, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y9 : getr (ms_regs ms7) 9 = getr regs 9) by (noW; cbn [sv_denot]; rewrite EA3 by lia; change (ew E 9) with (getr regsE 9); rewrite K9, Z.add_0_r; apply Z_to_bv_bv_unsigned).
    assert (Y21 : getr (ms_regs ms7) 21 = Z_to_bv 64 g) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E21, u_Z2bv by lia; f_equal; lia).
    assert (Y22 : getr (ms_regs ms7) 22 = Z_to_bv 64 cfp) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E22, u_Z2bv by lia; f_equal; lia).
    assert (Y27 : getr (ms_regs ms7) 27 = Z_to_bv 64 top) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E27, u_Z2bv by lia; f_equal; lia).
    assert (Y26 : getr (ms_regs ms7) 26 = Z_to_bv 64 (bot + 1)) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E26, u_Z2bv by lia; f_equal; lia).
    assert (Y25 : getr (ms_regs ms7) 25 = Z_to_bv 64 Wd) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E25, u_Z2bv by lia; f_equal; lia).
    assert (Y24 : getr (ms_regs ms7) 24 = Z_to_bv 64 bimg) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E24, u_Z2bv by lia; f_equal; lia).
    assert (Y23 : getr (ms_regs ms7) 23 = Z_to_bv 64 left) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E23, u_Z2bv by lia; f_equal; lia).
    assert (Y14 : getr (ms_regs ms7) 14 = Z_to_bv 64 SB) by (noW; cbn [sv_denot]; rewrite EA3 by lia; rewrite E38, u_Z2bv by lia; f_equal; lia).
    assert (Y19 : getr (ms_regs ms7) 19 = Z_to_bv 64 65535) by (noW; reflexivity).
    assert (Y20 : getr (ms_regs ms7) 20 = Z_to_bv 64 (y + 1)).
    { noW. apply denot_of_U2. apply U_atom_off; [exact F20 | lia | lia]. }
    assert (Y18 : getr (ms_regs ms7) 18 = Z_to_bv 64 x).
    { noW. apply denot_of_U2. rewrite (U_sub_not_ltu' E3 18 20 26 x y (bot + 1) 1 F18 F20 F26) by (rewrite ?Hif; lia). rewrite Hif. lia. }
    assert (AR5 : AR SEGS B lyc Sc W (ms_mem ms5) (with_vm_backing (m_vm_lazy md2) mat5 md2)) by exact (proj1 HJ5).
    assert (WK7 : wkept B lyc Sc W sp1 memc (ms_mem ms7)).
    { apply (wkept_trans _ _ _ _ _ memc (ms_mem ms5)); [exact WK5 | ].
      eapply (wkept_of_run B LAWS E3 _ lyc Sc W (ms_mem ms5) (ms_mem ms7) _ sp1 AR5 Hfr7' Hgr7); [noW | lia | lia | exact Wpres5]. }
    assert (V216c : val_mem SEGS (mrestrict (w_H W) (ms_mem ms7)) (sp1 + 216) 8 bimg).
    { eapply (val_mem_run_out E3 _ W (ms_mem ms5) (ms_mem ms7)); [exact Hfr7' | lia | lia | intros k0 _; revert k0; noW | exact V216s5]. }
    assert (V160c : val_mem SEGS (mrestrict (w_H W) (ms_mem ms7)) (sp1 + 160) 8 (bot + 1 - top)).
    { eapply (val_mem_run_out E3 _ W (ms_mem ms5) (ms_mem ms7)); [exact Hfr7' | lia | lia | intros k0 _; revert k0; noW | exact V160s5]. }
    rewrite Hms7.
    apply (Hind x (y + 1) c0 top bot left (ms_regs ms7) (ms_mem ms7) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat5 md2)) mat7 (with_vm_backing (m_vm_lazy md2) mat5 md2))).
    * rewrite Nat2Z.inj_succ in Lmeas. lia.
    * exact Lleft.
    * exact Lx.
    * lia.
    * lia.
    * exact Lbh.
    * exact Pc0.
    * exact Nright.
    * intros y2 Ry2. destruct (Z.eq_dec y2 y) as [-> | Ny2]; [exact NPp | apply Nabove; lia].
    * exact HJ7.
    * exact WK7.
    * intros r Hr. cbv [WKEPT5 In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; assumption.
    * exact Y21.
    * exact Y22.
    * exact Y19.
    * exact Y20.
    * exact Y18.
    * exact Y27.
    * exact Y26.
    * exact Y25.
    * exact Y24.
    * exact Y23.
    * exact Y14.
    * exact V216c.
    * exact V160c.
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
intros c0 top bot left regsE memE mdE Bl Bc Bt Bb Ptc AJ WK K5 G21 G22 G19 G20 G18 G27 G26 G25 G24 G23 G14 M216 M160.
pose proof HGEO as (RW & RH & _).
apply (fl_s4lX (Z.to_nat ((Wd - 1 - c0) * (bot + 1 - top) + (bot - top) + 1)) (Wd - 1) top c0 top bot left regsE memE mdE);
  try assumption.
- rewrite Z2Nat.id by nia. lia.
- lia.
- lia.
- lia.
- intros x2 y2 Rx2 _. lia.
- intros y2 Ry2. lia.
Qed.
End e.
End d.
End c.
End b.
