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
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AC8a AChd ACjr ACj1 ACj0 ACjc ACje.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACit.
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
Ltac wscr_windows Hb :=
  let a := fresh "a" in let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Ha := fresh "Ha" in
  intros a [rg [Hrg Ha]]; cbn in Hrg;
  repeat (destruct Hrg as [<- | Hrg]; [cbn [r_base r_wlo r_whi] in Ha; rewrite Hb in Ha; first [unfold wscr; lia | left; lia] | ]);
  contradiction.
Ltac off_windows Hb :=
  let rg := fresh "rg" in let Hrg := fresh "Hrg" in let Ha := fresh "Ha" in
  intros [rg [Hrg Ha]]; cbn in Hrg;
  repeat (destruct Hrg as [<- | Hrg]; [cbn [r_base r_wlo r_whi] in Ha; rewrite Hb in Ha; lia | ]);
  contradiction.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition s2o_regs := sr_set (sr_set (sr_set sr_atoms 12%bv (SOff 22 0)) 14%bv (SOff 22 1)) 27%bv (SLit 65535).
Definition s2o_mem : smem :=
  [ YP09.mkRegion (Some 9%nat) 152 176 152 176 [ YP09.mkChunk 160 (CVal 8 (SOff 33 0)) ];
    YP09.mkRegion (Some 9%nat) 200 232 200 200
      [ YP09.mkChunk 200 (CVal 8 (SOff 11 0)); YP09.mkChunk 216 (CVal 8 (SOff 36 0)); YP09.mkChunk 224 (CVal 8 (SOff 32 0)) ] ].
Definition s2o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (11%nat, mkAF 1 65535 0); (22%nat, mkAF 1 65534 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 0); (36%nat, HPTR 0); (33%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0); (35%nat, HPTR 3) ] [] [].
Definition ss_s2o : sstate := mkSS 7260 s2o_regs s2o_mem None s2o_facts.
Definition s2t_regs := sr_set sr_atoms 27%bv (SLit 65535).
Definition s2t_mem : smem :=
  [ YP09.mkRegion (Some 9%nat) 88 232 88 88
      [ YP09.mkChunk 88 (CVal 8 (SOff 34 0)); YP09.mkChunk 160 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 22 0));
        YP09.mkChunk 192 (CVal 8 (SOff 33 0)); YP09.mkChunk 200 (CVal 8 (SOff 37 0)) ] ].
Definition s2t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (22%nat, mkAF 1 65534 0);
(25%nat, HPTR 4); (24%nat, HPTR 3); (32%nat, HPTR 0); (36%nat, HPTR 0); (33%nat, mkAF 0 65533 0); (34%nat, mkAF 1 65534 0); (35%nat, HPTR 3);
(37%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2t : sstate := mkSS 7424 s2t_regs s2t_mem None s2t_facts.
Definition s2o_postX (top r : Z) : world SEGS -> config -> Prop :=
  fun W' c' =>
    W' = W /\
    exists (rgO : bvmap 5 word) (mmO : word -> option byte) (mdO : Model) (bot : Z),
      c' = {| cfg_ms := mkst rgO (Z_to_bv 64 (BASE + 7640)) mmO (seg_rom SEGS); cfg_model := mdO |} /\
      ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W mmO mdO k /\
      wkept B lyc Sc W sp1 memc mmO /\
      (forall q : Prelude.reg, In q WKEPT5 -> getr rgO q = getr regs q) /\
      getr rgO 6 = Z_to_bv 64 SB /\
      getr rgO 21 = Z_to_bv 64 g /\
      getr rgO 22 = Z_to_bv 64 cfp /\
      getr rgO 27 = Z_to_bv 64 65535 /\
      getr rgO 19 = Z_to_bv 64 top /\
      getr rgO 15 = Z_to_bv 64 (bot + 1) /\
      top <= bot < Hd /\
      val_mem SEGS (mrestrict (w_H W) mmO) (sp1 + 216) 8 bimg /\
      val_mem SEGS (mrestrict (w_H W) mmO) (sp1 + 184) 8 top /\
      (bot = top \/ exists col, 0 <= col < Wd /\ PDp (bot * Wd + col)) /\
      (forall px, (bot + 1) * Wd <= px < (r + 1) * Wd -> ~ PDp px).
Definition s2o_stmtX (m : nat) : Prop :=
  forall (i top v18 : Z) (regsE : bvmap 5 word) (memE : word -> option byte) (mdE : Model),
    i - top <= Z.of_nat m ->
    0 <= top ->
    top < i ->
    i < Hd ->
    ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memE mdE k ->
    wkept B lyc Sc W sp1 memc memE ->
    (forall q : Prelude.reg, In q WKEPT5 -> getr regsE q = getr regs q) ->
    getr regsE 6 = Z_to_bv 64 SB ->
    getr regsE 25 = Z_to_bv 64 g ->
    getr regsE 24 = Z_to_bv 64 cfp ->
    getr regsE 11 = Z_to_bv 64 Wd ->
    getr regsE 22 = Z_to_bv 64 i ->
    getr regsE 12 = Z_to_bv 64 i ->
    getr regsE 14 = Z_to_bv 64 (i + 1) ->
    getr regsE 27 = Z_to_bv 64 65535 ->
    getr regsE 18 = Z_to_bv 64 v18 ->
    v18 mod 2 ^ 32 = i * Wd ->
    val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 88) 8 (top + 1) ->
    val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 160) 8 top ->
    val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 184) 8 top ->
    val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 192) 8 top ->
    val_mem SEGS (mrestrict (w_H W) memE) (sp1 + 216) 8 bimg ->
    SRr SEGS W {| cfg_ms := mkst regsE (Z_to_bv 64 (BASE + 7260)) memE (seg_rom SEGS); cfg_model := mdE |} (s2o_postX top i).
Lemma fl_s2o_stepX : forall m, s2o_stmtX m -> s2o_stmtX (Datatypes.S m).
Proof using LAWS TCMP HC HGEO HFIMG.
intros m IH i top v18 regsE memE mdE Ms T0 Ti Ih Jn Wk Kp X6 X25 X24 X11 X22 X12 X14 X27 X18 Mv At88 At160 At184 At192 At216.
wctx_names. wprelude Jn.
pose proof (al_blocks _ _ LAWS lyc Sc W memE mdE g CGIF_SIZE HAR Hg) as Bg.
pose proof (al_blocks _ _ LAWS lyc Sc W memE mdE cfp FRAME_SIZE HAR Hcf) as Bc.
pose proof (al_blocks _ _ LAWS lyc Sc W memE mdE bfp FRAME_SIZE HAR Hbf) as Bb.
pose proof (al_blocks _ _ LAWS lyc Sc W memE mdE fimg Nb HAR Hfi) as Bf.
pose proof (al_blocks _ _ LAWS lyc Sc W memE mdE bimg Nb HAR Hbi) as Bi.
assert (SPr : 140735332483072 + 13000 <= sp1 /\ sp1 + 384 <= sp0 /\ sp0 <= 2 ^ 47) by lia.
assert (SBv : SB = 2147450880) by reflexivity.
assert (Rq : req_size CGIF_SIZE = 96 /\ req_size FRAME_SIZE = 40 /\ req_size Nb = Nb) by (repeat split; try reflexivity; unfold req_size; destruct (Nb =? 0) eqn:Hz; [apply Z.eqb_eq in Hz; lia | reflexivity]).
assert (B9 : bv_unsigned (getr regsE 9) = sp1).
{ rewrite (Kp 9%bv) by (unfold WKEPT5; simpl; tauto). rewrite H9. apply u_Z2bv; lia. }
assert (VK : forall off v mm, wkept B lyc Sc W sp1 memc mm -> 0 <= off -> off + 8 <= 280 ->
  (forall kk, 0 <= kk < 8 -> ~ wscr sp1 (sp1 + off + kk)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (sp1 + off) 8 v -> val_mem SEGS (mrestrict (w_H W) mm) (sp1 + off) 8 v).
{ intros off v mm Hk Ho1 Ho2 Hn Hv. eapply val_mem_wkept; eauto; lia. }
set (EX := [Z_to_bv 64 fimg; Z_to_bv 64 top; Z_to_bv 64 (top + 1); Z_to_bv 64 bfp; Z_to_bv 64 bimg; Z_to_bv 64 Wd]).
set (E0 := Eimg (Ereg regsE EX)).
assert (B9' : base_val E0 (Some 9%nat) = sp1) by exact B9.
assert (EA0 : env_agree 32 (Ereg regsE EX) E0).
{ split; [ | reflexivity]. intros n Hn. unfold E0, Eimg. cbn [ew].
  rewrite (proj2 (Nat.leb_gt A_TEXT n)) by (unfold A_TEXT; lia). reflexivity. }
assert (GR : forall ss ms r e v, st_ok_pi SEGS VAL E0 ss (restrict (w_H W) ms) ->
  sr_get (ss_regs ss) r = e -> U E0 e = v -> getr (ms_regs ms) r = Z_to_bv 64 v).
{ intros ss ms r e v Hs He Hu. rewrite (st_ok_pi_restrict_reg _ _ _ _ r Hs), He. apply denot_of_U2. exact Hu. }
assert (KR : forall ss ms, st_ok_pi SEGS VAL E0 ss (restrict (w_H W) ms) ->
  forallb (fun q => sv_eqb (sr_get (ss_regs ss) q) (SOff (Z.to_nat (bv_unsigned q)) 0)) WKEPT5 = true ->
  forall q, In q WKEPT5 -> getr (ms_regs ms) q = getr regs q).
{ intros ss ms Hs Hb q Hq. rewrite <- (Kp q Hq). exact (regs_kept_of_st_ok_pi _ _ _ _ _ _ Hs EA0 Hb q Hq). }
assert (WKS : forall (Ex : env) (rs : smem) (m1 m2 : word -> option byte) (md1 : Model),
  ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W m1 md1 k ->
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange Ex rs a -> wscr sp1 a) -> wkept B lyc Sc W sp1 m1 m2).
{ intros Ex rs m1 m2 md1 J1 F12 G12 Ww.
  pose proof J1 as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P1 & _).
  apply (wkept_of_run B LAWS Ex rs lyc Sc W m1 m2 md1 sp1 A1 F12 G12 Ww); [lia | lia | intros a Ha; apply P1; lia]. }
assert (A32 : ew E0 32 = Z_to_bv 64 fimg) by reflexivity.
assert (A33 : ew E0 33 = Z_to_bv 64 top) by reflexivity.
assert (A34 : ew E0 34 = Z_to_bv 64 (top + 1)) by reflexivity.
assert (A35 : ew E0 35 = Z_to_bv 64 bfp) by reflexivity.
assert (A36 : ew E0 36 = Z_to_bv 64 bimg) by reflexivity.
assert (A37 : ew E0 37 = Z_to_bv 64 Wd) by reflexivity.
assert (ST0 : st_ok_pi SEGS VAL E0 ss_s2o (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 7260)) memE (seg_rom SEGS)))).
{ change (restrict (w_H W) (mkst regsE (Z_to_bv 64 (BASE + 7260)) memE (seg_rom SEGS)))
    with (mkst regsE (Z_to_bv 64 (BASE + 7260)) (mrestrict (w_H W) memE) (seg_rom SEGS)).
  apply (pa_entry_st_ok_full E0 7260 s2o_regs regsE s2o_mem s2o_facts (mrestrict (w_H W) memE)).
  - unfold s2o_regs.
    apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity | ] | reflexivity | ] | reflexivity | ].
    + cbn [sv_denot]. change (ew E0 22) with (getr regsE 22). rewrite at_self, X12, X22. reflexivity.
    + cbn [sv_denot]. change (ew E0 22) with (getr regsE 22). rewrite X22, u_Z2bv, X14 by lia. reflexivity.
    + cbn [sv_denot]. exact X27.
  - reflexivity.
  - unfold s2o_mem.
    repeat apply Forall_cons; try apply Forall_nil;
      unfold region_ok; cbv beta zeta; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite B9';
      (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply apresent_writable; apply HSpres; lia|]).
    + apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ top) | apply Forall_nil].
      * cbn [sv_denot]. rewrite A33, at_self. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * exact At160.
    + apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ Wd) | apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ bimg) | apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ fimg) | apply Forall_nil]]].
      * cbn [sv_denot]. change (ew E0 11) with (getr regsE 11). rewrite at_self. exact X11.
      * cbn. lia.
      * cbn. lia.
      * apply VK; [exact Wk | lia | lia | intros kk Hk; unfold wscr; lia | exact V200].
      * cbn [sv_denot]. rewrite A36, at_self. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * exact At216.
      * cbn [sv_denot]. rewrite A32, at_self. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * apply VK; [exact Wk | lia | lia | intros kk Hk; unfold wscr; lia | exact HFIMG].
  - unfold s2o_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi].
    rewrite !B9'. repeat split; lia.
  - unfold facts_ok, s2o_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    change (ew E0 9) with (getr regsE 9). change (ew E0 6) with (getr regsE 6). change (ew E0 11) with (getr regsE 11).
    change (ew E0 22) with (getr regsE 22). change (ew E0 25) with (getr regsE 25). change (ew E0 24) with (getr regsE 24).
    rewrite A32, A33, A34, A35, A36.
    rewrite B9, X6, X11, X22, X25, X24, !u_Z2bv by lia.
    repeat split; try lia; try apply Z.mod_1_r.
    + exact Hsp1al.
    + exact (proj1 Bg).
    + exact (mod16_mod8 _ (proj1 Bc)).
    + exact (mod16_mod8 _ (proj1 Bb)). }
let v := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 40 7308 ss_s2o) in
lazymatch v with pair ?s1 ?t1 =>
  apply (RUNTOP W 40 7308 E0 ss_s2o s1 t1 _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc mdE k);
  [ apply Eimg_env | exact ST0 | vm_compute; reflexivity | exact I | exact Jn | wscr_windows B9' | ]
end.
intros ms1 mat1 ST1 Jn1 Fr1 Fr1r Gr1.
assert (Wk1 : wkept B lyc Sc W sp1 memc (ms_mem ms1)).
{ apply (wkept_trans _ _ _ _ _ _ _ _ Wk). exact (WKS _ _ _ _ _ Jn Fr1r Gr1 ltac:(wscr_windows B9')). }
assert (U18 : U E0 (SOff 18 0) = v18 mod 2 ^ 64).
{ unfold U. cbn [sv_denot]. change (ew E0 18) with (getr regsE 18). rewrite at_self, X18, unsigned_lit.
  unfold zcanon. rewrite M64_val. reflexivity. }
assert (M32 : U E0 (SOff 18 0) mod 2 ^ 32 = i * Wd).
{ rewrite U18, (Z.mod_mod_divide v18 (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity). exact Mv. }
assert (UZ32 : U E0 (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32)) = i * Wd)
  by (rewrite U_zext32; exact M32).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ ST1 eq_refl) as RG0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ ST1 eq_refl) as RG1.
rewrite (st_ok_pi_restrict_mkst _ _ _ _ ST1 eq_refl).
eapply SRr_bind.
{ apply (fl_s2iX B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp
    gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO (Z.to_nat Wd)
    0 (ms_regs ms1) (ms_mem ms1) _ i top).
  - rewrite Z2Nat.id by lia. lia.
  - lia.
  - lia.
  - lia.
  - exact Jn1.
  - exact Wk1.
  - exact (KR _ _ ST1 eq_refl).
  - apply (GR _ _ 6%bv (SOff 6 0) _ ST1 eq_refl). apply U_atom; [exact X6 | lia].
  - apply (GR _ _ 25%bv (SOff 25 0) _ ST1 eq_refl). apply U_atom; [exact X25 | lia].
  - apply (GR _ _ 24%bv (SOff 24 0) _ ST1 eq_refl). apply U_atom; [exact X24 | lia].
  - apply (GR _ _ 23%bv (SAlu ALU_ADD (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32))) (SLit 0)) _ ST1 eq_refl).
    rewrite U_add_lit0, (U_add_atom_zext32 E0 32 (SOff 18 0) fimg) by (rewrite ?A32; first [reflexivity | lia]).
    rewrite M32. lia.
  - apply (GR _ _ 20%bv (SAlu ALU_ADD (SOff 32 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32))) _ ST1 eq_refl).
    rewrite (U_add_atom_zext32 E0 32 (SOff 18 0) fimg) by (rewrite ?A32; first [reflexivity | lia]).
    rewrite M32. lia.
  - apply (GR _ _ 26%bv (SAlu ALU_ADD (SAlu ALU_ADD (SOff 36 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32))) (SLit 0)) _ ST1 eq_refl).
    rewrite U_add_lit0, (U_add_atom_zext32 E0 36 (SOff 18 0) bimg) by (rewrite ?A36; first [reflexivity | lia]).
    rewrite M32. lia.
  - apply (GR _ _ 19%bv (SAlu ALU_ADD (SOff 36 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 18 0) (SLit 32)) (SLit 32))) _ ST1 eq_refl).
    rewrite (U_add_atom_zext32 E0 36 (SOff 18 0) bimg) by (rewrite ?A36; first [reflexivity | lia]).
    rewrite M32. lia.
  - apply (GR _ _ 21%bv (SOff 11 0) _ ST1 eq_refl).
    rewrite (U_atom E0 11 Wd); [f_equal; lia | change (ew E0 11) with (getr regsE 11); exact X11 | lia].
  - eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At192.
  - apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 152 8 (SOff 22 1) (i + 1) RG0 B9); [cbn; tauto | | lia | lia].
    cbn [sv_denot]. change (ew E0 22) with (getr regsE 22). rewrite X22, u_Z2bv by lia. reflexivity. }
intros W2 c2 Wle2 Post2.
destruct Post2 as (-> & rg2 & mm2 & md2 & pc2 & -> & Jn2 & Wk2 & Lk2 & Pr2 & S6 & Cases).
assert (Kp2 : forall q, In q WKEPT5 -> getr rg2 q = getr regs q).
{ intros q Hq. rewrite (Pr2 q) by (revert Hq; unfold WKEPT5; cbn; intros [<-|[<-|[<-|[<-|[<-|[]]]]]]; reflexivity).
  exact (KR _ _ ST1 eq_refl q Hq). }
assert (R24 : getr rg2 24 = Z_to_bv 64 cfp)
  by (rewrite (Pr2 24%bv) by reflexivity; apply (GR _ _ 24%bv (SOff 24 0) _ ST1 eq_refl); apply U_atom; [exact X24 | lia]).
assert (R25 : getr rg2 25 = Z_to_bv 64 g)
  by (rewrite (Pr2 25%bv) by reflexivity; apply (GR _ _ 25%bv (SOff 25 0) _ ST1 eq_refl); apply U_atom; [exact X25 | lia]).
assert (R27 : getr rg2 27 = Z_to_bv 64 65535)
  by (rewrite (Pr2 27%bv) by reflexivity; apply (GR _ _ 27%bv (SLit 65535) _ ST1 eq_refl); rewrite U_SLit; reflexivity).
assert (R18 : getr rg2 18 = Z_to_bv 64 (v18 mod 2 ^ 64))
  by (rewrite (Pr2 18%bv) by reflexivity; apply (GR _ _ 18%bv (SOff 18 0) _ ST1 eq_refl); exact U18).
assert (L216 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 216) 8 bimg).
{ eapply val_mem_lkept; [exact Lk2 | lia | lia | ].
  eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At216. }
assert (L184 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 184) 8 top).
{ eapply val_mem_lkept; [exact Lk2 | lia | lia | ].
  eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At184. }
assert (L88 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 88) 8 (top + 1)).
{ eapply val_mem_lkept; [exact Lk2 | lia | lia | ].
  eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At88. }
assert (L160 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 160) 8 top).
{ eapply val_mem_lkept; [exact Lk2 | lia | lia | ].
  apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 160 8 (SOff 33 0) top RG0 B9); [cbn; tauto | | lia | lia].
  cbn [sv_denot]. rewrite A33, at_self. reflexivity. }
assert (L192 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 192) 8 top).
{ eapply val_mem_lkept; [exact Lk2 | lia | lia | ].
  eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At192. }
assert (L200 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 200) 8 Wd)
  by (apply VK; [exact Wk2 | lia | lia | intros kk Hk; unfold wscr; lia | exact V200]).
assert (L168 : val_mem SEGS (mrestrict (w_H W) mm2) (sp1 + 168) 8 i).
{ eapply val_mem_lkept; [exact Lk2 | lia | lia | ].
  apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 168 8 (SOff 22 0) i RG0 B9); [cbn; tauto | | lia | lia].
  cbn [sv_denot]. change (ew E0 22) with (getr regsE 22). rewrite at_self. exact X22. }
destruct Cases as [(-> & R22 & NoDiff) | (-> & (col & Hcol & HPD) & R19 & R15 & R21 & R22)].
- assert (R22i : getr rg2 22 = Z_to_bv 64 i).
  { rewrite R22. apply (GR _ _ 22%bv (SOff 22 0) _ ST1 eq_refl). apply U_atom; [exact X22 | lia]. }
  set (EY := [Z_to_bv 64 fimg; Z_to_bv 64 top; Z_to_bv 64 (top + 1); Z_to_bv 64 bfp; Z_to_bv 64 bimg; Z_to_bv 64 Wd]).
  set (E1 := Eimg (Ereg rg2 EY)).
  assert (C9 : bv_unsigned (getr rg2 9) = sp1).
  { rewrite (Kp2 9%bv) by (unfold WKEPT5; simpl; tauto). rewrite H9. apply u_Z2bv; lia. }
  assert (C9' : base_val E1 (Some 9%nat) = sp1) by exact C9.
  assert (EA1 : env_agree 32 (Ereg rg2 EY) E1).
  { split; [ | reflexivity]. intros n Hn. unfold E1, Eimg. cbn [ew].
    rewrite (proj2 (Nat.leb_gt A_TEXT n)) by (unfold A_TEXT; lia). reflexivity. }
  assert (GR1 : forall ss ms r e v, st_ok_pi SEGS VAL E1 ss (restrict (w_H W) ms) ->
    sr_get (ss_regs ss) r = e -> U E1 e = v -> getr (ms_regs ms) r = Z_to_bv 64 v).
  { intros ss ms r e v Hs He Hu. rewrite (st_ok_pi_restrict_reg _ _ _ _ r Hs), He. apply denot_of_U2. exact Hu. }
  assert (KR1 : forall ss ms, st_ok_pi SEGS VAL E1 ss (restrict (w_H W) ms) ->
    forallb (fun q => sv_eqb (sr_get (ss_regs ss) q) (SOff (Z.to_nat (bv_unsigned q)) 0)) WKEPT5 = true ->
    forall q, In q WKEPT5 -> getr (ms_regs ms) q = getr regs q).
  { intros ss ms Hs Hb q Hq. rewrite <- (Kp2 q Hq). exact (regs_kept_of_st_ok_pi _ _ _ _ _ _ Hs EA1 Hb q Hq). }
  assert (D32 : ew E1 32 = Z_to_bv 64 fimg) by reflexivity.
  assert (D33 : ew E1 33 = Z_to_bv 64 top) by reflexivity.
  assert (D34 : ew E1 34 = Z_to_bv 64 (top + 1)) by reflexivity.
  assert (D35 : ew E1 35 = Z_to_bv 64 bfp) by reflexivity.
  assert (D36 : ew E1 36 = Z_to_bv 64 bimg) by reflexivity.
  assert (D37 : ew E1 37 = Z_to_bv 64 Wd) by reflexivity.
  assert (ST2 : st_ok_pi SEGS VAL E1 ss_s2t (restrict (w_H W) (mkst rg2 (Z_to_bv 64 (BASE + 7424)) mm2 (seg_rom SEGS)))).
  { change (restrict (w_H W) (mkst rg2 (Z_to_bv 64 (BASE + 7424)) mm2 (seg_rom SEGS)))
      with (mkst rg2 (Z_to_bv 64 (BASE + 7424)) (mrestrict (w_H W) mm2) (seg_rom SEGS)).
    apply (pa_entry_st_ok_full E1 7424 s2t_regs rg2 s2t_mem s2t_facts (mrestrict (w_H W) mm2)).
    - unfold s2t_regs. apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity | ]. cbn [sv_denot]. exact R27.
    - reflexivity.
    - unfold s2t_mem.
      repeat apply Forall_cons; try apply Forall_nil;
        unfold region_ok; cbv beta zeta; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite C9';
        (split; [lia|]); (split; [lia|]); (split; [intros o Ho; lia|]).
      apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ (top + 1)) |
        apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ top) |
        apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ i) |
        apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ top) |
        apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ Wd) | apply Forall_nil]]]]].
      + cbn [sv_denot]. rewrite D34, at_self. reflexivity.
      + cbn. lia.
      + cbn. lia.
      + exact L88.
      + cbn [sv_denot]. rewrite D33, at_self. reflexivity.
      + cbn. lia.
      + cbn. lia.
      + exact L160.
      + cbn [sv_denot]. change (ew E1 22) with (getr rg2 22). rewrite R22i, u_Z2bv by lia. f_equal; lia.
      + cbn. lia.
      + cbn. lia.
      + exact L168.
      + cbn [sv_denot]. rewrite D33, at_self. reflexivity.
      + cbn. lia.
      + cbn. lia.
      + exact L192.
      + cbn [sv_denot]. rewrite D37, at_self. reflexivity.
      + cbn. lia.
      + cbn. lia.
      + exact L200.
    - unfold s2t_mem. cbn [pairwise_disjoint all_disjoint]. repeat split.
    - unfold facts_ok, s2t_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      change (ew E1 9) with (getr rg2 9). change (ew E1 6) with (getr rg2 6).
      change (ew E1 22) with (getr rg2 22). change (ew E1 25) with (getr rg2 25). change (ew E1 24) with (getr rg2 24).
      rewrite D32, D33, D34, D35, D36, D37.
      rewrite C9, S6, R22i, R25, R24, !u_Z2bv by lia.
      repeat split; try lia; try apply Z.mod_1_r.
      + exact Hsp1al.
      + exact (proj1 Bg).
      + exact (mod16_mod8 _ (proj1 Bc)).
      + exact (mod16_mod8 _ (proj1 Bb)). }
  assert (UT : U E1 (SOff 33 0) = top) by (apply U_atom; [exact D33 | lia]).
  assert (UI1 : U E1 (SAlu ALU_AND (SOff 22 (-1)) (SLit 65535)) = i - 1).
  { rewrite (U_and_ffff_off E1 22 i (-1)) by
      (first [change (ew E1 22) with (getr rg2 22); exact R22i | lia]). lia. }
  let v := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 30 7456 ss_s2t) in
  lazymatch v with pair ?s3 ?t3 =>
    apply (RUNTOP W 30 7456 E1 ss_s2t s3 t3 _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc md2 k);
    [ apply Eimg_env | exact ST2 | vm_compute; reflexivity | exact I | exact Jn2 | wscr_windows C9' | ]
  end.
  intros ms3 mat3 ST3 Jn3 Fr3 Fr3r Gr3.
  apply (BR W E1 _ ms3 _ _ BC_LTU (SOff 33 0) (SAlu ALU_AND (SOff 22 (-1)) (SLit 65535)) ST3).
  + intros Btk ST3b. rewrite branch_ltu_U, UT, UI1 in Btk. apply Z.ltb_lt in Btk.
    match type of ST3b with st_ok_pi _ _ _ ?ssb _ =>
      let v := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 30 7260 ssb) in
      lazymatch v with pair ?s4 ?t4 =>
        apply (RUNTOP W 30 7260 E1 ssb s4 t4 ms3 TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k);
        [ apply Eimg_env | exact ST3b | vm_compute; reflexivity | exact I | exact Jn3 | wscr_windows C9' | ]
      end
    end.
    intros ms4 mat4 ST4 Jn4 Fr4 Fr4r Gr4.
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ ST4 eq_refl).
    assert (U18b : U E1 (SOff 18 0) = v18 mod 2 ^ 64).
    { unfold U. cbn [sv_denot]. change (ew E1 18) with (getr rg2 18). rewrite at_self, R18, unsigned_lit.
      unfold zcanon. rewrite M64_val. apply Z.mod_mod. lia. }
    assert (UW1 : U E1 (SOff 37 0) = Wd) by (apply U_atom; [exact D37 | lia]).
    assert (M32b : U E1 (SOff 18 0) mod 2 ^ 32 = i * Wd).
    { rewrite U18b, (Z.mod_mod_divide v18 (2 ^ 64) (2 ^ 32)) by (exists (2 ^ 32); reflexivity). exact Mv. }
    assert (Msub : U E1 (SAluw ALU_SUB (SOff 18 0) (SOff 37 0)) mod 2 ^ 32 = (i - 1) * Wd).
    { rewrite U_subw_mod32, UW1, <- Zminus_mod_idemp_l, M32b.
      replace (i * Wd - Wd) with ((i - 1) * Wd) by ring. apply Z.mod_small. nia. }
    assert (Wk4 : wkept B lyc Sc W sp1 memc (ms_mem ms4)).
    { apply (wkept_trans _ _ _ _ _ _ _ _ Wk2).
      apply (wkept_trans _ _ _ _ _ _ (ms_mem ms3)).
      - exact (WKS _ _ _ _ _ Jn2 Fr3r Gr3 ltac:(wscr_windows C9')).
      - exact (WKS _ _ _ _ _ Jn3 Fr4r Gr4 ltac:(wscr_windows C9')). }
    eapply SRr_mono.
    { apply (IH (i - 1) top (U E1 (SAluw ALU_SUB (SOff 18 0) (SOff 37 0))) (ms_regs ms4) (ms_mem ms4) _).
      - rewrite Nat2Z.inj_succ in Ms. lia.
      - exact T0.
      - exact Btk.
      - lia.
      - exact Jn4.
      - exact Wk4.
      - exact (KR1 _ _ ST4 eq_refl).
      - apply (GR1 _ _ 6%bv (SOff 6 0) _ ST4 eq_refl).
        apply U_atom; [change (ew E1 6) with (getr rg2 6); exact S6 | lia].
      - apply (GR1 _ _ 25%bv (SOff 25 0) _ ST4 eq_refl).
        apply U_atom; [change (ew E1 25) with (getr rg2 25); exact R25 | lia].
      - apply (GR1 _ _ 24%bv (SOff 24 0) _ ST4 eq_refl).
        apply U_atom; [change (ew E1 24) with (getr rg2 24); exact R24 | lia].
      - apply (GR1 _ _ 11%bv (SOff 37 0) _ ST4 eq_refl). exact UW1.
      - apply (GR1 _ _ 22%bv (SOff 22 (-1)) _ ST4 eq_refl).
        rewrite (U_atom_off E1 22 i (-1)) by
          (first [change (ew E1 22) with (getr rg2 22); exact R22i | lia]). lia.
      - apply (GR1 _ _ 12%bv (SOff 22 (-1)) _ ST4 eq_refl).
        rewrite (U_atom_off E1 22 i (-1)) by
          (first [change (ew E1 22) with (getr rg2 22); exact R22i | lia]). lia.
      - apply (GR1 _ _ 14%bv (SOff 22 0) _ ST4 eq_refl).
        rewrite (U_atom E1 22 i) by (first [change (ew E1 22) with (getr rg2 22); exact R22i | lia]). lia.
      - apply (GR1 _ _ 27%bv (SLit 65535) _ ST4 eq_refl). rewrite U_SLit. reflexivity.
      - apply (GR1 _ _ 18%bv (SAluw ALU_SUB (SOff 18 0) (SOff 37 0)) _ ST4 eq_refl). reflexivity.
      - exact Msub.
      - eapply val_mem_frame; [exact Fr4r | intros kk Hk; off_windows C9' | lia | lia | ].
        eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L88.
      - eapply val_mem_frame; [exact Fr4r | intros kk Hk; off_windows C9' | lia | lia | ].
        eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L160.
      - eapply val_mem_frame; [exact Fr4r | intros kk Hk; off_windows C9' | lia | lia | ].
        eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L184.
      - eapply val_mem_frame; [exact Fr4r | intros kk Hk; off_windows C9' | lia | lia | ].
        eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L192.
      - eapply val_mem_frame; [exact Fr4r | intros kk Hk; off_windows C9' | lia | lia | ].
        eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L216. }
    intros Wz cz Wlez Hz.
    destruct Hz as (-> & rgz & mmz & mdz & bz & Ez & Jnz & Wkz & Kpz & Z6 & Z21 & Z22 & Z27 & Z19 & Z15 & Bz & Z216 & Z184 & Orz & Nrz).
    split; [reflexivity | ].
    exists rgz, mmz, mdz, bz.
    repeat (split; [first [exact Ez | exact Jnz | exact Wkz | exact Kpz | exact Z6 | exact Z21 | exact Z22 | exact Z27 | exact Z19 | exact Z15 | lia | exact Z216 | exact Z184 | exact Orz] | ]).
    intros px Hpx. destruct (Z_lt_le_dec px (i * Wd)) as [Hlo | Hhi].
    * apply Nrz. lia.
    * intros Hbad. apply (NoDiff (px - i * Wd)); [lia | ].
      replace (i * Wd + (px - i * Wd)) with px by ring. exact Hbad.
  + intros Bnt ST3b. rewrite branch_ltu_U, UT, UI1 in Bnt. apply Z.ltb_ge in Bnt.
    assert (Tis : top = i - 1) by lia.
    match type of ST3b with st_ok_pi _ _ _ ?ssb _ =>
      let v := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 30 7640 ssb) in
      lazymatch v with pair ?s4 ?t4 =>
        apply (RUNTOP W 30 7640 E1 ssb s4 t4 ms3 TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k);
        [ apply Eimg_env | exact ST3b | vm_compute; reflexivity | exact I | exact Jn3 | wscr_windows C9' | ]
      end
    end.
    intros ms5 mat5 ST5 Jn5 Fr5 Fr5r Gr5.
    apply SRr_ret. split; [reflexivity | ].
    eexists (ms_regs ms5), (ms_mem ms5), _, top.
    split; [rewrite (st_ok_pi_restrict_mkst _ _ _ _ ST5 eq_refl) at 1; reflexivity | ].
    split; [exact Jn5 | ].
    split.
    { apply (wkept_trans _ _ _ _ _ _ _ _ Wk2).
      apply (wkept_trans _ _ _ _ _ _ (ms_mem ms3)).
      - exact (WKS _ _ _ _ _ Jn2 Fr3r Gr3 ltac:(wscr_windows C9')).
      - exact (WKS _ _ _ _ _ Jn3 Fr5r Gr5 ltac:(wscr_windows C9')). }
    split; [exact (KR1 _ _ ST5 eq_refl) | ].
    split; [apply (GR1 _ _ 6%bv (SOff 6 0) _ ST5 eq_refl);
      apply U_atom; [change (ew E1 6) with (getr rg2 6); exact S6 | lia] | ].
    split; [apply (GR1 _ _ 21%bv (SOff 25 0) _ ST5 eq_refl);
      apply U_atom; [change (ew E1 25) with (getr rg2 25); exact R25 | lia] | ].
    split; [apply (GR1 _ _ 22%bv (SOff 24 0) _ ST5 eq_refl);
      apply U_atom; [change (ew E1 24) with (getr rg2 24); exact R24 | lia] | ].
    split; [apply (GR1 _ _ 27%bv (SLit 65535) _ ST5 eq_refl); rewrite U_SLit; reflexivity | ].
    split; [apply (GR1 _ _ 19%bv (SOff 33 0) _ ST5 eq_refl); exact UT | ].
    split; [apply (GR1 _ _ 15%bv (SOff 34 0) _ ST5 eq_refl); apply U_atom; [exact D34 | lia] | ].
    split; [lia | ].
    split.
    { eapply val_mem_frame; [exact Fr5r | intros kk Hk; off_windows C9' | lia | lia | ].
      eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L216. }
    split.
    { eapply val_mem_frame; [exact Fr5r | intros kk Hk; off_windows C9' | lia | lia | ].
      eapply val_mem_frame; [exact Fr3r | intros kk Hk; off_windows C9' | lia | lia | ]. exact L184. }
    split; [left; reflexivity | ].
    intros px Hpx Hbad. apply (NoDiff (px - i * Wd)); [lia | ].
    replace (i * Wd + (px - i * Wd)) with px by ring. exact Hbad.
- apply SRr_ret. split; [reflexivity | ].
  exists rg2, mm2, md2, i.
  split; [reflexivity | ].
  split; [exact Jn2 | ].
  split; [exact Wk2 | ].
  split; [exact Kp2 | ].
  split; [exact S6 | ].
  split; [exact R21 | ].
  split; [exact R22 | ].
  split; [exact R27 | ].
  split; [exact R19 | ].
  split; [exact R15 | ].
  split; [lia | ].
  split; [exact L216 | ].
  split; [exact L184 | ].
  split; [right; exists col; split; [lia | exact HPD] | ].
  intros px Hpx. lia.
Qed.
Lemma fl_s2oX : forall m, s2o_stmtX m.
Proof. induction m as [|m IH]; [unfold s2o_stmtX; intros; exfalso; lia | exact (fl_s2o_stepX m IH)]. Qed.
Definition s2s_regs := sr_set sr_atoms 10%bv (SOff 19 0).
Definition s2s_mem : smem :=
  [ YP09.mkRegion (Some 9%nat) 88 96 88 96 [];
    YP09.mkRegion (Some 9%nat) 152 176 152 176 [];
    YP09.mkRegion (Some 9%nat) 184 216 184 200
      [ YP09.mkChunk 184 (CVal 8 (SOff 19 0)); YP09.mkChunk 200 (CVal 8 (SOff 35 0)); YP09.mkChunk 208 (CVal 8 (SOff 15 0)) ] ].
Definition s2s_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (6%nat, mkAF SB SB 0); (19%nat, mkAF 0 65534 0); (15%nat, mkAF 1 65535 0);
(21%nat, HPTR 4); (22%nat, HPTR 3); (35%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s2s : sstate := mkSS 7196 s2s_regs s2s_mem None s2s_facts.
Lemma fl_s2X : forall (top : Z) (regsF : bvmap 5 word) memF mdF,
0 <= top < Hd ->
ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W memF mdF k -> wkept B lyc Sc W sp1 memc memF ->
(forall r : bv 5, In r WKEPT5 -> getr regsF r = getr regs r) ->
getr regsF 6 = Z_to_bv 64 SB -> getr regsF 21 = Z_to_bv 64 g -> getr regsF 22 = Z_to_bv 64 cfp -> getr regsF 24 = Z_to_bv 64 cfp ->
getr regsF 19 = Z_to_bv 64 top -> getr regsF 10 = Z_to_bv 64 top -> getr regsF 15 = Z_to_bv 64 Hd ->
val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 184) 8 top -> val_mem SEGS (mrestrict (w_H W) memF) (sp1 + 216) 8 bimg ->
SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + 0x1c1c)) memF (seg_rom SEGS)) mdF) (s2o_postX top (Hd - 1)).
Proof using LAWS TCMP HC HGEO HFIMG.
intros top regsF memF mdF Tp Jn Wk Kp X6 X21 X22 X24 X19 X10 X15 At184 At216.
wctx_names. wprelude Jn.
pose proof (al_blocks _ _ LAWS lyc Sc W memF mdF g CGIF_SIZE HAR Hg) as Bg.
pose proof (al_blocks _ _ LAWS lyc Sc W memF mdF cfp FRAME_SIZE HAR Hcf) as Bc.
assert (SPr : 140735332483072 + 13000 <= sp1 /\ sp1 + 384 <= sp0 /\ sp0 <= 2 ^ 47) by lia.
assert (SBv : SB = 2147450880) by reflexivity.
assert (Rq : req_size CGIF_SIZE = 96 /\ req_size FRAME_SIZE = 40) by (split; reflexivity).
assert (B9 : bv_unsigned (getr regsF 9) = sp1).
{ rewrite (Kp 9%bv) by (unfold WKEPT5; simpl; tauto). rewrite H9. apply u_Z2bv; lia. }
assert (VK : forall off v m, wkept B lyc Sc W sp1 memc m -> 0 <= off -> off + 8 <= 280 ->
  (forall kk, 0 <= kk < 8 -> ~ wscr sp1 (sp1 + off + kk)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (sp1 + off) 8 v -> val_mem SEGS (mrestrict (w_H W) m) (sp1 + off) 8 v).
{ intros off v m Hk Ho1 Ho2 Hn Hv. eapply val_mem_wkept; eauto; lia. }
set (E0 := Eimg (Ereg regsF [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 Wd])).
assert (B9' : base_val E0 (Some 9%nat) = sp1) by exact B9.
assert (EA0 : env_agree 32 (Ereg regsF [Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 Wd]) E0).
{ split; [ | reflexivity]. intros n Hn. unfold E0, Eimg. cbn [ew].
  rewrite (proj2 (Nat.leb_gt A_TEXT n)) by (unfold A_TEXT; lia). reflexivity. }
assert (GR : forall ss ms r e v, st_ok_pi SEGS VAL E0 ss (restrict (w_H W) ms) ->
  sr_get (ss_regs ss) r = e -> U E0 e = v -> getr (ms_regs ms) r = Z_to_bv 64 v).
{ intros ss ms r e v Hs He Hu. rewrite (st_ok_pi_restrict_reg _ _ _ _ r Hs), He. apply denot_of_U2. exact Hu. }
assert (KR : forall ss ms, st_ok_pi SEGS VAL E0 ss (restrict (w_H W) ms) ->
  forallb (fun q => sv_eqb (sr_get (ss_regs ss) q) (SOff (Z.to_nat (bv_unsigned q)) 0)) WKEPT5 = true ->
  forall q, In q WKEPT5 -> getr (ms_regs ms) q = getr regs q).
{ intros ss ms Hs Hb q Hq. rewrite <- (Kp q Hq). exact (regs_kept_of_st_ok_pi _ _ _ _ _ _ Hs EA0 Hb q Hq). }
assert (WKS : forall (Ex : env) (rs : smem) (m1 m2 : word -> option byte) (md1 : Model),
  ajournal SEGS B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc W m1 md1 k ->
  frame_of Ex rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  mem_grows (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall a, in_wrange Ex rs a -> wscr sp1 a) -> wkept B lyc Sc W sp1 m1 m2).
{ intros Ex rs m1 m2 md1 J1 F12 G12 Ww.
  pose proof J1 as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & P1 & _).
  apply (wkept_of_run B LAWS Ex rs lyc Sc W m1 m2 md1 sp1 A1 F12 G12 Ww); [lia | lia | intros a Ha; apply P1; lia]. }
assert (ST0 : st_ok_pi SEGS VAL E0 ss_s2s (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 7196)) memF (seg_rom SEGS)))).
{ change (restrict (w_H W) (mkst regsF (Z_to_bv 64 (BASE + 7196)) memF (seg_rom SEGS)))
    with (mkst regsF (Z_to_bv 64 (BASE + 7196)) (mrestrict (w_H W) memF) (seg_rom SEGS)).
  apply (pa_entry_st_ok_full E0 7196 s2s_regs regsF s2s_mem s2s_facts (mrestrict (w_H W) memF)).
  - unfold s2s_regs. apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | reflexivity | ].
    cbn [sv_denot]. change (ew E0 19) with (getr regsF 19). rewrite at_self, X10, X19. reflexivity.
  - reflexivity.
  - unfold s2s_mem.
    repeat apply Forall_cons; try apply Forall_nil;
      unfold region_ok; cbv beta zeta; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks]; rewrite B9';
      (split; [lia|]); (split; [lia|]); (split; [intros o Ho; apply apresent_writable; apply HSpres; lia|]).
    + constructor.
    + constructor.
    + apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ top) | apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ Wd) | apply Forall_cons; [apply (chunk_ok_val _ _ _ _ _ _ _ Hd) | apply Forall_nil]]].
      * cbn [sv_denot]. change (ew E0 19) with (getr regsF 19). rewrite at_self. exact X19.
      * cbn. lia.
      * cbn. lia.
      * exact At184.
      * cbn [sv_denot]. change (ew E0 35) with (Z_to_bv 64 Wd). rewrite at_self. reflexivity.
      * cbn. lia.
      * cbn. lia.
      * apply VK; [exact Wk | lia | lia | intros kk Hk; unfold wscr; lia | exact V200].
      * cbn [sv_denot]. change (ew E0 15) with (getr regsF 15). rewrite at_self. exact X15.
      * cbn. lia.
      * cbn. lia.
      * apply VK; [exact Wk | lia | lia | intros kk Hk; unfold wscr; lia | exact V112].
  - unfold s2s_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi].
    rewrite !B9'. repeat split; lia.
  - unfold facts_ok, s2s_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    change (ew E0 9) with (getr regsF 9). change (ew E0 6) with (getr regsF 6). change (ew E0 19) with (getr regsF 19).
    change (ew E0 15) with (getr regsF 15). change (ew E0 21) with (getr regsF 21). change (ew E0 22) with (getr regsF 22).
    change (ew E0 35) with (Z_to_bv 64 Wd).
    rewrite B9, X6, X19, X15, X21, X22, !u_Z2bv by lia.
    repeat split; try lia; try apply Z.mod_1_r.
    + exact Hsp1al.
    + exact (proj1 Bg).
    + exact (mod16_mod8 _ (proj1 Bc)). }
assert (UA : U E0 (SAlu ALU_AND (SOff 19 0) (SLit 65535)) = top).
{ rewrite (U_and_ffff_off E0 19 top 0) by (exact X19 || lia). lia. }
assert (UB : U E0 (SAlu ALU_AND (SOff 15 (-1)) (SLit 65535)) = Hd - 1).
{ rewrite (U_and_ffff_off E0 15 Hd (-1)) by (exact X15 || lia). lia. }
let v := eval vm_compute in (sym_runN_pi (@pl_tpi _ PL_asan3_0) 30 ss_s2s) in
lazymatch v with pair ?s1 ?t1 =>
  apply (RUNP W 30 E0 ss_s2s s1 t1 _ TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc mdF k);
  [ apply Eimg_env | exact ST0 | vm_compute; reflexivity | exact I | exact Jn | wscr_windows B9' | ]
end.
intros ms1 mat1 ST1 Jn1 Fr1 Fr1r Gr1.
apply (BR W E0 _ ms1 _ _ BC_GEU (SAlu ALU_AND (SOff 19 0) (SLit 65535)) (SAlu ALU_AND (SOff 15 (-1)) (SLit 65535)) ST1).
- intros Btk ST1b. rewrite branch_geu_U, UA, UB in Btk.
  assert (TH : top = Hd - 1) by (apply negb_true_iff, Z.ltb_ge in Btk; lia).
  match type of ST1b with st_ok_pi _ _ _ ?ssb _ =>
    let v := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 30 7640 ssb) in
    lazymatch v with pair ?s2 ?t2 =>
      apply (RUNTOP W 30 7640 E0 ssb s2 t2 ms1 TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k);
      [ apply Eimg_env | exact ST1b | vm_compute; reflexivity | exact I | exact Jn1 | wscr_windows B9' | ]
    end
  end.
  intros ms2 mat2 ST2 Jn2 Fr2 Fr2r Gr2.
  apply SRr_ret. split; [reflexivity | ].
  eexists (ms_regs ms2), (ms_mem ms2), _, (Hd - 1).
  split; [rewrite (st_ok_pi_restrict_mkst _ _ _ _ ST2 eq_refl) at 1; reflexivity | ].
  split; [exact Jn2 | ].
  split.
  { apply (wkept_trans _ _ _ _ _ _ _ _ Wk).
    apply (wkept_trans _ _ _ _ _ _ (ms_mem ms1)).
    - exact (WKS _ _ _ _ _ Jn Fr1r Gr1 ltac:(wscr_windows B9')).
    - exact (WKS _ _ _ _ _ Jn1 Fr2r Gr2 ltac:(wscr_windows B9')). }
  split; [exact (KR _ _ ST2 eq_refl) | ].
  split; [apply (GR _ _ 6%bv (SOff 6 0) _ ST2 eq_refl); apply U_atom; [exact X6 | lia] | ].
  split; [apply (GR _ _ 21%bv (SOff 21 0) _ ST2 eq_refl); apply U_atom; [exact X21 | lia] | ].
  split; [apply (GR _ _ 22%bv (SOff 22 0) _ ST2 eq_refl); apply U_atom; [exact X22 | lia] | ].
  split; [apply (GR _ _ 27%bv (SLit 65535) _ ST2 eq_refl); rewrite U_SLit; reflexivity | ].
  split; [apply (GR _ _ 19%bv (SOff 19 0) _ ST2 eq_refl); apply U_atom; [exact X19 | lia] | ].
  split; [apply (GR _ _ 15%bv (SOff 15 0) _ ST2 eq_refl); apply U_atom; [change (ew E0 15) with (getr regsF 15); rewrite X15; f_equal; lia | lia] | ].
  split; [lia | ].
  split.
  { eapply val_mem_frame; [exact Fr2r | intros kk Hk; off_windows B9' | lia | lia | ].
    eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At216. }
  split.
  { pose proof (st_ok_pi_region_nth _ _ _ 2 _ ST2 eq_refl) as RG2.
    apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 184 8 (SOff 19 0) top RG2 B9); [cbn; tauto | | lia | lia].
    cbn [sv_denot]. change (ew E0 19) with (getr regsF 19). rewrite at_self. exact X19. }
  split; [left; lia | ].
  intros px Hpx. lia.
- intros Bnt ST1b. rewrite branch_geu_U, UA, UB in Bnt.
  assert (TL' : top < Hd - 1) by (apply negb_false_iff, Z.ltb_lt in Bnt; lia).
  match type of ST1b with st_ok_pi _ _ _ ?ssb _ =>
    let v := eval vm_compute in (sym_run_toN_pi (@pl_tpi _ PL_asan3_0) 30 7260 ssb) in
    lazymatch v with pair ?s2 ?t2 =>
      apply (RUNTOP W 30 7260 E0 ssb s2 t2 ms1 TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(2, fpos)] lyc Sc _ k);
      [ apply Eimg_env | exact ST1b | vm_compute; reflexivity | exact I | exact Jn1 | wscr_windows B9' | ]
    end
  end.
  intros ms2 mat2 ST2 Jn2 Fr2 Fr2r Gr2.
  rewrite (st_ok_pi_restrict_mkst _ _ _ _ ST2 eq_refl).
  assert (UW : U E0 (SOff 35 0) = Wd) by (apply U_atom; [reflexivity | lia]).
  assert (UZ : U E0 (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48)) = Hd - 1)
    by (apply U_dec_zext16; [exact X15 | lia]).
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ ST2 eq_refl) as RG0.
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ ST2 eq_refl) as RG1.
  pose proof (st_ok_pi_region_nth _ _ _ 2 _ ST2 eq_refl) as RG2.
  apply (fl_s2oX (Z.to_nat (Hd - 1 - top)) (Hd - 1) top (Wd * (Hd - 1))).
  { rewrite Z2Nat.id by lia. lia. }
  { lia. }
  { exact TL'. }
  { lia. }
  { exact Jn2. }
  { apply (wkept_trans _ _ _ _ _ _ _ _ Wk).
    apply (wkept_trans _ _ _ _ _ _ (ms_mem ms1)).
    - exact (WKS _ _ _ _ _ Jn Fr1r Gr1 ltac:(wscr_windows B9')).
    - exact (WKS _ _ _ _ _ Jn1 Fr2r Gr2 ltac:(wscr_windows B9')). }
  { exact (KR _ _ ST2 eq_refl). }
  { apply (GR _ _ 6%bv (SOff 6 0) _ ST2 eq_refl). apply U_atom; [exact X6 | lia]. }
  { apply (GR _ _ 25%bv (SOff 21 0) _ ST2 eq_refl). apply U_atom; [exact X21 | lia]. }
  { apply (GR _ _ 24%bv (SOff 24 0) _ ST2 eq_refl). apply U_atom; [exact X24 | lia]. }
  { apply (GR _ _ 11%bv (SOff 35 0) _ ST2 eq_refl). exact UW. }
  { apply (GR _ _ 22%bv _ _ ST2 eq_refl). exact UZ. }
  { apply (GR _ _ 12%bv (SOff 15 (-1)) _ ST2 eq_refl).
    rewrite (U_atom_off E0 15 Hd (-1)) by (exact X15 || lia). lia. }
  { apply (GR _ _ 14%bv (SOff 15 0) _ ST2 eq_refl).
    apply U_atom; [change (ew E0 15) with (getr regsF 15); rewrite X15; f_equal; lia | lia]. }
  { apply (GR _ _ 27%bv (SLit 65535) _ ST2 eq_refl). rewrite U_SLit. reflexivity. }
  { apply (GR _ _ 18%bv (SMd M_MUL (SOff 35 0) (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 15 0) (SLit 48)) (SLit (-281474976710656))) (SLit 48))) _ ST2 eq_refl).
    rewrite U_mul_small; rewrite UW, UZ; [reflexivity | nia]. }
  { rewrite Z.mod_small by nia. ring. }
  { apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 88 8 (SOff 19 1) (top + 1) RG0 B9); [cbn; tauto | | lia | lia].
    cbn [sv_denot]. change (ew E0 19) with (getr regsF 19). rewrite X19, u_Z2bv by lia. reflexivity. }
  { apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 160 8 (SAlu ALU_AND (SOff 19 0) (SLit 65535)) top RG1 B9); [cbn; tauto | | lia | lia].
    apply denot_of_U2. exact UA. }
  { apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 184 8 (SOff 19 0) top RG2 B9); [cbn; tauto | | lia | lia].
    cbn [sv_denot]. change (ew E0 19) with (getr regsF 19). rewrite at_self. exact X19. }
  { apply (field_of_region E0 _ 9 sp1 _ _ _ _ _ 192 8 (SOff 19 0) top RG2 B9); [cbn; tauto | | lia | lia].
    cbn [sv_denot]. change (ew E0 19) with (getr regsF 19). rewrite at_self. exact X19. }
  { eapply val_mem_frame; [exact Fr2r | intros kk Hk; off_windows B9' | lia | lia | ].
    eapply val_mem_frame; [exact Fr1r | intros kk Hk; off_windows B9' | lia | lia | ]. exact At216. }
Qed.
End f.
End d.
End c.
End b.
