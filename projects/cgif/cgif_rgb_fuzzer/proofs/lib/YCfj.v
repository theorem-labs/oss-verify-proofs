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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YI02 YI01 YI03 YI04 YI06 YCfy.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YC01 YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YCcz.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB1u YCe7 YF9i YCeb YCe8 YCfq YCdv YCe5 YCe9 YCfx YCex YCev YCf8 YCfa YCfi.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma U_mul_add_ptr : forall E nh nw na h w a, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w -> ew E na = Z_to_bv 64 a ->
0 <= h < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= a -> h * w + a < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff nh 0) (SOff nw 0)) (SOff na 0)) = h * w + a.
Proof.
intros E nh nw na h w a Hh Hw Ha Rh Rw Ra Hs. assert (0 <= h * w) by (apply Z.mul_nonneg_nonneg; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E nh h Hh), (U_atom E nw w Hw), (U_atom E na a Ha) by lia.
rewrite (zcanon_id (h * w)) by (rewrite M64_val; lia). apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma denot_mul_add_ptr : forall E nh nw na h w a, ew E nh = Z_to_bv 64 h -> ew E nw = Z_to_bv 64 w -> ew E na = Z_to_bv 64 a ->
0 <= h < 2 ^ 16 -> 0 <= w < 2 ^ 16 -> 0 <= a -> h * w + a < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff nh 0) (SOff nw 0)) (SOff na 0)) = Z_to_bv 64 (h * w + a).
Proof. intros. rewrite denot_lit_U. f_equal. apply U_mul_add_ptr; assumption. Qed.
Lemma U_sltu1_pos : forall E e, 0 < U E e -> U E (SAlu ALU_SLTU e (SLit 1)) = 0.
Proof. intros E e H. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon 1) with 1. destruct (Z.ltb_spec (U E e) 1); [lia | reflexivity]. Qed.
Lemma U_xor1_sltu1 : forall E e, 0 < U E e -> U E (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU e (SLit 1))) = 1.
Proof. intros E e H. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_sltu1_pos E e H), U_SLit. reflexivity. Qed.
Lemma U_sane_flag : forall E P nb b, ew E nb = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 -> b <= U E P -> 0 < U E P ->
U E (SAlu ALU_AND (SAlu ALU_XOR (SAlu ALU_SLTU P (SOff nb 0)) (SLit (-1))) (SAlu ALU_XOR (SLit 1) (SAlu ALU_SLTU P (SLit 1)))) = 1.
Proof.
intros E P nb b Hb Rb Hle Hpos. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_xor1_sltu1 E P Hpos).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E nb b Hb Rb), U_SLit.
destruct (Z.ltb_spec (U E P) b) as [Hlt|Hge]; [lia|]. reflexivity.
Qed.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws trbsegs B.
Hypothesis TCMP : tcmp_spec B.
Ltac env_agree32 HAE :=
lazymatch goal with
| |- env_agree 32 _ (ewset ?X ?n ?v) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_ewset]]
| |- env_agree 32 _ (havoc ?X ?n ?ws) => apply (env_agree_trans 32 _ X); [env_agree32 HAE | apply (YQ04.env_agree_le 32 n); [lia | apply env_agree_havoc]]
| |- _ => exact HAE
end.
Section f.
Variables (W : world trbsegs) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (sp0 sp1 : Z) (FP : list (Z * Z))
(ly : alayout) (S : astate) (W0 : world trbsegs) (mem0 : word -> option byte) (md0 : Model) (lyc : alayout) (Sc : astate) (k : Z) (fpos : Z)
(ch1 : list (Z * Z * Z)) (fimg bimg Nb g cfp bfp : Z) (gvals cvals bvals : list Z) (gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx : Z)
(Wd Hd : Z).
Hypothesis HC : wctx B W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Hypothesis HGEO : 1 <= Wd <= 65535 /\ 1 <= Hd <= 65535 /\ Nb = Wd * Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 176) 8 Wd /\ val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 136) 8 Hd /\
val_mem trbsegs (mrestrict (w_H W) memc) (sp1 + 168) 8 fimg.
Let PDp := PD W memc fimg bimg gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx.
Ltac wctx_names :=
pose proof HC as (HJc & Hfi & Hbi & HNb & Dfb & Hg & Hcf & Hbf & Hcb & Og & Ogpal & Ongp & Oc & Ocpal & Ocattr & Ocnlp & Octidx
& Ob & Obpal & Obattr & Obnlp & Obtidx & HLc & HLb & HGp & Hsp & Hsp1 & Hsp1al & H9 & Hgp & Htp & Hch & Hs0 & Vsb & Vbfp & Vg & Vcfp);
pose proof HGEO as (RW & RH & HN & V176 & V136 & V168).
Ltac wprelude HJ :=
pose proof Hwx_tfa as Hwx; pose proof trb_segs_low as Hsegs;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof (proj1 HJ) as HAR;
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSpres & Hstk & _);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
assert (FFS : TFLUSH_STK = 17440) by reflexivity; assert (WS : TCMP_STK = 4112) by reflexivity; assert (Hes : ESTACK = 4096) by reflexivity.
Ltac efact HS n En G :=
lazymatch type of HS with st_ok _ ?Ecur _ _ => lazymatch type of En with ew _ _ = ?v =>
assert (G : ew Ecur n = v) by (rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En) end end.
Ltac rget R En :=
rewrite R; rewrite ?ew_ewset_other, ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact En.
Ltac run_ro_wkept HFr HG HARx WK WKn :=
lazymatch type of HFr with frame_of ?Ef ?rs (mrestrict _ _) (mrestrict _ _) =>
pose proof (wkept_trans B _ _ _ _ _ _ _ WK (wkept_of_run B LAWS Ef rs lyc Sc W _ _ _ sp1 HARx HFr HG
ltac:(let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; lia|]); destruct Hr)
ltac:(lia) ltac:(lia) ltac:(pose proof WK as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WKn end.
Definition WKEPT5 : list (bv 5) := [2; 3; 4; 8; 9]%bv.
Definition s1o_regs := sr_set (sr_set sr_atoms 18%bv (SLit 1)) 23%bv (SLit 1).
Definition s1o_loc : YQ0b.region :=
YQ0b.mkRegion (Some 9%nat) 136 224 136 136
[YQ0b.mkChunk 136 (CVal 8 (SOff 36 0)); YQ0b.mkChunk 152 (CVal 8 (SOff 32 0)); YQ0b.mkChunk 160 (CVal 8 (SOff 34 0)); YQ0b.mkChunk 168 (CVal 8 (SOff 33 0));
YQ0b.mkChunk 176 (CVal 8 (SOff 35 0)); YQ0b.mkChunk 192 (CVal 8 (SOff 17 0)); YQ0b.mkChunk 200 (CVal 8 (SOff 15 0)); YQ0b.mkChunk 208 (CVal 8 (SOff 16 0));
YQ0b.mkChunk 216 (CVal 8 (SOff 29 0))].
Definition s1o_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (29%nat, mkAF SB SB 0); (10%nat, mkAF 1 65535 0); (32%nat, mkAF 0 65534 0); (33%nat, HPTR 0); (34%nat, HPTR 0);
(35%nat, mkAF 1 65535 0); (36%nat, mkAF 1 65535 0); (24%nat, HPTR 0); (25%nat, HPTR 0); (26%nat, HPTR 0); (27%nat, HPTR 0);
(15%nat, HPTR 4); (16%nat, HPTR 3); (17%nat, HPTR 3) ] [] [].
Definition ss_s1o : sstate := mkSS 0x87a78 s1o_regs [s1o_loc] None s1o_facts.
Definition s1t_mem : smem :=
[ YQ0b.mkRegion (Some 9%nat) 136 144 136 136 [YQ0b.mkChunk 136 (CVal 8 (SOff 32 0))];
YQ0b.mkRegion (Some 9%nat) 152 160 152 160 [YQ0b.mkChunk 152 (CVal 8 (SOff 33 0))];
YQ0b.mkRegion (Some 9%nat) 160 168 160 160 [YQ0b.mkChunk 160 (CVal 8 (SOff 34 0))];
YQ0b.mkRegion (Some 9%nat) 176 184 176 176 [YQ0b.mkChunk 176 (CVal 8 (SOff 35 0))] ].
Definition s1t_facts : facts :=
mkFacts [ (9%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 1 65535 0); (33%nat, mkAF 0 65534 0); (35%nat, mkAF 1 65535 0) ] [] [].
Definition ss_s1t : sstate := mkSS 0x87b78 sr_atoms s1t_mem None s1t_facts.
Definition s1o_post : world trbsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md' pc',
c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom trbsegs)) md' /\
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W mem' md' k /\
wkept B lyc Sc W sp1 memc mem' /\
(forall r : bv 5, In r WKEPT5 -> getr regs' r = getr regs r) /\
((pc' = 0x87bec /\ exists top c0, 0 <= top < Hd /\ 0 <= c0 < Wd /\ PDp (top * Wd + c0) /\
getr regs' 11 = Z_to_bv 64 top /\ getr regs' 18 = Z_to_bv 64 top /\ getr regs' 24 = Z_to_bv 64 Hd /\
val_mem trbsegs (mrestrict (w_H W) mem') (sp1 + 152) 8 top /\ val_mem trbsegs (mrestrict (w_H W) mem') (sp1 + 160) 8 bimg) \/
(pc' = 0x88250 /\ getr regs' 21 = Z_to_bv 64 1 /\ getr regs' 23 = Z_to_bv 64 1 /\ getr regs' 22 = Z_to_bv 64 0 /\ getr regs' 27 = Z_to_bv 64 Wd /\
val_mem trbsegs (mrestrict (w_H W) mem') (sp1 + 152) 8 0)).
Definition s1o_stmt (m : nat) : Prop :=
forall (i : Z) (regsE : bvmap 5 word) memE mdE,
Hd - i <= Z.of_nat m -> 0 <= i < Hd ->
ajournal trbsegs B TFLUSH_STK sp0 FP ly S W0 mem0 md0 [(1, fpos)] lyc Sc W memE mdE k -> wkept B lyc Sc W sp1 memc memE ->
(forall r : bv 5, In r WKEPT5 -> getr regsE r = getr regs r) ->
getr regsE 29 = Z_to_bv 64 SB -> getr regsE 15 = Z_to_bv 64 g -> getr regsE 16 = Z_to_bv 64 cfp -> getr regsE 17 = Z_to_bv 64 bfp ->
getr regsE 26 = Z_to_bv 64 (fimg + i * Wd) -> getr regsE 24 = Z_to_bv 64 (fimg + i * Wd) ->
getr regsE 27 = Z_to_bv 64 (bimg + i * Wd) -> getr regsE 25 = Z_to_bv 64 (bimg + i * Wd) ->
getr regsE 10 = Z_to_bv 64 Wd -> getr regsE 18 = Z_to_bv 64 1 -> getr regsE 23 = Z_to_bv 64 1 ->
val_mem trbsegs (mrestrict (w_H W) memE) (sp1 + 152) 8 i -> val_mem trbsegs (mrestrict (w_H W) memE) (sp1 + 160) 8 bimg ->
SRr trbsegs W (mkCfg (mkst regsE (Z_to_bv 64 0x87a78) memE (seg_rom trbsegs)) mdE) s1o_post.
Lemma fl_s1o_step : forall m, s1o_stmt m -> s1o_stmt (Datatypes.S m).
Proof.
intros m IH. unfold s1o_stmt.
intros i regsE memE mdE Hm Hi HJE WK HKE E29r E15r E16r E17r E26r E24r E27r E25r E10r E18r E23r V152 V160.
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
destruct (al_blocks _ _ LAWS lyc Sc W memE mdE bfp FRAME_SIZE HAR Hbf) as (Hp16 & Hp4096 & Hpceil & Hpfh_ia & _ & _). pose proof (proj1 Hpfh_ia) as Hpfh.
pose proof (blk_off_img _ _ _ _ _ _ bfp FRAME_SIZE HAR Hbf) as Hpfh_img.
change (req_size CGIF_SIZE) with 96 in *. change (req_size FRAME_SIZE) with 40 in *.
pose proof (req_size_pos' Nb ltac:(lia)) as [_ HrNb].
assert (HiW : 0 <= i * Wd /\ i * Wd + Wd <= Nb) by (rewrite HN; clear - Hi RW RH; nia).
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 216 SB WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vsb) as VsbE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 192 bfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vbfp) as VbfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 200 g WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vg) as VgE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 208 cfp WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) Vcfp) as VcfpE.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 176 Wd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 136 Hd WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V136) as V136E.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memE 168 fimg WK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V168) as V168E.
remember (Ereg regsE [Z_to_bv 64 i; Z_to_bv 64 fimg; Z_to_bv 64 bimg; Z_to_bv 64 Wd; Z_to_bv 64 Hd]) as E eqn:HE.
assert (HAE : env_agree 32 (Ereg regsE [Z_to_bv 64 i; Z_to_bv 64 fimg; Z_to_bv 64 bimg; Z_to_bv 64 Wd; Z_to_bv 64 Hd]) E) by (rewrite HE; apply env_agree_refl).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsE r) by (intros n r Hn; subst E; apply ew_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl), (HKE 9%bv ltac:(cbv; tauto)); exact H9).
pose proof (EE 29%nat 29%bv eq_refl) as F29. rewrite E29r in F29.
pose proof (EE 15%nat 15%bv eq_refl) as E15. rewrite E15r in E15. pose proof (EE 16%nat 16%bv eq_refl) as E16. rewrite E16r in E16.
pose proof (EE 17%nat 17%bv eq_refl) as E17. rewrite E17r in E17.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite E26r in E26. pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite E24r in E24.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite E27r in E27. pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite E25r in E25.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite E10r in E10.
assert (E32 : ew E 32 = Z_to_bv 64 i) by (subst E; exact (ew_Ereg_extra regsE _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 fimg) by (subst E; exact (ew_Ereg_extra regsE _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 bimg) by (subst E; exact (ew_Ereg_extra regsE _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 Wd) by (subst E; exact (ew_Ereg_extra regsE _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 Hd) by (subst E; exact (ew_Ereg_extra regsE _ 4)).
assert (HS : st_ok trbsegs E ss_s1o (restrict (w_H W) (mkst regsE (Z_to_bv 64 0x87a78) memE (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_s1o, s1o_regs.
apply (rn_st_ok_any E 0x87a78 _ regsE _ _ (mrestrict (w_H W) memE)).
- subst E. apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | rewrite E18r; cbn [sv_denot]; reflexivity]
| intros X; discriminate X | rewrite E23r; cbn [sv_denot]; reflexivity].
- reflexivity.
- apply Forall_cons; [|apply Forall_nil]; unfold region_ok, s1o_loc;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val].
rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 136 8 _ Hd); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136E]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 152 8 _ i); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 168 8 _ fimg); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V168E]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176E]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 192 8 _ bfp); [cbn [sv_denot]; rewrite E17, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VbfpE]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 200 8 _ g); [cbn [sv_denot]; rewrite E15, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VgE]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 208 8 _ cfp); [cbn [sv_denot]; rewrite E16, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact VcfpE]|].
apply Forall_cons; [apply (chunk_ok_val trbsegs E _ sp1 216 8 _ SB); [cbn [sv_denot]; rewrite F29, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | unfold SB; zside | exact VsbE]|].
apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; exact I]. cbn [s1o_facts f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
rewrite E9, F29, E10, E32, E33, E34, E35, E36, E24, E25, E26, E27, E15, E16, E17, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. unfold SB. repeat match goal with |- _ /\ _ => split end; try (apply mod16_mod8; assumption);
first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HE. pose proof HS as HS0.
shok_auto SHOK (SOff 29 0) E (mrestrict (w_H W) memE).
pose proof (proj1 HJE) as HAR1.
aj_run_tok trbtbl_lib_ok HS HJE SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_wkept HFr HG HAR1 WK WK1. rename HFr into HFr1. clear HF HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
1: {
exfalso. rewrite branch_ltu_U in Hc. rewrite (U_mul_add_ptr _ 32 35 33 i Wd fimg E32 E35 E33), (U_atom _ 33 fimg E33) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
pose proof (proj1 HJE) as HAR2.
aj_run_tok trbtbl_lib_ok HS HJE SHOK FLBspan.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_wkept HFr HG HAR2 WK1 WK2. rename HFr into HFr2. clear HF HG.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
1: { exfalso. rewrite branch_eq_U in Hc. rewrite U_xor1_sltu1, U_lit in Hc by (first [rewrite (U_mul_add_ptr _ 32 35 33 i Wd fimg E32 E35 E33) by lia; lia | lia]). discriminate Hc. }
clear Hc.
pose proof (proj1 HJE) as HAR3.
aj_run_to_tok trbtbl_lib_ok HS HJE SHOK FLBspan 0x87ac0.
1: { apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
run_ro_wkept HFr HG HAR3 WK2 WK3. rename HFr into HFr3. clear HF HG.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsE _ [2; 3; 4; 8; 9; 15; 16; 17; 24; 25; 26; 27; 29]%bv HS ltac:(env_agree32 HAE) ltac:(vm_compute; reflexivity)) as HKr1. cbn [ms_regs restrict] in HKr1.
rreg HS (18%bv : bv 5) R18. rreg HS (23%bv : bv 5) R23. rreg HS (20%bv : bv 5) R20.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
efact HS 32%nat E32 G32; efact HS 33%nat E33 G33; efact HS 34%nat E34 G34; efact HS 35%nat E35 G35;
rreg_by HS (19%bv : bv 5) (Z_to_bv 64 (i * Wd + fimg)) (denot_mul_add_ptr Ev 32 35 33 i Wd fimg G32 G35 G33 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) R19;
rreg_by HS (21%bv : bv 5) (Z_to_bv 64 (i * Wd + bimg)) (denot_mul_add_ptr Ev 32 35 34 i Wd bimg G32 G35 G34 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) R21;
rreg_by HS (22%bv : bv 5) (Z_to_bv 64 1)
(eq_trans (denot_lit_U Ev _) (f_equal (Z_to_bv 64) (U_sane_flag Ev _ 34 bimg G34 ltac:(lia)
ltac:(rewrite (U_mul_add_ptr Ev 32 35 34 i Wd bimg G32 G35 G34) by lia; lia) ltac:(rewrite (U_mul_add_ptr Ev 32 35 34 i Wd bimg G32 G35 G34) by lia; lia)))) R22 end.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s1o_loc) in
pose proof (st_ok_region_nth Ex ssx msx 0 r0 HS ltac:(vm_compute; reflexivity)) as HR9; cbn [ms_mem restrict mkst] in HR9;
lazymatch type of HR9 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SOff 32 0) i HR9
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152a;
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SOff 34 0) bimg HR9
ltac:(rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; rewrite ?ew_havoc_old by lia; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160a end; clear HR9 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V152a, V160a.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ pose proof (fl_s1i B LAWS TCMP W regs memc mdc sp0 sp1 FP ly S W0 mem0 md0 lyc Sc k fpos ch1 fimg bimg Nb g cfp bfp gvals cvals bvals
gpal ngp cpal cattr cnlp ctidx bpal battr bnlp btidx Wd Hd HC HGEO (Z.to_nat Wd)) as S1I. unfold s1i_stmt in S1I.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (S1I 0 (ms_regs msX) (ms_mem msX) mdX i) end;
[ rewrite Z2Nat.id by lia; lia | lia | exact Hi | exact HJE | exact WK3
| intros r Hr; transitivity (getr regsE r); [apply HKr1; cbv [In] in Hr |- *; tauto | apply HKE; exact Hr]
| rewrite (HKr1 29%bv ltac:(cbv; tauto)); exact E29r | rewrite (HKr1 15%bv ltac:(cbv; tauto)); exact E15r
| rewrite (HKr1 16%bv ltac:(cbv; tauto)); exact E16r | rewrite (HKr1 17%bv ltac:(cbv; tauto)); exact E17r
| rewrite (HKr1 26%bv ltac:(cbv; tauto)); exact E26r | rewrite (HKr1 24%bv ltac:(cbv; tauto)); exact E24r
| rewrite R19; f_equal; lia
| rewrite (HKr1 27%bv ltac:(cbv; tauto)); exact E27r | rewrite (HKr1 25%bv ltac:(cbv; tauto)); exact E25r
| rewrite R21; f_equal; lia
| exact R20 | exact R18 | exact R22 | exact R23
| exact V152a | exact V160a ]. }
cbv beta. intros W2 c2 _ (-> & regsI & memI & mdI & pcI & -> & HJI & WKI & LI & HKI & HexI).
clear R18 R23 R20 R19 R21 R22.
assert (HK5I : forall r : bv 5, In r WKEPT5 -> getr regsI r = getr regs r).
{ intros r Hr. rewrite (HKI r) by (cbv [WKEPT5 In] in Hr; repeat (destruct Hr as [<- | Hr]; [reflexivity|]); destruct Hr).
transitivity (getr regsE r); [apply HKr1; cbv [WKEPT5 In] in Hr |- *; tauto | apply HKE; exact Hr]. }
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 152) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V152a) as V152b.
pose proof (val_mem_lkept W sp1 _ _ (sp1 + 160) 8 _ LI ltac:(lia) ltac:(cbn [Z.of_nat]; lia) V160a) as V160b.
destruct HexI as [(-> & H24I & H18I & H22I & H23I & H29I & H15I & H16I & H17I) | (-> & Hwit & H11I & H18I & H24I)].
2: {
apply SRr_ret. split; [reflexivity|]. exists regsI, memI, mdI, 0x87bec. split; [reflexivity|]. split; [exact HJI|]. split; [exact WKI|].
split; [exact HK5I|].
left. split; [reflexivity|]. destruct Hwit as (c0 & Hc0 & HPc0). exists i, c0.
split; [exact Hi|]. split; [exact Hc0|]. split; [exact HPc0|]. split; [exact H11I|]. split; [exact H18I|]. split; [exact H24I|].
split; [exact V152b | exact V160b]. }
assert (I9 : getr regsI 9 = Z_to_bv 64 sp1) by (rewrite (HKI 9%bv eq_refl), (HKr1 9%bv ltac:(cbv; tauto)); exact (eq_trans (HKE 9%bv ltac:(cbv; tauto)) H9)).
assert (I26 : getr regsI 26 = Z_to_bv 64 (fimg + i * Wd)) by (rewrite (HKI 26%bv eq_refl), (HKr1 26%bv ltac:(cbv; tauto)); exact E26r).
assert (I24 : getr regsI 24 = Z_to_bv 64 (fimg + i * Wd)) by (rewrite H24I, (HKr1 24%bv ltac:(cbv; tauto)); exact E24r).
assert (I27 : getr regsI 27 = Z_to_bv 64 (bimg + i * Wd)) by (rewrite (HKI 27%bv eq_refl), (HKr1 27%bv ltac:(cbv; tauto)); exact E27r).
assert (I25 : getr regsI 25 = Z_to_bv 64 (bimg + i * Wd)) by (rewrite (HKI 25%bv eq_refl), (HKr1 25%bv ltac:(cbv; tauto)); exact E25r).
pose proof (proj1 HJI) as HARI.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 136 Hd WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V136) as V136I.
pose proof (val_mem_wkept B lyc Sc W sp1 memc memI 176 Wd WKI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros kk Hkk; unfold wscr; lia) V176) as V176I.
assert (HSpresI : forall a, sp1 - TCMP_STK <= a < sp1 + 232 -> apresent (w_H W) memI a).
{ intros a Ha. pose proof HJI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSp & _). apply HSp. lia. }
remember (Ereg regsI [Z_to_bv 64 Hd; Z_to_bv 64 i; Z_to_bv 64 bimg; Z_to_bv 64 Wd]) as Et eqn:HEt.
assert (HAEt : env_agree 32 (Ereg regsI [Z_to_bv 64 Hd; Z_to_bv 64 i; Z_to_bv 64 bimg; Z_to_bv 64 Wd]) Et) by (rewrite HEt; apply env_agree_refl).
assert (EEt : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Et n = getr regsI r) by (intros n r Hn; subst Et; apply ew_Ereg_nat; exact Hn).
pose proof (EEt 9%nat 9%bv eq_refl) as T9. rewrite I9 in T9.
pose proof (EEt 26%nat 26%bv eq_refl) as T26. rewrite I26 in T26. pose proof (EEt 24%nat 24%bv eq_refl) as T24. rewrite I24 in T24.
pose proof (EEt 27%nat 27%bv eq_refl) as T27. rewrite I27 in T27. pose proof (EEt 25%nat 25%bv eq_refl) as T25. rewrite I25 in T25.
assert (T32 : ew Et 32 = Z_to_bv 64 Hd) by (subst Et; exact (ew_Ereg_extra regsI _ 0)).
assert (T33 : ew Et 33 = Z_to_bv 64 i) by (subst Et; exact (ew_Ereg_extra regsI _ 1)).
assert (T34 : ew Et 34 = Z_to_bv 64 bimg) by (subst Et; exact (ew_Ereg_extra regsI _ 2)).
assert (T35 : ew Et 35 = Z_to_bv 64 Wd) by (subst Et; exact (ew_Ereg_extra regsI _ 3)).
assert (HSt : st_ok trbsegs Et ss_s1t (restrict (w_H W) (mkst regsI (Z_to_bv 64 0x87b78) memI (seg_rom trbsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_s1t.
apply (rn_st_ok_any Et 0x87b78 _ regsI _ _ (mrestrict (w_H W) memI)).
- subst Et. apply regs_ok_Ereg.
- reflexivity.
- unfold s1t_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi YQ0b.r_chunks base_val]; rewrite T9, unsigned_lit_small by lia;
(split; [lia|]); (split; [lia|]); (split; [intros o Ho; first [lia | apply (apresent_writable trbsegs); apply HSpresI; lia]|]).
+ apply Forall_cons; [apply (chunk_ok_val trbsegs Et _ sp1 136 8 _ Hd); [cbn [sv_denot]; rewrite T32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V136I]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trbsegs Et _ sp1 152 8 _ i); [cbn [sv_denot]; rewrite T33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V152b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trbsegs Et _ sp1 160 8 _ bimg); [cbn [sv_denot]; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V160b]|]. apply Forall_nil.
+ apply Forall_cons; [apply (chunk_ok_val trbsegs Et _ sp1 176 8 _ Wd); [cbn [sv_denot]; rewrite T35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V176I]|]. apply Forall_nil.
- unfold s1t_mem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi base_val]. rewrite T9, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; exact I]. cbn [s1t_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite T9, T32, T33, T35, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?C3 in *. repeat match goal with |- _ /\ _ => split end; first [lia | match goal with |- ?g => idtac "FACT-LEFT" g end]. }
clear HEt. pose proof HSt as HSt0. clear HS HS0. rename HSt into HS. try clear SHOK.
shok_auto SHOK (SOff 29 0) Et (mrestrict (w_H W) memI).
aj_run_tok trbtbl_lib_ok HS HJI SHOK FLBspan.
1: { unfold s1t_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite T9; apply unsigned_lit_small; lia | cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr4. rename HG into HG4. clear HF.
assert (W4 : forall a, in_wrange Et (ss_mem ss_s1t) a -> wscr sp1 a).
{ unfold ss_s1t, s1t_mem; cbn [ss_mem]. intros a (r & Hr & Hw); cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr]; [(cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; rewrite T9, unsigned_lit_small in Hw by lia; unfold wscr; lia) |]); destruct Hr. }
pose proof (wkept_trans B _ _ _ _ _ _ _ WKI (wkept_of_run B LAWS Et _ lyc Sc W memI _ mdI sp1 HARI HFr4 HG4 W4 ltac:(lia) ltac:(lia) HSpresI)) as WK4.
srr_branch_tok trbtbl_lib_ok HS SHOK FLBspan.
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 33 i 1 T33), (U_atom _ 32 Hd T32) in Hc by lia.
apply (proj1 (negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
pose proof (proj1 HJI) as HAR5.
aj_run_to_tok trbtbl_lib_ok HS HJI SHOK FLBspan 0x87a78.
1: { unfold s1t_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia | cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr5. rename HG into HG5. clear HF.
lazymatch type of HFr5 with frame_of ?Ef ?rsf _ _ =>
assert (W5 : forall a, in_wrange Ef rsf a -> wscr sp1 a) by
(cbn [ss_mem]; intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [(cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; unfold wscr; lia) |]); destruct Hr) end.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK4 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 W5 ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsI _ [2; 3; 4; 8; 9; 15; 16; 17; 18; 23; 29]%bv HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr5. cbn [ms_regs restrict] in HKr5.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YQ0b.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SOff 33 1) (i + 1) HR1
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(rewrite denot_lit_U; f_equal; apply (U_atom_off Ex 33 i 1); [cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; exact T33 | lia | lia])
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152n end; clear HR1;
let r2 := eval vm_compute in (nth 2 (ss_mem ssx) (YQ0b.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2; cbn [ms_mem restrict mkst] in HR2;
lazymatch type of HR2 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 160 8%N (SOff 34 0) bimg HR2
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(cbn [sv_denot]; cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V160n end; clear HR2 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V152n, V160n.
rreg HS (10%bv : bv 5) R10.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
efact HS 26%nat T26 GT26; efact HS 24%nat T24 GT24; efact HS 27%nat T27 GT27; efact HS 25%nat T25 GT25; efact HS 35%nat T35 GT35;
rreg_by HS (26%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd + Wd)) (denot_add_atoms Ev 26 35 (fimg + i * Wd) Wd GT26 GT35 ltac:(lia) ltac:(lia) ltac:(lia)) R26;
rreg_by HS (24%bv : bv 5) (Z_to_bv 64 (fimg + i * Wd + Wd)) (denot_add_atoms Ev 24 35 (fimg + i * Wd) Wd GT24 GT35 ltac:(lia) ltac:(lia) ltac:(lia)) R24;
rreg_by HS (27%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd + Wd)) (denot_add_atoms Ev 27 35 (bimg + i * Wd) Wd GT27 GT35 ltac:(lia) ltac:(lia) ltac:(lia)) R27;
rreg_by HS (25%bv : bv 5) (Z_to_bv 64 (bimg + i * Wd + Wd)) (denot_add_atoms Ev 25 35 (bimg + i * Wd) Wd GT25 GT35 ltac:(lia) ltac:(lia) ltac:(lia)) R25 end.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_mono.
{ eapply (IH (i + 1) _ _ _); [ lia | lia | exact HJI | exact WK5
| intros r Hr; transitivity (getr regsI r); [apply HKr5; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]
| rewrite (HKr5 29%bv ltac:(cbv; tauto)); exact H29I | rewrite (HKr5 15%bv ltac:(cbv; tauto)); exact H15I
| rewrite (HKr5 16%bv ltac:(cbv; tauto)); exact H16I | rewrite (HKr5 17%bv ltac:(cbv; tauto)); exact H17I
| rewrite R26; f_equal; lia | rewrite R24; f_equal; lia | rewrite R27; f_equal; lia | rewrite R25; f_equal; lia
| rget R10 T35
| rewrite (HKr5 18%bv ltac:(cbv; tauto)); exact H18I | rewrite (HKr5 23%bv ltac:(cbv; tauto)); exact H23I
| exact V152n | exact V160n ]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & pc3 & -> & HJ3 & WK6 & HK3 & Hex).
split; [reflexivity|]. exists regs3, mem3, md3, pc3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact WK6|].
split; [exact HK3 | exact Hex].
-
rewrite branch_ne_U in Hc. rewrite (U_atom_off _ 33 i 1 T33), (U_atom _ 32 Hd T32) in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
pose proof (proj1 HJI) as HAR5.
aj_run_to_tok trbtbl_lib_ok HS HJI SHOK FLBspan 0x88250.
1: { unfold s1t_mem.
repeat (first [ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia | cbn [YQ0b.r_wlo YQ0b.r_whi]; intros a Ha; left; rewrite FFS; lia |] ]). }
rename HFr into HFr5. rename HG into HG5. clear HF.
lazymatch type of HFr5 with frame_of ?Ef ?rsf _ _ =>
assert (W5 : forall a, in_wrange Ef rsf a -> wscr sp1 a) by
(cbn [ss_mem]; intros a (r & Hr & Hw); lazymatch type of Hr with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hr end; cbn [In] in Hr;
repeat (destruct Hr as [<- | Hr]; [(cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw; rewrite ?ew_ewset_other in Hw by lia; rewrite T9, unsigned_lit_small in Hw by lia; unfold wscr; lia) |]); destruct Hr) end.
pose proof (wkept_trans B _ _ _ _ _ _ _ WK4 (wkept_of_run B LAWS _ _ lyc Sc W _ _ _ sp1 HAR5 HFr5 HG5 W5 ltac:(lia) ltac:(lia) ltac:(pose proof WK4 as [(_ & _ & _ & _ & _ & K6) _]; exact K6))) as WK5.
pose proof (regs_kept_of_st_ok trbsegs _ _ _ regsI _ [2; 3; 4; 8; 9]%bv HS ltac:(env_agree32 HAEt) ltac:(vm_compute; reflexivity)) as HKr5. cbn [ms_regs restrict] in HKr5.
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (YQ0b.mkRegion None 0 0 0 0 [])) in
pose proof (st_ok_region_nth Ex ssx msx 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1; cbn [ms_mem restrict mkst] in HR1;
lazymatch type of HR1 with region_ok _ _ _ (YQ0b.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex _ 9 sp1 cs lo hi wlo whi 152 8%N (SLit 0) 0 HR1
ltac:(cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite T9; apply unsigned_lit_small; lia) ltac:(cbn; tauto)
ltac:(reflexivity) ltac:(cbn [Z.of_N Z.mul]; lia) ltac:(cbn; lia)) as V152n end; clear HR1 end.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in V152n.
rreg HS (21%bv : bv 5) R21. rreg HS (23%bv : bv 5) R23. rreg HS (22%bv : bv 5) R22. rreg HS (27%bv : bv 5) R27.
rewrite (st_ok_restrict_mkst trbsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx, 0x88250 end.
split; [reflexivity|]. split; [exact HJI|]. split; [exact WK5|].
split; [intros r Hr; transitivity (getr regsI r); [apply HKr5; cbv [WKEPT5 In] in Hr |- *; tauto | apply HK5I; exact Hr]|].
right. split; [reflexivity|]. split; [exact R21|]. split; [exact R23|]. split; [exact R22|]. split; [rget R27 T35 | exact V152n].
Qed.
Lemma fl_s1o : forall m, s1o_stmt m.
Proof. induction m as [|m IH]; [unfold s1o_stmt; intros; exfalso; lia | exact (fl_s1o_step m IH)]. Qed.
End f.
End d.
End c.
