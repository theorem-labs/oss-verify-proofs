(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YB1v YCef YF0l YCej YCeh YCem YCei YCep YCeo YCes YCew YCex YCey.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Set Hyps Limit 8. Set Printing Depth 14. Set Printing Width 250.
Ltac keStepS HF HFr HG KE PR Zs Zsm Usp B10 Hsp UN :=
unrunRD HFr Zsm Usp B10 Hsp UN; clear HF HFr; prStep HG PR;
first
[ lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
lazymatch type of UN with forall a, _ -> _ -> aview ?sg ?Hh ?m2 a = aview _ _ m1 a =>
let KE2 := fresh "KE" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg Hh m2 a = aview sg Hh m0 a)
by (intros a' Ha' Hn'; rewrite (UN a' Ha' ltac:(intros X; apply Hn'; revert X; cbv delta [Zs Zsm]; cbn beta; clear; unfold TRFC_STK, ASTACK; intros X; lia)); exact (KE a' Ha' Hn'));
clear KE; rename KE2 into KE end end
|
lazymatch type of UN with forall a, _ -> _ -> aview ?sg ?Hh ?m2 a = aview _ _ ?m1 a =>
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg Hh m2 a = aview sg Hh m1 a)
by (intros a' Ha' Hn'; exact (UN a' Ha' ltac:(intros X; apply Hn'; revert X; cbv delta [Zs Zsm]; cbn beta; clear; unfold TRFC_STK, ASTACK; intros X; lia))) end ].
Ltac dkeep D UN dtac :=
lazymatch type of UN with forall a, _ -> _ -> aview ?sg ?Hh ?m2 a = _ =>
let D2 := fresh "D" in
assert (D2 : forall i, 0 <= i < 16 -> aview sg Hh m2 (_ + i) = Some 0) by (intros i Hi; rewrite (UN (_ + i)); [exact (D i Hi) | dtac | dtac]);
clear D; rename D2 into D end.
Ltac rkeep RD H2 m2 etac :=
lazymatch type of RD with ?rk = 0 -> forall i, 0 <= i < ?nk -> aview _ ?Hh ?m (?a + i) = aview _ ?Hc ?mc (?pb + (?o + i)) =>
let RD2 := fresh "RD" in
assert (RD2 : rk = 0 -> forall i, 0 <= i < nk -> aview tfibsegs H2 m2 (a + i) = aview tfibsegs Hc mc (pb + (o + i)))
by (let Hz := fresh "Hz" in intros Hz i Hi; rewrite <- (RD Hz i Hi); etac);
clear RD; rename RD2 into RD
| ?ty => fail "rkeep: unexpected shape" ty end.
Ltac dhkeep DH H2 m2 etac :=
lazymatch type of DH with forall i, ?hole -> aview _ ?Hh ?m (?a + i) = Some 0 =>
let D2 := fresh "DH" in
assert (D2 : forall i, hole -> aview tfibsegs H2 m2 (a + i) = Some 0)
by (intros i Hi; rewrite <- (DH i Hi); etac);
clear DH; rename D2 into DH
| ?ty => fail "dhkeep: unexpected shape" ty end.
Ltac vkeep V H2 m2 etac :=
lazymatch type of V with val_mem _ (mrestrict ?Hh ?m) ?a ?n ?v =>
let V2 := fresh "V" in
assert (V2 : val_mem tfibsegs (mrestrict H2 m2) a n v) by (apply (val_mem_kept Hh H2 m m2 a n v V); intros i Hi; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hi; etac);
clear V; rename V2 into V end.
Ltac vkeepUN UN Vp Vn Vc ztac :=
lazymatch type of UN with forall a, _ -> _ -> aview _ ?H2 ?m2 a = _ =>
vkeep Vp H2 m2 ltac:(apply UN; ztac); vkeep Vn H2 m2 ltac:(apply UN; ztac); vkeep Vc H2 m2 ltac:(apply UN; ztac) end.
Ltac oblDST RA E11x E32x :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff 11 ?c)) _ =>
rewrite (U_atom_off Ex 11 _ c ltac:(enorm; agnorm; exact E11x)) by lia;
eapply obl_of_range; [exact RA | rewrite (U_atom Ex 32 SB ltac:(enorm; agnorm; exact E32x)) by (unfold SB; lia); reflexivity | lia | lia] end.
Ltac keStepD HF HFr HG KE PR D Zs Zsm Usp B10 Hsp dtac :=
let UN := fresh "UN" in
unrunRD HFr Zsm Usp B10 Hsp UN; clear HF HFr; prStep HG PR;
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = aview _ _ ?m0 a =>
lazymatch type of UN with forall a, _ -> _ -> aview ?sg ?Hh ?m2 a = aview _ _ m1 a =>
let KE2 := fresh "KE" in let D2 := fresh "D" in
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg Hh m2 a = aview sg Hh m0 a)
by (intros a' Ha' Hn'; rewrite (UN a' Ha' ltac:(intros X; apply Hn'; revert X; cbv delta [Zs Zsm]; cbn beta; clear; unfold TRFC_STK, ASTACK; intros X; lia)); exact (KE a' Ha' Hn'));
clear KE; rename KE2 into KE;
assert (D2 : forall i, 0 <= i < 16 -> aview sg Hh m2 (_ + i) = Some 0)
by (intros i Hi; rewrite (UN (_ + i)); [exact (D i Hi) | dtac | dtac]);
clear D UN; rename D2 into D end end.
Ltac renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n :=
try clear E10n; try clear E11n; try clear E32n; try clear Uspn; try clear B10n; try clear B11n;
lazymatch type of HS with st_ok _ ?Ev _ _ =>
lazymatch type of E10 with _ = ?v => assert (E10n : ew Ev 10 = v) by (rewrite (AG 10%nat) by lia; exact E10) end;
lazymatch type of E11 with _ = ?v => assert (E11n : ew Ev 11 = v) by (rewrite (AG 11%nat) by lia; exact E11) end;
lazymatch type of E32 with _ = ?v => assert (E32n : ew Ev 32 = v) by (rewrite (AG 32%nat) by lia; exact E32) end;
lazymatch type of Usp with _ = ?v => assert (Uspn : bv_unsigned (ew Ev 2) = v) by (rewrite (AG 2%nat) by lia; exact Usp) end;
assert (B10n : bv_unsigned (ew Ev 10) = st) by (rewrite E10n; apply unsigned_lit_small; lia);
assert (B11n : bv_unsigned (ew Ev 11) = dst) by (rewrite E11n; apply unsigned_lit_small; lia) end.
Ltac reseatL HS HJ2 HP2 keep AG kept_tac :=
let K := lazymatch type of HS with st_ok _ _ ?ss _ => eval vm_compute in (run_K 0 (SOff 32 0) [] ss) end in
let HS2 := fresh "HS2" in
lazymatch type of HJ2 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?W2 ?mem2 _ _ =>
lazymatch type of HP2 with aregs_preserved _ ?regs2 =>
jafter_call_keep HS K regs2 (mrestrict (w_H W2) mem2) HP2 keep HS2 end end;
match type of HS2 with ?Q -> _ =>
let HQ := fresh "HQ" in
assert (HQ : Q); [ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil; kept_tac | specialize (HS2 HQ); clear HQ ] end;
clear HS; rewrite <- restrict_mkst_fx in HS2; rename HS2 into HS;
let AG2 := fresh "AG" in let Ev := fresh "E" in let HEv := fresh "HE" in
lazymatch type of AG with forall n, _ -> _ = ew ?E0 n =>
lazymatch type of HS with st_ok _ ?Enew _ _ =>
remember Enew as Ev eqn:HEv in HS;
assert (AG2 : forall n, (n < 33)%nat -> ew Ev n = ew E0 n)
by (intros nn Hnn; rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; apply AG; exact Hnn);
repeat match goal with H : ew ?Eo ?n = ?v |- _ =>
lazymatch Eo with
| Ev => fail
| _ => lazymatch (eval cbv in (Nat.leb 33 n)) with
| true => let H2 := fresh H in
assert (H2 : ew Ev n = v) by (rewrite HEv; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; exact H);
clear H; rename H2 into H
end end end;
clear HEv AG; rename AG2 into AG end end.
Lemma denot_mul3 : forall E n i, ew E n = Z_to_bv 64 i -> 0 <= i < 2 ^ 16 ->
sv_denot E (SMd M_MUL (SOff n 0) (SLit 3)) = Z_to_bv 64 (3 * i).
Proof.
intros E n i Hn Hi. rewrite denot_lit_U. f_equal. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E n i Hn) by lia. rewrite U_SLit. rewrite (zcanon_id 3) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma U_attr_bit : forall E n fattr, ew E n = Z_to_bv 64 fattr -> 0 <= fattr < 2 ^ 32 ->
U E (SAlu ALU_AND (SExt false 8 (SOff n 0)) (SLit 1)) = Z.land fattr 1.
Proof.
intros E n fattr Hn Hf. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit, (U_atom E n fattr Hn) by lia. cbn [Z.of_N].
change (2 ^ 8) with 256. pose proof (Z.mod_pos_bound fattr 256 ltac:(lia)) as Hm.
rewrite (zcanon_id (fattr mod 256)) by (unfold M64; lia). rewrite (zcanon_id 1) by (unfold M64; lia).
assert (L1 : forall x, 0 <= x -> Z.land x 1 = x mod 2) by (intros x Hx; change 1 with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
rewrite !L1 by lia. rewrite zcanon_id by (unfold M64; pose proof (Z.mod_pos_bound (fattr mod 256) 2 ltac:(lia)); lia).
apply Z.mod_mod_divide. exists 128. reflexivity.
Qed.
Definition dst_regionA (K : nat) : YP09.region :=
YP09.mkRegion (Some 11%nat) 0 32 0 16
[YP09.mkChunk 0 (CZero 16); YP09.mkChunk 16 (CVal 4 (SOff K 0)); YP09.mkChunk 20 (CVal 4 (SOff (K + 1) 0));
YP09.mkChunk 24 (CVal 2 (SOff (K + 2) 0)); YP09.mkChunk 26 (CVal 2 (SOff (K + 3) 0)); YP09.mkChunk 28 (CVal 1 (SOff (K + 4) 0))].
Lemma rfcA_Z_lor_bound : forall x y n, 0 <= n -> 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n -> 0 <= Z.lor x y < 2 ^ n.
Proof.
intros x y n Hn Hx Hy. pose proof (proj2 (Z.lor_nonneg x y) ltac:(lia)) as Hnn. split; [exact Hnn|].
destruct (Z.eq_dec x 0) as [->|Hx0]; [rewrite Z.lor_0_l; lia|].
destruct (Z.eq_dec y 0) as [->|Hy0]; [rewrite Z.lor_0_r; lia|].
assert (Hp : 0 < Z.lor x y).
{ destruct (Z.eq_dec (Z.lor x y) 0) as [H0|H0]; [|lia]. apply Z.lor_eq_0_iff in H0. lia. }
apply Z.log2_lt_pow2; [exact Hp|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.
Lemma rfcA_alu_or_lits : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
alu64 ALU_OR (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof.
intros x y Hx Hy. set (E0 := mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])).
change (alu64 _ _ _) with (sv_denot E0 (SAlu ALU_OR (SLit x) (SLit y))).
rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite !U_SLit. rewrite (zcanon_id x), (zcanon_id y) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; apply rfcA_Z_lor_bound; lia). reflexivity.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section RA.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes tfibsegs B OSet A_asan_memset_tfb.
Hypothesis AMEMCPY : aintrin_realizes tfibsegs B OCpy A_asan_memcpy_tfb.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule tfibsegs B MT.
Let HBcode := tl_code B TL. Let errno_low := tl_env B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Lemma rfc_A_ok : RFC_I_stmt B MT -> trfc_specX B MT.
Proof.
intros RI. unfold trfc_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos ch T P
HJ Hsub HPerm Hpd Hra Hra4 Hgp Htp G10 G11 G12 Hch Hctx Hal16 Hwlo Hwhi Hown Hcid Hfal Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 RAst RAdst HN Hcur Hnb Wp Wn Wc Hev Hlive
HPL HlenP HMOK HCOST.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (HTS : TRFC_STK = 112 + ASTACK) by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (ESTACK = 4096) as Hes by reflexivity.
assert (HEV : EV_RFC = 6) by reflexivity.
assert (Hpdc : In (pdata, nb) (ablocks B lyc Sc)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hpd]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb HAR Hpdc) as (Hp16 & Hp4096 & Hpceil & [Hph Hpapp] & Hppres & _ & HnbM).
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp. rbox Hpapp. rbox Hph_img || idtac.
pose proof (blk_off_img _ _ _ _ _ _ pdata nb HAR Hpdc) as Hph_img.
pose proof (req_size_pos nb ltac:(lia)) as [Hrq1 Hrq2]. unfold MALLOC_MAX in HnbM.
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & [HFhi1 HFhi2] & HFpres & HFSpres). ceil; unfold ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFhi2. pose proof (fs_frame_bytes_nonneg cid) as HFB.
pose proof (frm_off_img _ _ _ _ _ _ _ _ HAR Hfin) as HFhi2_img.
assert (HFceil : frame_addr lyc cid pos + fs_frame_bytes cid <= alloc_ceiling) by (clear - HFhi2 C1; lia).
assert (HlyF : ly_F lyc = ly_F ly) by (destruct Hly as (_ & _ & _ & _ & _ & -> & _); reflexivity).
assert (HSPB : alloc_ceiling <= spZ regs - TRFC_STK /\ spZ regs <= 2 ^ 47) by (clear - Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0; lia).
assert (Hsd : rboxed (st + 24 <= dst \/ dst + 32 <= st)) by (unfold rboxed; right; clear - Hst1 HSPB Hdst2 HFhi2 HTS Has C1; lia).
assert (HSTB : spZ regs <= st /\ st + 24 <= 2 ^ 47 /\ alloc_ceiling <= st) by (clear - Hst1 Hst2 Hwlo Hwhi Hceil Hslo Hshi H47 Hstk0 HTS Has C1; lia).
assert (HDSTB : (4096 <= dst /\ (dst + 32 <= 65536 \/ 6270976 <= dst) /\ (dst + 32 <= 2147446784 \/ 17594333495296 <= dst)) /\ dst + 32 <= alloc_ceiling) by (try generalize HFhi2_img; clear - Hdst1 Hdst2 HFhi1 HFhi2 C1 C3; unfold off_img; intros; lia).
assert (HSEP : rfc_sep (spZ regs) Bb lyc Sc st dst) by (eapply (rfc_sep_intro B LAWS); [exact HAR | exact HPerm | exact Hfin | clear - Hst1 HSPB HTS Has C1; lia | exact Hdst1 | exact Hdst2 | clear - HDSTB; lia]).
assert (RC : rfc_cx B MT STK sp0 FP ly S own lyc Sc k regs Bb st dst N pdata nb cur cid pos T P).
{ unfold rfc_cx. repeat match goal with |- _ /\ _ => split end; try assumption; first [clear - HN Hcur Hpceil HnbM C1; lia | unfold rboxed in Hpapp, Hph_img; clear - HFhi1 HFhi2 HFhi2_img Hph Hpapp Hph_img Hp4096 Hrq1 Hrq2 C1 C3; unfold off_img in *; lia]. }
pose proof (mo_le_refl MT MTL Sc : mo_le MT Sc Sc 0) as HMLE. pose proof (Z.le_refl 0 : 0 <= 0) as Hacc.
assert (HDST0 : 4096 <= dst) by (clear - HDSTB; lia). assert (HDSTC : dst + 32 <= alloc_ceiling) by (clear - HDSTB; lia).
assert (HDSTI : dst + 32 <= 65536 \/ 6270976 <= dst) by (clear - HDSTB; lia). rbox HDSTI.
assert (HDSTH : dst + 32 <= 2147446784 \/ 17594333495296 <= dst) by (clear - HDSTB; lia). rbox HDSTH.
clear HDSTB. rbox HFhi2. rbox HFhi2_img.
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ pdata nb cid pos HAR Hpdc Hfin) as Hpdst. unfold zdisjoint in Hpdst. cbn [fst snd] in Hpdst. rbox Hpdst.
remember (Ereg regs (rfc_extra pdata nb cur)) as E eqn:HE.
pose proof (rfc_entry B TL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
HJ HPerm Hpd G10 G11 G12 Hal16 Hwlo Hwhi Hown Hcid Hdst1 Hdst2 Hdst8 Hst1 Hst2 Hst8 HN Hcur Hnb Wp Wn Wc) as HS. rewrite <- HE in HS.
assert (HAE : env_agree 32 (Ereg regs (rfc_extra pdata nb cur)) E) by (rewrite HE; split; [intros m Hm; reflexivity | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Ereg_nat; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (exact (EE 1%nat 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 st) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 dst) by (rewrite (EE 11%nat 11%bv eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 N) by (rewrite (EE 12%nat 12%bv eq_refl); exact G12).
assert (E3 : ew E 3 = Z_to_bv 64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = Z_to_bv 64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (EX : forall j, ew E (32 + j) = nth j (rfc_extra pdata nb cur) (Z_to_bv 64 0)) by (intros j; rewrite HE; apply ew_Ereg_extra).
pose proof (EX 0%nat) as E32. pose proof (EX 1%nat) as E33. pose proof (EX 2%nat) as E34. pose proof (EX 3%nat) as E35.
cbn [Nat.add nth rfc_extra map app] in E32, E33, E34, E35. clear EX.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (B10 : bv_unsigned (ew E 10) = st) by (rewrite E10; apply unsigned_lit_small; lia).
assert (B11 : bv_unsigned (ew E 11) = dst) by (rewrite E11; apply unsigned_lit_small; lia).
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by (intros; reflexivity).
clear HE.
set (Zs := fun a : Z => spZ regs - TRFC_STK <= a < spZ regs \/ dst <= a < dst + 32 \/ st + 16 <= a < st + 24).
assert (ZB : forall a, SB <= a < kHighShadowEnd -> ~ Zs a).
{ intros a Ha. subst Zs. cbn beta. clear - Ha HSPB HSTB HDST0 HDSTH HTS Has C1 C2 C3 C4 C5. unfold rboxed in HDSTH. unfold SB in Ha. lia. }
reshok_bx HS 32%nat.
unfold cfg_at. change (w64 A_read_frameconfig) with (Z_to_bv 64 A_read_frameconfig).
change memc with (ms_mem (mkst regs (Z_to_bv 64 A_read_frameconfig) memc (seg_rom tfibsegs))) in HJ.
assert (EFA0 : forall c p, frame_addr lyc c p = frame_addr lyc c p) by reflexivity.
set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs).
aj_run_tok tfibtbl_lib_ok HS HJ SHOK RBspan.
{ awrRFC Usp E10 E11 Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UN0.
vkeepUN UN0 Wp Wn Wc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UN0.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
change (Z_to_bv 64 334504) with (Z_to_bv 64 A_asan_memset_tfb).
shkOf KE ZB SHK.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_intrin_at_io B LAWS OSet A_asan_memset_tfb AMEMSET _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc _ k dst 0 32 (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_MS) HJ);
[ rewrite Ra0, E11; reflexivity
| rewrite Ra1; reflexivity
| rewrite Ra2; reflexivity
| lia | lia | lia
| unfold spZ; rewrite Rsp; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| unfold ESTACK; clear - Hwlo HTS Has; lia
| rewrite Rgp, E3; reflexivity
| rewrite Rtp, E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; lia] | unfold ESTACK; clear - Ha HSPB HDST0 HDSTC C1 HTS Has; lia]
| apply amem_range_high; [clear; lia | clear - HDSTH; unfold rboxed in HDSTH; lia | clear - HDSTC; lia]
| apply (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst)
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc Sc W _ _ cid pos dst 32 (proj1 HJ) Hfin); lia
| exact I ] end. }
cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & -> & HJ1 & HP1 & Ha01 & Heff1 & Hfr1 & Hpres1 & Hio1).
assert (HIOc : same_io mdc md1) by (io_after Hio1). clear Hio1.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr1 by lia.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp SHK.
reseatL HS HJ1 HP1 [0; 1; 2]%nat AG
ltac:(first [ eapply region_kept_aview; [evalER AG | intros a Ha; apply Hfr1; [clear - Ha HSPB HSTB HDST0 HDSTC HTS Has C1 C3; lia | clear - Ha HSPB HSTB HDST0 HDSTC Hsd HTS Has; unfold rboxed in Hsd; lia | clear - Ha HSPB HSTB HDST0 HDSTC HTS Has; unfold ESTACK; lia] | exact Hpres1]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = _ =>
assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite <- (KE a Ha Hna); apply (Hfr1 a Ha); clear - Hna Hes HTS Has; subst Zs; cbn beta in *; lia) end.
clear KE. rename KE1 into KE.
assert (PR1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem1 a) by (intros a' Ha'; exact (Hpres1 a' (PR a' Ha'))). clear PR. rename PR1 into PR.
vkeep Wp (w_H W) mem1 ltac:(apply Hfr1; [clear - Hi HSTB C1; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi Hst1 Hes; lia]).
vkeep Wn (w_H W) mem1 ltac:(apply Hfr1; [clear - Hi HSTB C1; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi Hst1 Hes; lia]).
vkeep Wc (w_H W) mem1 ltac:(apply Hfr1; [clear - Hi HSTB C1; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi Hst1 Hes; lia]).
rename Wp into Vp. rename Wn into Vn. rename Wc into Vc.
assert (D16 : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem1 (dst + i) = Some 0) by (intros i Hi; rewrite (Heff1 i ltac:(lia)); reflexivity).
assert (DH : forall i, (i = 2 \/ i = 3 \/ i = 6 \/ i = 7) -> aview tfibsegs (w_H W) mem1 (dst + 16 + i) = Some 0)
by (intros i Hi; replace (dst + 16 + i) with (dst + (16 + i)) by (clear; lia); rewrite (Heff1 (16 + i) ltac:(clear - Hi; lia)); reflexivity).
clear Heff1 Hfr1 Hpres1 Ha01 E33 E34 E35.
norm_ss HS. renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan A_readdata.
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
dkeep D16 UNs ltac:(first [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ => dhkeep DH (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UNs.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
st (dst + 16) 2 pdata nb cur (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_RD1));
[ exact HJ1
| rewrite Ra0; enorm; agnorm; rewrite E10; reflexivity
| rewrite Ra1; enorm; agnorm; rewrite E11, unsigned_lit_small by lia; reflexivity
| rewrite Ra2; reflexivity
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has Hes; lia
| exact Hst8
| clear - Hst1; lia
| exact Hst2
| exact RAstN
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpdc] | clear - Hcur; lia
| lia | lia
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia] | clear - Ha HSPB HDST0 HDSTC C1 HTS Has Hes; lia]
| apply amem_range_high; [clear; lia | clear - HDSTH; unfold rboxed in HDSTH; lia | clear - HDSTC; lia]
| eapply range_addressable_sub; [exact RAdstN | lia | lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc Sc W _ _ cid pos (dst + 16) 2 (proj1 HJ1) Hfin); clear - Hdst1 Hdst2; lia
| clear - Hsd; unfold rboxed in Hsd; lia
| clear - Hpdst Hdst1 Hdst2 Hrq2; unfold rboxed in Hpdst; lia ] end. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & r1 & cur1 & -> & HJ2 & HP2 & Ha02 & Hr1 & Vp' & Vn' & Vc' & Hfr2 & Hpres2 & Hio2).
assert (HIOc' : same_io mdc md2) by (io_after Hio2). clear Hio2 HIOc. rename HIOc' into HIOc.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr2 by lia.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstN RAdstN Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb1 : cur <= cur1 <= nb) by (clear - Hr1 Hcur Hnb; destruct Hr1 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc1 : rboxed ((r1 = 0 /\ cur1 = cur + 2 /\ cur + 2 <= nb) \/ (r1 = 2 ^ 64 - 1 /\ cur1 = nb /\ nb < cur + 2))) by (clear - Hr1; unfold rboxed; destruct Hr1 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left; split; [exact A1 | split; [exact A2 | exact X]] | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD1 : r1 = 0 -> forall i, 0 <= i < 2 -> aview tfibsegs (w_H W) mem2 (dst + 16 + i) = aview tfibsegs (w_H W) memc (pdata + ((cur + 0) + i))).
{ intros Hz i Hi. destruct Hr1 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp i Hi).
replace (pdata + cur + i) with (pdata + ((cur + 0) + i)) by (clear; lia).
apply KE; [clear - Hi Hle Hph Hpceil Hcur Hnb Hrq2  C1; unfold rboxed in *; lia | subst Zs; cbn beta; clear - Hi Hle Hcur Hnb Hrq2 Hpdst Hdst1 Hdst2 Hst1 Hpceil HSPB HSTB HTS Has  C1; unfold rboxed in *; lia]. }
clear Hr1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ1)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
reseatL HS HJ2 HP2 [0; 1; 2]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr2;
[ clear - Ha HSPB HTS Has C1; lia
| clear - Ha HSPB HDST0 HDSTC HTS Has C1; lia
| clear - Ha Hst1; lia
| clear - Ha; unfold ESTACK; lia ]
| exact Hpres2 ]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = _ =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite <- (KE a Ha Hna); apply (Hfr2 a Ha); clear - Hna Hes HTS Has; subst Zs; cbn beta in *; lia) end.
clear KE. rename KE2 into KE.
assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem2 a) by (intros a' Ha'; exact (Hpres2 a' (PR a' Ha'))). clear PR. rename PR2 into PR.
assert (D16' : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem2 (dst + i) = Some 0)
by (intros i Hi; rewrite (Hfr2 (dst + i)); [exact (D16 i Hi) | clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear D16. rename D16' into D16.
dhkeep DH (w_H W) mem2 ltac:(apply Hfr2; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear Hfr2 Hpres2 HJ1 HP2.
renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
rreg HS (10%bv : bv 5) Rr1. cbn [ms_regs] in Rr1. rewrite Ha02 in Rr1. symmetry in Rr1. unfold w64 in Rr1. clear Ha02.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ2 SHOK RBspan A_readdata.
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
dkeep D16 UNs ltac:(first [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ => dhkeep DH (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD1 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UNs.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
st (dst + 20) 2 pdata nb cur1 (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_RD2));
[ exact HJ2
| rewrite Ra0; enorm; agnorm; rewrite E10; reflexivity
| rewrite Ra1; enorm; agnorm; rewrite E11, unsigned_lit_small by lia; reflexivity
| rewrite Ra2; reflexivity
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has Hes; lia
| exact Hst8
| clear - Hst1; lia
| exact Hst2
| exact RAstN
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpdc] | clear - Hcb1 Hcur; lia
| lia | lia
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia] | clear - Ha HSPB HDST0 HDSTC C1 HTS Has Hes; lia]
| apply amem_range_high; [clear; lia | clear - HDSTH; unfold rboxed in HDSTH; lia | clear - HDSTC; lia]
| eapply range_addressable_sub; [exact RAdstN | lia | lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc Sc W _ _ cid pos (dst + 20) 2 (proj1 HJ2) Hfin); clear - Hdst1 Hdst2; lia
| clear - Hsd; unfold rboxed in Hsd; lia
| clear - Hpdst Hdst1 Hdst2 Hrq2; unfold rboxed in Hpdst; lia ] end. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & r2 & cur2 & -> & HJ3 & HP3 & Ha03 & Hr2 & Vp' & Vn' & Vc' & Hfr3 & Hpres3 & Hio3).
assert (HIOc' : same_io mdc md3) by (io_after Hio3). clear Hio3 HIOc. rename HIOc' into HIOc.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr3 by lia.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstN RAdstN Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb2 : cur <= cur2 <= nb) by (clear - Hr2 Hcb1 Hcur Hnb; destruct Hr2 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc2 : rboxed ((r2 = 0 /\ cur2 = cur1 + 2 /\ cur1 + 2 <= nb) \/ (r2 = 2 ^ 64 - 1 /\ cur2 = nb /\ nb < cur1 + 2))) by (clear - Hr2; unfold rboxed; destruct Hr2 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left; split; [exact A1 | split; [exact A2 | exact X]] | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD2 : r2 = 0 -> forall i, 0 <= i < 2 -> aview tfibsegs (w_H W) mem3 (dst + 20 + i) = aview tfibsegs (w_H W) memc (pdata + ((cur + 2) + i))).
{ intros Hz i Hi. destruct Hr2 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp i Hi).
assert (Hpv : cur1 = cur + 2) by (unfold rboxed in *; clear - Hle Hrc1 Hcur; lia). rewrite Hpv.
replace (pdata + (cur + 2) + i) with (pdata + ((cur + 2) + i)) by (clear; lia).
apply KE; [clear - Hi Hle Hph Hpceil Hcur Hnb Hrq2 Hrc1 C1; unfold rboxed in *; lia | subst Zs; cbn beta; clear - Hi Hle Hcur Hnb Hrq2 Hpdst Hdst1 Hdst2 Hst1 Hpceil HSPB HSTB HTS Has Hrc1 C1; unfold rboxed in *; lia]. }
clear Hr2 Hcb1.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ2)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
reseatL HS HJ3 HP3 [0; 1; 2]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr3;
[ clear - Ha HSPB HTS Has C1; lia
| clear - Ha HSPB HDST0 HDSTC HTS Has C1; lia
| clear - Ha Hst1; lia
| clear - Ha; unfold ESTACK; lia ]
| exact Hpres3 ]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = _ =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite <- (KE a Ha Hna); apply (Hfr3 a Ha); clear - Hna Hes HTS Has; subst Zs; cbn beta in *; lia) end.
clear KE. rename KE2 into KE.
assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem3 a) by (intros a' Ha'; exact (Hpres3 a' (PR a' Ha'))). clear PR. rename PR2 into PR.
assert (D16' : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem3 (dst + i) = Some 0)
by (intros i Hi; rewrite (Hfr3 (dst + i)); [exact (D16 i Hi) | clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear D16. rename D16' into D16.
dhkeep DH (w_H W) mem3 ltac:(apply Hfr3; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD1 (w_H W) mem3 ltac:(apply Hfr3; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear Hfr3 Hpres3 HJ2 HP3.
renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
rreg HS (10%bv : bv 5) Rr2. cbn [ms_regs] in Rr2. rewrite Ha03 in Rr2. symmetry in Rr2. unfold w64 in Rr2. clear Ha03.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ3 SHOK RBspan A_readdata.
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
dkeep D16 UNs ltac:(first [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ => dhkeep DH (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD1 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD2 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UNs.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
st (dst + 24) 2 pdata nb cur2 (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_RD3));
[ exact HJ3
| rewrite Ra0; enorm; agnorm; rewrite E10; reflexivity
| rewrite Ra1; enorm; agnorm; rewrite E11, unsigned_lit_small by lia; reflexivity
| rewrite Ra2; reflexivity
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has Hes; lia
| exact Hst8
| clear - Hst1; lia
| exact Hst2
| exact RAstN
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpdc] | clear - Hcb2 Hcur; lia
| lia | lia
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia] | clear - Ha HSPB HDST0 HDSTC C1 HTS Has Hes; lia]
| apply amem_range_high; [clear; lia | clear - HDSTH; unfold rboxed in HDSTH; lia | clear - HDSTC; lia]
| eapply range_addressable_sub; [exact RAdstN | lia | lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc Sc W _ _ cid pos (dst + 24) 2 (proj1 HJ3) Hfin); clear - Hdst1 Hdst2; lia
| clear - Hsd; unfold rboxed in Hsd; lia
| clear - Hpdst Hdst1 Hdst2 Hrq2; unfold rboxed in Hpdst; lia ] end. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & r3 & cur3 & -> & HJ4 & HP4 & Ha04 & Hr3 & Vp' & Vn' & Vc' & Hfr4 & Hpres4 & Hio4).
assert (HIOc' : same_io mdc md4) by (io_after Hio4). clear Hio4 HIOc. rename HIOc' into HIOc.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr4 by lia.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstN RAdstN Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb3 : cur <= cur3 <= nb) by (clear - Hr3 Hcb2 Hcur Hnb; destruct Hr3 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc3 : rboxed ((r3 = 0 /\ cur3 = cur2 + 2 /\ cur2 + 2 <= nb) \/ (r3 = 2 ^ 64 - 1 /\ cur3 = nb /\ nb < cur2 + 2))) by (clear - Hr3; unfold rboxed; destruct Hr3 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left; split; [exact A1 | split; [exact A2 | exact X]] | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD3 : r3 = 0 -> forall i, 0 <= i < 2 -> aview tfibsegs (w_H W) mem4 (dst + 24 + i) = aview tfibsegs (w_H W) memc (pdata + ((cur + 4) + i))).
{ intros Hz i Hi. destruct Hr3 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp i Hi).
assert (Hpv : cur2 = cur + 4) by (unfold rboxed in *; clear - Hle Hrc1 Hrc2 Hcur; lia). rewrite Hpv.
replace (pdata + (cur + 4) + i) with (pdata + ((cur + 4) + i)) by (clear; lia).
apply KE; [clear - Hi Hle Hph Hpceil Hcur Hnb Hrq2 Hrc1 Hrc2 C1; unfold rboxed in *; lia | subst Zs; cbn beta; clear - Hi Hle Hcur Hnb Hrq2 Hpdst Hdst1 Hdst2 Hst1 Hpceil HSPB HSTB HTS Has Hrc1 Hrc2 C1; unfold rboxed in *; lia]. }
clear Hr3 Hcb2.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ3)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ4)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
reseatL HS HJ4 HP4 [0; 1; 2]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr4;
[ clear - Ha HSPB HTS Has C1; lia
| clear - Ha HSPB HDST0 HDSTC HTS Has C1; lia
| clear - Ha Hst1; lia
| clear - Ha; unfold ESTACK; lia ]
| exact Hpres4 ]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = _ =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mem4 a = aview tfibsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite <- (KE a Ha Hna); apply (Hfr4 a Ha); clear - Hna Hes HTS Has; subst Zs; cbn beta in *; lia) end.
clear KE. rename KE2 into KE.
assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem4 a) by (intros a' Ha'; exact (Hpres4 a' (PR a' Ha'))). clear PR. rename PR2 into PR.
assert (D16' : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem4 (dst + i) = Some 0)
by (intros i Hi; rewrite (Hfr4 (dst + i)); [exact (D16 i Hi) | clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear D16. rename D16' into D16.
dhkeep DH (w_H W) mem4 ltac:(apply Hfr4; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD1 (w_H W) mem4 ltac:(apply Hfr4; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD2 (w_H W) mem4 ltac:(apply Hfr4; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear Hfr4 Hpres4 HJ3 HP4.
renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
rreg HS (10%bv : bv 5) Rr3. cbn [ms_regs] in Rr3. rewrite Ha04 in Rr3. symmetry in Rr3. unfold w64 in Rr3. clear Ha04.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ4 SHOK RBspan A_readdata.
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
dkeep D16 UNs ltac:(first [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ => dhkeep DH (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD1 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD2 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD3 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UNs.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
st (dst + 28) 1 pdata nb cur3 (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_RD4));
[ exact HJ4
| rewrite Ra0; enorm; agnorm; rewrite E10; reflexivity
| rewrite Ra1; enorm; agnorm; rewrite E11, unsigned_lit_small by lia; reflexivity
| rewrite Ra2; reflexivity
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has Hes; lia
| exact Hst8
| clear - Hst1; lia
| exact Hst2
| exact RAstN
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpdc] | clear - Hcb3 Hcur; lia
| lia | lia
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia] | clear - Ha HSPB HDST0 HDSTC C1 HTS Has Hes; lia]
| apply amem_range_high; [clear; lia | clear - HDSTH; unfold rboxed in HDSTH; lia | clear - HDSTC; lia]
| eapply range_addressable_sub; [exact RAdstN | lia | lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc Sc W _ _ cid pos (dst + 28) 1 (proj1 HJ4) Hfin); clear - Hdst1 Hdst2; lia
| clear - Hsd; unfold rboxed in Hsd; lia
| clear - Hpdst Hdst1 Hdst2 Hrq2; unfold rboxed in Hpdst; lia ] end. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & r4 & cur4 & -> & HJ5 & HP5 & Ha05 & Hr4 & Vp' & Vn' & Vc' & Hfr5 & Hpres5 & Hio5).
assert (HIOc' : same_io mdc md5) by (io_after Hio5). clear Hio5 HIOc. rename HIOc' into HIOc.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr5 by lia.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstN RAdstN Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb4 : cur <= cur4 <= nb) by (clear - Hr4 Hcb3 Hcur Hnb; destruct Hr4 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc4 : rboxed ((r4 = 0 /\ cur4 = cur3 + 1 /\ cur3 + 1 <= nb) \/ (r4 = 2 ^ 64 - 1 /\ cur4 = nb /\ nb < cur3 + 1))) by (clear - Hr4; unfold rboxed; destruct Hr4 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left; split; [exact A1 | split; [exact A2 | exact X]] | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD4 : r4 = 0 -> forall i, 0 <= i < 1 -> aview tfibsegs (w_H W) mem5 (dst + 28 + i) = aview tfibsegs (w_H W) memc (pdata + ((cur + 6) + i))).
{ intros Hz i Hi. destruct Hr4 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp i Hi).
assert (Hpv : cur3 = cur + 6) by (unfold rboxed in *; clear - Hle Hrc1 Hrc2 Hrc3 Hcur; lia). rewrite Hpv.
replace (pdata + (cur + 6) + i) with (pdata + ((cur + 6) + i)) by (clear; lia).
apply KE; [clear - Hi Hle Hph Hpceil Hcur Hnb Hrq2 Hrc1 Hrc2 Hrc3 C1; unfold rboxed in *; lia | subst Zs; cbn beta; clear - Hi Hle Hcur Hnb Hrq2 Hpdst Hdst1 Hdst2 Hst1 Hpceil HSPB HSTB HTS Has Hrc1 Hrc2 Hrc3 C1; unfold rboxed in *; lia]. }
clear Hr4 Hcb3.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ4)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ5)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
reseatL HS HJ5 HP5 [0; 1; 2]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr5;
[ clear - Ha HSPB HTS Has C1; lia
| clear - Ha HSPB HDST0 HDSTC HTS Has C1; lia
| clear - Ha Hst1; lia
| clear - Ha; unfold ESTACK; lia ]
| exact Hpres5 ]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = _ =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mem5 a = aview tfibsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite <- (KE a Ha Hna); apply (Hfr5 a Ha); clear - Hna Hes HTS Has; subst Zs; cbn beta in *; lia) end.
clear KE. rename KE2 into KE.
assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem5 a) by (intros a' Ha'; exact (Hpres5 a' (PR a' Ha'))). clear PR. rename PR2 into PR.
assert (D16' : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem5 (dst + i) = Some 0)
by (intros i Hi; rewrite (Hfr5 (dst + i)); [exact (D16 i Hi) | clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear D16. rename D16' into D16.
dhkeep DH (w_H W) mem5 ltac:(apply Hfr5; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD1 (w_H W) mem5 ltac:(apply Hfr5; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD2 (w_H W) mem5 ltac:(apply Hfr5; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD3 (w_H W) mem5 ltac:(apply Hfr5; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear Hfr5 Hpres5 HJ4 HP5.
renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
rreg HS (10%bv : bv 5) Rr4. cbn [ms_regs] in Rr4. rewrite Ha05 in Rr4. symmetry in Rr4. unfold w64 in Rr4. clear Ha05.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ5 SHOK RBspan A_readdata.
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
dkeep D16 UNs ltac:(first [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ => dhkeep DH (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD1 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD2 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD3 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]); rkeep RD4 (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UNs.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
st (dst + 26) 2 pdata nb cur4 (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_RD5));
[ exact HJ5
| rewrite Ra0; enorm; agnorm; rewrite E10; reflexivity
| rewrite Ra1; enorm; agnorm; rewrite E11, unsigned_lit_small by lia; reflexivity
| rewrite Ra2; reflexivity
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has Hes; lia
| exact Hst8
| clear - Hst1; lia
| exact Hst2
| exact RAstN
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact Hpdc] | clear - Hcb4 Hcur; lia
| lia | lia
| intros a Ha; split; [right; right; right; exists cid, pos; split; [exact Hown | left; unfold in_zr; cbn [fst snd]; clear - Ha Hdst1 Hdst2; lia] | clear - Ha HSPB HDST0 HDSTC C1 HTS Has Hes; lia]
| apply amem_range_high; [clear; lia | clear - HDSTH; unfold rboxed in HDSTH; lia | clear - HDSTC; lia]
| eapply range_addressable_sub; [exact RAdstN | lia | lia]
| intros _; eapply (shadow_hull_vis_of_frame tfibsegs B LAWS lyc Sc W _ _ cid pos (dst + 26) 2 (proj1 HJ5) Hfin); clear - Hdst1 Hdst2; lia
| clear - Hsd; unfold rboxed in Hsd; lia
| clear - Hpdst Hdst1 Hdst2 Hrq2; unfold rboxed in Hpdst; lia ] end. }
cbv beta. intros W6 c6 _ (-> & regs6 & mem6 & md6 & r5 & cur5 & -> & HJ6 & HP6 & Ha06 & Hr5 & Vp' & Vn' & Vc' & Hfr6 & Hpres6 & Hio6).
assert (HIOc' : same_io mdc md6) by (io_after Hio6). clear Hio6 HIOc. rename HIOc' into HIOc.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr6 by lia.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp RAstN RAdstN Vp Vn Vc. rename Vp' into Vp. rename Vn' into Vn. rename Vc' into Vc.
assert (Hcb5 : cur <= cur5 <= nb) by (clear - Hr5 Hcb4 Hcur Hnb; destruct Hr5 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc5 : rboxed ((r5 = 0 /\ cur5 = cur4 + 2 /\ cur4 + 2 <= nb) \/ (r5 = 2 ^ 64 - 1 /\ cur5 = nb /\ nb < cur4 + 2))) by (clear - Hr5; unfold rboxed; destruct Hr5 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left; split; [exact A1 | split; [exact A2 | exact X]] | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (RD5 : r5 = 0 -> forall i, 0 <= i < 2 -> aview tfibsegs (w_H W) mem6 (dst + 26 + i) = aview tfibsegs (w_H W) memc (pdata + ((cur + 7) + i))).
{ intros Hz i Hi. destruct Hr5 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp i Hi).
assert (Hpv : cur4 = cur + 7) by (unfold rboxed in *; clear - Hle Hrc1 Hrc2 Hrc3 Hrc4 Hcur; lia). rewrite Hpv.
replace (pdata + (cur + 7) + i) with (pdata + ((cur + 7) + i)) by (clear; lia).
apply KE; [clear - Hi Hle Hph Hpceil Hcur Hnb Hrq2 Hrc1 Hrc2 Hrc3 Hrc4 C1; unfold rboxed in *; lia | subst Zs; cbn beta; clear - Hi Hle Hcur Hnb Hrq2 Hpdst Hdst1 Hdst2 Hst1 Hpceil HSPB HSTB HTS Has Hrc1 Hrc2 Hrc3 Hrc4 C1; unfold rboxed in *; lia]. }
clear Hr5 Hcb4.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ5)) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ6)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
reseatL HS HJ6 HP6 [0; 1; 2]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr6;
[ clear - Ha HSPB HTS Has C1; lia
| clear - Ha HSPB HDST0 HDSTC HTS Has C1; lia
| clear - Ha Hst1; lia
| clear - Ha; unfold ESTACK; lia ]
| exact Hpres6 ]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
lazymatch type of KE with forall a, _ -> _ -> aview _ _ ?m1 a = _ =>
assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview tfibsegs (w_H W) mem6 a = aview tfibsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite <- (KE a Ha Hna); apply (Hfr6 a Ha); clear - Hna Hes HTS Has; subst Zs; cbn beta in *; lia) end.
clear KE. rename KE2 into KE.
assert (PR2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) mem6 a) by (intros a' Ha'; exact (Hpres6 a' (PR a' Ha'))). clear PR. rename PR2 into PR.
assert (D16' : forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem6 (dst + i) = Some 0)
by (intros i Hi; rewrite (Hfr6 (dst + i)); [exact (D16 i Hi) | clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear D16. rename D16' into D16.
dhkeep DH (w_H W) mem6 ltac:(apply Hfr6; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD1 (w_H W) mem6 ltac:(apply Hfr6; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD2 (w_H W) mem6 ltac:(apply Hfr6; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD3 (w_H W) mem6 ltac:(apply Hfr6; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
rkeep RD4 (w_H W) mem6 ltac:(apply Hfr6; [clear - Hi HDST0 HDSTC C1; lia | clear - Hi; lia | clear - Hi Hsd; unfold rboxed in Hsd; lia | clear - Hi HDST0 HDSTC HSPB HTS Has Hes C1; lia]).
clear Hfr6 Hpres6 HJ5 HP6.
renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
rreg HS (10%bv : bv 5) Rr5. cbn [ms_regs] in Rr5. rewrite Ha06 in Rr5. symmetry in Rr5. unfold w64 in Rr5. clear Ha06.
set (b := fun j : Z => abyte (w_H W) mem6 (dst + 16 + j)).
assert (Hb : forall j, 0 <= b j < 256) by (intros j; subst b; apply abyte_range).
assert (Vb : forall j, 0 <= j < 16 -> val_mem tfibsegs (mrestrict (w_H W) mem6) (dst + 16 + j) 1 (b j)).
{ intros j Hj. subst b. apply abyte_val. apply PR. apply (proj1 (HFpres (dst + 16 + j) ltac:(clear - Hj Hdst1 Hdst2; lia))). }
set (fattr := (b 0 + 256 * b 1) + 65536 * (b 2 + 256 * b 3)).
set (fgen := (b 4 + 256 * b 5) + 65536 * (b 6 + 256 * b 7)).
set (delay := b 8 + 256 * b 9). set (nlp := b 10 + 256 * b 11). set (tidx := b 12).
pose proof (Hb 0) as Hb0. pose proof (Hb 1) as Hb1. pose proof (Hb 2) as Hb2. pose proof (Hb 3) as Hb3. pose proof (Hb 4) as Hb4. pose proof (Hb 5) as Hb5.
pose proof (Hb 6) as Hb6. pose proof (Hb 7) as Hb7. pose proof (Hb 8) as Hb8. pose proof (Hb 9) as Hb9. pose proof (Hb 10) as Hb10. pose proof (Hb 11) as Hb11. pose proof (Hb 12) as Hb12.
assert (Rfattr : 0 <= fattr < 2 ^ 32) by (subst fattr; clear - Hb0 Hb1 Hb2 Hb3; lia).
assert (Rfgen : 0 <= fgen < 2 ^ 32) by (subst fgen; clear - Hb4 Hb5 Hb6 Hb7; lia).
assert (Rdelay : 0 <= delay < 65536) by (subst delay; clear - Hb8 Hb9; lia).
assert (Rnlp : 0 <= nlp < 65536) by (subst nlp; clear - Hb10 Hb11; lia).
assert (Rtidx : 0 <= tidx < 256) by (subst tidx; clear - Hb12; lia).
assert (HDRV : r1 = 0 -> r2 = 0 -> r3 = 0 -> r4 = 0 -> r5 = 0 ->
fattr = hb P cur 0 + 256 * hb P cur 1 /\ fgen = hb P cur 2 + 256 * hb P cur 3 /\ delay = hb P cur 4 + 256 * hb P cur 5 /\
tidx = hb P cur 6 /\ nlp = hb P cur 7 + 256 * hb P cur 8).
{ intros Z1 Z2 Z3 Z4 Z5.
assert (HP9 : cur + 9 <= nb) by (unfold rboxed in *; clear - Z5 Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcur; lia).
assert (GB : forall j, 0 <= j < 9 -> aview tfibsegs (w_H W) memc (pdata + (cur + j)) = Some (hb P cur j)).
{ intros j Hj. unfold hb. replace (pdata + (cur + j)) with (pdata + Z.of_nat (Z.to_nat (cur + j))) by (clear - Hj Hcur; lia).
apply (garr8_aview _ _ _ _ HPL). clear - Hj Hcur HP9 HlenP. lia. }
subst fattr fgen delay nlp tidx. subst b. unfold abyte.
replace (dst + 16 + 0) with (dst + 16 + 0) by reflexivity.
rewrite (RD1 Z1 0) by (clear; lia). rewrite (RD1 Z1 1) by (clear; lia).
rewrite (DH 2) by (clear; lia). rewrite (DH 3) by (clear; lia).
replace (dst + 16 + 4) with (dst + 20 + 0) by (clear; lia). replace (dst + 16 + 5) with (dst + 20 + 1) by (clear; lia).
rewrite (RD2 Z2 0) by (clear; lia). rewrite (RD2 Z2 1) by (clear; lia).
rewrite (DH 6) by (clear; lia). rewrite (DH 7) by (clear; lia).
replace (dst + 16 + 8) with (dst + 24 + 0) by (clear; lia). replace (dst + 16 + 9) with (dst + 24 + 1) by (clear; lia).
rewrite (RD3 Z3 0) by (clear; lia). rewrite (RD3 Z3 1) by (clear; lia).
replace (dst + 16 + 10) with (dst + 26 + 0) by (clear; lia). replace (dst + 16 + 11) with (dst + 26 + 1) by (clear; lia).
rewrite (RD5 Z5 0) by (clear; lia). rewrite (RD5 Z5 1) by (clear; lia).
replace (dst + 16 + 12) with (dst + 28 + 0) by (clear; lia).
rewrite (RD4 Z4 0) by (clear; lia).
replace (cur + 0 + 0) with (cur + 0) by (clear; lia). replace (cur + 0 + 1) with (cur + 1) by (clear; lia).
replace (cur + 2 + 0) with (cur + 2) by (clear; lia). replace (cur + 2 + 1) with (cur + 3) by (clear; lia).
replace (cur + 4 + 0) with (cur + 4) by (clear; lia). replace (cur + 4 + 1) with (cur + 5) by (clear; lia).
replace (cur + 7 + 0) with (cur + 7) by (clear; lia). replace (cur + 7 + 1) with (cur + 8) by (clear; lia).
replace (cur + 6 + 0) with (cur + 6) by (clear; lia).
rewrite !GB by (clear; lia). cbv iota beta. clear; lia. }
assert (Vfattr : val_mem tfibsegs (mrestrict (w_H W) mem6) (dst + 16) 4 fattr).
{ subst fattr. apply val_mem_half2; [| | clear - Hb0 Hb1; lia | clear - Hb2 Hb3; lia].
- replace (dst + 16) with (dst + 16 + 0) by lia. apply val_mem_bytes2; [exact (Vb 0 ltac:(lia)) | replace (dst + 16 + 0 + 1) with (dst + 16 + 1) by lia; exact (Vb 1 ltac:(lia)) | exact Hb0 | exact Hb1].
- replace (dst + 16 + 2) with (dst + 16 + 2) by lia. apply val_mem_bytes2; [exact (Vb 2 ltac:(lia)) | replace (dst + 16 + 2 + 1) with (dst + 16 + 3) by lia; exact (Vb 3 ltac:(lia)) | exact Hb2 | exact Hb3]. }
assert (Vfgen : val_mem tfibsegs (mrestrict (w_H W) mem6) (dst + 20) 4 fgen).
{ subst fgen. apply val_mem_half2; [| | clear - Hb4 Hb5; lia | clear - Hb6 Hb7; lia].
- replace (dst + 20) with (dst + 16 + 4) by lia. apply val_mem_bytes2; [exact (Vb 4 ltac:(lia)) | replace (dst + 16 + 4 + 1) with (dst + 16 + 5) by lia; exact (Vb 5 ltac:(lia)) | exact Hb4 | exact Hb5].
- replace (dst + 20 + 2) with (dst + 16 + 6) by lia. apply val_mem_bytes2; [exact (Vb 6 ltac:(lia)) | replace (dst + 16 + 6 + 1) with (dst + 16 + 7) by lia; exact (Vb 7 ltac:(lia)) | exact Hb6 | exact Hb7]. }
assert (Vdelay : val_mem tfibsegs (mrestrict (w_H W) mem6) (dst + 24) 2 delay).
{ subst delay. replace (dst + 24) with (dst + 16 + 8) by lia. apply val_mem_bytes2; [exact (Vb 8 ltac:(lia)) | replace (dst + 16 + 8 + 1) with (dst + 16 + 9) by lia; exact (Vb 9 ltac:(lia)) | exact Hb8 | exact Hb9]. }
assert (Vnlp : val_mem tfibsegs (mrestrict (w_H W) mem6) (dst + 26) 2 nlp).
{ subst nlp. replace (dst + 26) with (dst + 16 + 10) by lia. apply val_mem_bytes2; [exact (Vb 10 ltac:(lia)) | replace (dst + 16 + 10 + 1) with (dst + 16 + 11) by lia; exact (Vb 11 ltac:(lia)) | exact Hb10 | exact Hb11]. }
assert (Vtidx : val_mem tfibsegs (mrestrict (w_H W) mem6) (dst + 28) 1 tidx).
{ subst tidx. replace (dst + 28) with (dst + 16 + 12) by lia. exact (Vb 12 ltac:(lia)). }
clearbody fattr fgen delay nlp tidx. clear Vb Hb Hb0 Hb1 Hb2 Hb3 Hb4 Hb5 Hb6 Hb7 Hb8 Hb9 Hb10 Hb11 Hb12 b.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let HS3 := fresh "HS3" in
let WS := constr:([Z_to_bv 64 fattr; Z_to_bv 64 fgen; Z_to_bv 64 delay; Z_to_bv 64 nlp; Z_to_bv 64 tidx] : list word) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3;
clear HS; rename HS3 into HS;
assert (Efattr : ew (havoc Ev K WS) K = Z_to_bv 64 fattr) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Efgen : ew (havoc Ev K WS) (K + 1) = Z_to_bv 64 fgen) by (exact (ew_havoc_new Ev K WS 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Edelay : ew (havoc Ev K WS) (K + 2) = Z_to_bv 64 delay) by (exact (ew_havoc_new Ev K WS 2 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Enlp : ew (havoc Ev K WS) (K + 3) = Z_to_bv 64 nlp) by (exact (ew_havoc_new Ev K WS 3 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (Etidx : ew (havoc Ev K WS) (K + 4) = Z_to_bv 64 tidx) by (exact (ew_havoc_new Ev K WS 4 (Z_to_bv 64 0) ltac:(cbn; lia)));
cbn [Nat.add] in Efgen, Edelay, Enlp, Etidx;
let HS4 := fresh "HS4" in
pose proof (ast_ok_add_region tfibsegs _ _ _ (dst_regionA K) HS eq_refl
ltac:(unfold dst_regionA, region_ok; cbn [Nat.add YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite ?ew_havoc_old by (clear; cbn; lia); rewrite (AG 11%nat) by lia; rewrite B11;
split; [clear - HDST0 HDSTC C1; lia|]; split; [clear - HDST0 HDSTC C1; lia|]; split;
[ intros q Hq; apply (apresent_writable tfibsegs); apply PR; apply (proj1 (HFpres (dst + q) ltac:(clear - Hq Hdst1 Hdst2; lia)))
| apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]]];
[ apply (chunk_ok_zero tfibsegs); intros i Hi; rewrite Z.add_0_r;
destruct (aview_byte tfibsegs (w_H W) mem6 (dst + i) 0 (D16 i Hi)) as (bb & Hbb & Hv & _); rewrite Hbb; f_equal; apply bv_eq; rewrite Z_to_bv_unsigned; change (bv_wrap 8 0) with 0; clear - Hv; lia
| apply (chunk_ok_val tfibsegs _ _ dst 16 4 _ fattr); [cbn [sv_denot]; rewrite ?Efattr, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vfattr]
| apply (chunk_ok_val tfibsegs _ _ dst 20 4 _ fgen); [cbn [sv_denot]; rewrite ?Efgen, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vfgen]
| apply (chunk_ok_val tfibsegs _ _ dst 24 2 _ delay); [cbn [sv_denot]; rewrite ?Edelay, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vdelay]
| apply (chunk_ok_val tfibsegs _ _ dst 26 2 _ nlp); [cbn [sv_denot]; rewrite ?Enlp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vnlp]
| apply (chunk_ok_val tfibsegs _ _ dst 28 1 _ tidx); [cbn [sv_denot]; rewrite ?Etidx, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vtidx] ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
unfold dst_regionA; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?ew_havoc_old by (clear; cbn; lia); rewrite (AG 11%nat), (AG 2%nat) by lia; rewrite B11, Usp;
unfold A_GOT_shadow, A_shadow_glob; clear - HSPB HDST0 HDSTC HDSTI HTS Has C1; unfold rboxed in HDSTI; repeat split; lia)) as HS4;
clear HS; rename HS4 into HS; norm_ss HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := lazymatch type of Efattr with ew _ ?K = _ => K end in
let HS3 := fresh "HS3" in
pose proof (st_ok_add_fact tfibsegs Ev _ msv K (mkAF 0 (2 ^ 32 - 1) 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 1)%nat (mkAF 0 (2 ^ 32 - 1) 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 2)%nat (mkAF 0 65535 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 3)%nat (mkAF 0 65535 0)
(st_ok_add_fact tfibsegs Ev _ msv (K + 4)%nat (mkAF 0 255 0) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Etidx, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rtidx; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Enlp, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rnlp; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Edelay, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rdelay; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Efgen, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rfgen; lia))
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2 Nat.add]; rewrite Efattr, unsigned_lit_small by lia; rewrite Z.pow_0_r, Z.mod_1_r; clear - Rfattr; lia)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
reshok_bx HS 32%nat.
clear Zsm. set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst <= a < dst + 16).
assert (ZBsm : forall a, SB <= a < kHighShadowEnd -> ~ Zsm a) by (intros a Ha X; apply (ZB a Ha); subst Zs Zsm; cbn beta in *; clear - X HTS Has; lia).
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
aj_run_tok tfibtbl_lib_ok HS HJ6 SHOK RBspan.
all: try (oblDST RAdstN E11 E32).
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs. clear D16 RAdstN.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]). clear UNs.
assert (Hrr1 : 0 <= r1 < 2 ^ 64) by (unfold rboxed in Hrc1; clear - Hrc1; lia). assert (Hrr2 : 0 <= r2 < 2 ^ 64) by (unfold rboxed in Hrc2; clear - Hrc2; lia).
assert (Hrr3 : 0 <= r3 < 2 ^ 64) by (unfold rboxed in Hrc3; clear - Hrc3; lia). assert (Hrr4 : 0 <= r4 < 2 ^ 64) by (unfold rboxed in Hrc4; clear - Hrc4; lia).
assert (Hrr5 : 0 <= r5 < 2 ^ 64) by (unfold rboxed in Hrc5; clear - Hrc5; lia).
pose proof (rfcA_Z_lor_bound r2 r1 64 ltac:(clear; lia) Hrr2 Hrr1) as Hl21. pose proof (rfcA_Z_lor_bound r3 r4 64 ltac:(clear; lia) Hrr3 Hrr4) as Hl34.
pose proof (rfcA_Z_lor_bound _ _ 64 ltac:(clear; lia) Hl21 Hl34) as Hl4. pose proof (rfcA_Z_lor_bound _ r5 64 ltac:(clear; lia) Hl4 Hrr5) as Hl5.
set (racc := Z.lor (Z.lor (Z.lor r2 r1) (Z.lor r3 r4)) r5) in Hl5.
assert (Hracc0 : racc = 0 -> r1 = 0 /\ r2 = 0 /\ r3 = 0 /\ r4 = 0 /\ r5 = 0)
by (intros Hz; subst racc; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz Hz5]; apply Z.lor_eq_0_iff in Hz; destruct Hz as [Hz21 Hz34];
apply Z.lor_eq_0_iff in Hz21; apply Z.lor_eq_0_iff in Hz34; clear - Hz21 Hz34 Hz5; tauto).
assert (Hraccnz : racc <> 0 -> ~ (r1 = 0 /\ r2 = 0 /\ r3 = 0 /\ r4 = 0 /\ r5 = 0))
by (intros Hz (Z1 & Z2 & Z3 & Z4 & Z5); apply Hz; subst racc; rewrite Z1, Z2, Z3, Z4, Z5; reflexivity).
assert (Hhdrv : rfc_hdrv P cur nb fattr fgen delay tidx nlp)
by (intros H9; apply HDRV; unfold rboxed in *; clear - H9 Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcur; lia).
assert (HprogH : rfc_progH cur nb racc cur5).
{ unfold rfc_progH. destruct (Z.eq_dec racc 0) as [Hz|Hnz].
- left. pose proof (Hracc0 Hz) as (Z1 & Z2 & Z3 & Z4 & Z5). unfold rboxed in *. clear - Hz Z1 Z2 Z3 Z4 Z5 Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcur. lia.
- right. pose proof (Hraccnz Hnz) as Hsome. unfold rboxed in *. clear - Hnz Hsome Hrc1 Hrc2 Hrc3 Hrc4 Hrc5 Hcur Hnb. lia. }
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
-
assert (Hbit : Z.land fattr 1 = 0).
{ rewrite branch_eq_U, (U_attr_bit _ 132%nat fattr) in Hc by first [exact Rfattr | enorm; agnorm; exact Efattr]. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [assumption | discriminate Hc]. }
clear Hc. norm_ss HS. reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ6 SHOK RBspan RFC_I.
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]). clear UNs.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstI. clear SHK.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zs (rfc_kept_refl B W memc (spZ regs) Bb lyc Sc st dst) HSEP KE ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (20%bv : bv 5) Q20. rreg HS (25%bv : bv 5) Q25. rreg HS (26%bv : bv 5) Q26. rreg HS (27%bv : bv 5) Q27.
lazymatch type of Q20 with getr ?rg _ = _ => assert (HRACC : bv_unsigned (getr rg 20) = racc) end.
{ rewrite Q20. cbn [ms_regs]. enorm. agnorm. rewrite Rr1, Rr2, Rr3, Rr4, Rr5.
rewrite (rfcA_alu_or_lits r2 r1 Hrr2 Hrr1), (rfcA_alu_or_lits r3 r4 Hrr3 Hrr4), (rfcA_alu_or_lits _ _ Hl21 Hl34), (rfcA_alu_or_lits _ _ Hl4 Hrr5).
subst racc. apply unsigned_lit_small. clear - Hl5. lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
assert (B11x : forall Ex, (forall m, (m < 33)%nat -> ew Ex m = ew E m) -> bv_unsigned (ew Ex 11) = dst) by (intros Ex AGx; rewrite (AGx 11%nat) by lia; exact B11).
pose proof (zero_of_region _ _ 11%nat dst _ _ _ _ _ 0 16 dst 8 HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 11%nat dst _ _ _ _ _ 0 16 (dst + 8) 8 HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 16 4 (SOff 132 0) fattr HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Efattr, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 20 4 (SOff 133 0) fgen HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Efgen, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfg.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 24 2 (SOff 134 0) delay HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Edelay, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 26 2 (SOff 135 0) nlp HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Enlp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 28 1 (SOff 136 0) tidx HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Etidx, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vfa, Vfg, Vde, Vnl, Vti.
pose proof (rfc_frame_of_stackA _ _ regs _ _ _ _ _ HRs ltac:(enorm; agnorm; exact Usp)
ltac:(intros j Hj; do 11 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 11 (destruct j as [|j]; [cbn [nth rfc_saved Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; enorm; agnorm; rewrite (proj1 HAE) by lia; apply ew_Ereg_nat; reflexivity|]); exfalso; clear - Hj; lia)) as HFR.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 526976) with (Z_to_bv 64 RFC_I).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (RI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W (ms_regs msX) (ms_mem msX) mdX lyc Sc k (bv_unsigned (getr (ms_regs msX) 20)) cur5 0 nlp fattr fgen delay tidx [] T 0 P);
[ exact RC | exact HPL | exact HMLE | apply (mo_malloc_nonneg MT MTL); clear; lia | exact Hhdrv
|
rewrite HRACC; unfold rfc_progP, palsz; rewrite Hbit; cbn [Z.eqb]; rewrite !Z.add_0_r;
destruct HprogH as [(Hz & Hfit & Ecv) | (Hnz & Hsh & Ecv)];
[ left; split; [exact Hz|]; split; [exact Hfit|]; split; [exact Ecv | intros X; exfalso; apply X; reflexivity]
| right; split; [exact Hnz|]; split; [exact Hsh | exact Ecv] ]
| exact HJ6 | clear; lia | reflexivity | cbn [app]; exact HPerm
|   unfold rfc_pal; rewrite Hbit; cbn [Z.eqb]; split; [reflexivity|]; split; [intros _; reflexivity|]; split; [intros b Hb; destruct Hb | intros b m Hb; destruct Hb]
|   unfold rfc_vals; split; [pose proof (bv_unsigned_in_range 64 (getr (ms_regs msX) 20)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR|];
split; [exact Hcb5|]; split; [clear; lia|]; split; [exact Rnlp|]; split; [exact Rfattr|]; split; [exact Rfgen|]; split; [exact Rdelay|]; clear - Rtidx; lia
|   unfold I_regs_at, w64; rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q25, Q26, Q27; enorm; agnorm;
rewrite E3, E4, E11, E12, E10, E32, Usp, Z_to_bv_bv_unsigned, (EE 26%nat 26%bv eq_refl), (EE 27%nat 27%bv eq_refl);
repeat split; try reflexivity; f_equal; lia
| exact HFR
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstI
| exact KEPT
| io_now ] end.
-
assert (Hbit : Z.land fattr 1 <> 0).
{ rewrite branch_eq_U, (U_attr_bit _ 132%nat fattr) in Hc by first [exact Rfattr | enorm; agnorm; exact Efattr]. rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
destruct (Z.eqb_spec (Z.land fattr 1) 0); [discriminate Hc | assumption]. }
clear Hc. norm_ss HS. reshok_bx HS 32%nat.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
aj_run_tok tfibtbl_lib_ok HS HJ6 SHOK RBspan.
all: try (oblDST RAdstN E11 E32).
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs. clear RAdstN.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]). clear UNs.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zs (rfc_kept_refl B W memc (spZ regs) Bb lyc Sc st dst) HSEP KE ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT.
assert (Hlive1 : blocks_bytes Sc + 3 * nlp <= LIVE_MAX) by (unfold LIVE_RFC in Hlive; clear - Hlive Rnlp; lia).
rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp. rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
replace (Z_to_bv 64 338272) with (Z_to_bv 64 (pc_wrap_malloc (as_code B))) by (rewrite HBcode; reflexivity).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
assert (CH : chain_pre lyc (aview tfibsegs (w_H W) (ms_mem msX)) (ms_regs msX) []) end.
{ eapply (achain_chain_pre lyc _ (spZ regs - 96) dst []).
- apply achain_low; clear - HDST0 HDSTC; lia.
- unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; clear - HSPB C1 HTS Has; unfold spZ in HSPB; lia.
- unfold s0Z; rewrite Rs0; enorm; agnorm; rewrite E11; apply unsigned_lit_small; clear - HDST0 HDSTC C1; lia.
- unfold raZ; rewrite Rra, unsigned_lit_small by lia; lia. }
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (amalloc04_sub tfibsegs B LAWS tfib_segs_low MT AMALLOC4 W (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own
lyc Sc _ k (3 * nlp) (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_PM) [] HJ6);
[ rewrite Ra0; enorm; agnorm; unfold w64; rewrite <- (denot_mul3 _ 135%nat nlp Enlp Rnlp); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| unfold MALLOC_MAX; clear - Rnlp; lia
| exact Hlive1
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has; lia
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| rewrite HEV in Hev; clear - Hnev Hev; lia
| exact CH
| rewrite call_trace_nil; unfold raZ; rewrite Rra, unsigned_lit_small by lia; rewrite HBcode, (tl_universe B TL);
apply TRACES_read_frameconfig_U; apply memZL_In; vm_compute; reflexivity
|
apply (mok_station MT Sc Sc T 0 (mo_malloc MT (3 * nlp)) MTL HMOK HMLE); [apply (mo_malloc_nonneg MT MTL); clear - Rnlp; lia|];
unfold RFC_COST in HCOST; pose proof (mo_malloc_mono MT MTL (3 * nlp) 196605 ltac:(clear - Rnlp; lia)) as Hmm;
pose proof (mo_malloc_nonneg MT MTL N ltac:(clear - HN; lia)) as HmN; pose proof (mo_free_nonneg MT MTL) as Hf0; clear - HCOST Hmm HmN Hf0; lia ] end. }
cbv beta. clear Ra0 Rra Rsp Rgp Rtp Rs0 CH.
intros W7 c7 Hwle7 (ly7 & S7 & regs7 & mem7 & md7 & res & -> & HJ7 & HP7 & Ha07 & Hfrs7 & Hr4096 & Ebl & HK0 & HMLE7 & HJS7).
assert (HIOc' : same_io mdc md7) by (io_after (ajournal_closed_same_io B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ sink_closed_nil HJS7)). clear HJS7 HIOc. rename HIOc' into HIOc.
pose proof (proj1 HJ7) as HAR7.
lazymatch type of HK0 with acall_kept _ _ _ _ _ ?mm0 _ _ _ _ _ =>
assert (HK : acall_kept tfibsegs B lyc Sc W mm0 W7 mem7 (sp0 + (spZ regs - 96 - sp0) - ASTACK) (sp0 + (spZ regs - 96 - sp0)) (fun a => res <> 0 /\ res <= a < res + req_size (3 * nlp)))
by (eapply acall_kept_mono_E; [exact HK0 | intros a Ha; cbn beta; split; [clear - Hr4096; lia | exact Ha]]) end.
assert (HBin : forall b, In b (ablocks B lyc Sc) -> In b (ablocks B ly7 S7)) by (intros b Hb; rewrite Ebl; apply in_app_iff; left; exact Hb).
assert (HrIn : In (res, 3 * nlp) (ablocks B ly7 S7)) by (rewrite Ebl; apply in_app_iff; right; left; reflexivity).
assert (HresIn : res <> 0 -> In (res, 3 * nlp) (ablocks B ly7 S7)) by (intros _; exact HrIn).
vkeep Vp (w_H W7) mem7 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
vkeep Vn (w_H W7) mem7 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
vkeep Vc (w_H W7) mem7 ltac:(apply (proj1 HK); [clear - Hi HSTB; lia | clear - Hi Hst1; lia]).
destruct (al_blocks _ _ LAWS _ _ _ _ _ res (3 * nlp) HAR7 HrIn) as (Hr16 & _ & HrCeil & [_ HrHi2] & _).
pose proof (blk_off_img _ _ _ _ _ _ _ _ HAR7 HrIn) as HrHi1.
assert (HrHi : (res + req_size (3 * nlp) <= 65536 \/ 6270976 <= res) /\ (res + req_size (3 * nlp) <= 2147446784 \/ 17594333495296 <= res))
by (pose proof asan_consts as (C1' & C2' & C3' & C4' & C5'); clear - HrHi1 HrHi2 C1' C2' C3' C4' C5'; unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
assert (Hrng : res = 0 \/ (4096 <= res /\ ((res + req_size (3 * nlp) <= 65536 \/ 6270976 <= res) /\ (res + req_size (3 * nlp) <= 2147446784 \/ 17594333495296 <= res)) /\ res + req_size (3 * nlp) <= alloc_ceiling /\ res mod 16 = 0 /\ In (res, 3 * nlp) (ablocks B ly7 S7)))
by (right; split; [exact Hr4096|]; split; [exact HrHi|]; split; [exact HrCeil|]; split; [exact Hr16 | exact HrIn]).
assert (Hfin7 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR7 Hfin7) as (_ & _ & HFpres7 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ6)) as (Kcell6 & _ & Kgot6 & _). rewrite HBgot, HBcell in Kgot6. rewrite HBcell in Kcell6.
destruct (al_const _ _ LAWS _ _ _ _ _ HAR7) as (Kcell7 & _ & Kgot7 & _). rewrite HBgot, HBcell in Kgot7. rewrite HBcell in Kcell7.
pose proof HJ7 as (_ & Hly7 & _).
assert (EFA7 : forall c p, frame_addr ly7 c p = frame_addr lyc c p)
by (intros c p; unfold frame_addr; destruct Hly7 as (_ & _ & _ & _ & _ & -> & _); rewrite HlyF; reflexivity).
assert (HnewF : forall a, frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ (res <> 0 /\ res <= a < res + req_size (3 * nlp))).
{ intros a Ha [Hnz Hin]. pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) cid pos HAR7 (HresIn Hnz) Hfin7) as D.
rewrite EFA7 in D. unfold zdisjoint in D. cbn [fst snd] in D. clear - D Ha Hin. lia. }
assert (RAdst7 : range_addressable (aview tfibsegs (w_H W7) mem7) SHADOW_OFF dst 32).
{ shkOf KE ZB SHK.
eapply (RA_kept_call B lyc Sc); [exact HK | exact Hfin | intros a [Hnz Ha]; clear - Hnz Ha Hrng; unfold rboxed in *; lia | exact Hcid | exact Hfal
| clear - HFhi1; lia | exact HFceil | exact Hdst1 | exact Hdst2 |].
apply (RA_kept_band _ _ dst 32 SHK); [lia | clear - HDST0 HDSTC C1 C4; lia | exact RAdst]. }
pose proof Hly7 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo7 & Ehi7 & _).
assert (RAst7 : range_addressable (aview tfibsegs (w_H W7) mem7) SHADOW_OFF st 24).
{ apply (RA_stack B LAWS ly7 S7 W7 mem7 _ st 24 HAR7); [rewrite Elo7; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi7; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]. }
reseatL HS HJ7 HP7 [0; 1; 2; 3]%nat AG
ltac:(first [ eapply (region_kept_stack_aj tfibsegs B); [exact HK | exact HJ7 | evalER AG | clear - Hst1 HTS Has; lia | clear - Hwlo Hst1 HTS Has; lia | clear - Hwhi Hst2; lia | cbn; lia | cbn; lia]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot6) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot7) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell6) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell7) | lia]
| eapply (region_kept_ownframe_aj tfibsegs _); [exact HK | evalER AG | exact Hfin | left; cbn [YP09.r_lo YP09.r_hi]; lia
| intros a Ha; cbn beta; apply HnewF; lia | intros a Ha; apply (fun H => proj1 (HFpres7 a H)); rewrite EFA7; lia ]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell6 Kgot6 Kcell7 Kgot7.
rreg HS (10%bv : bv 5) Rres. rewrite Ha07 in Rres. symmetry in Rres. unfold w64 in Rres.
assert (HBb1 : forall b m, In (b, m) Bb -> In (b, m) (ablocks B lyc Sc)) by (intros b m Hb; eapply Permutation_in; [apply Permutation_sym; exact HPerm | exact Hb]).
clear KE. renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
clear Hrng. rbox HrHi.
pose proof (aftok_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) HJ6 (proj1 HJ7) Ebl ltac:(clear - Rnlp; lia)) as Tpal.
assert (Apal : forall blc i lyq, In (res, 3 * nlp) blc -> 0 <= i < req_size (3 * nlp) -> awr_byte STK sp0 FP (ablocks B ly S) blc lyq own (res + i)).
{ intros blc i lyq Hin Hi. exact (awr_new_block tfibsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ res (3 * nlp) blc i lyq HJ6 (proj1 HJ7) Ebl ltac:(clear - Rnlp; lia) Hin Hi). }
assert (HPerm7 : Permutation (ablocks B ly7 S7) ([(res, 3 * nlp)] ++ Bb)).
{ rewrite Ebl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply Permutation_cons; [reflexivity | exact HPerm]. }
pose proof (req_size_pos (3 * nlp) ltac:(clear - Rnlp; lia)) as [Hrql1 Hrql2].
assert (HsepB : forall b m, In (b, m) Bb -> res + req_size (3 * nlp) <= b \/ b + req_size m <= res).
{ intros b m Hb. destruct (in_split _ _ Hb) as (l1 & l2 & El).
assert (HP' : Permutation (ablocks B ly7 S7) ((res, 3 * nlp) :: (b, m) :: l1 ++ l2)).
{ eapply Permutation_trans; [exact HPerm7|]. cbn [app]. apply perm_skip. rewrite El. apply Permutation_sym. apply Permutation_middle. }
pose proof (sep_blocks_perm tfibsegs B LAWS _ _ _ _ _ _ _ _ HAR7 HP') as D. unfold zdisjoint, block_rng in D. cbn [fst snd] in D. clear - D. lia. }
assert (KEPT7 : rfc_kept B W memc W7 mem7 (spZ regs) Bb lyc Sc st dst).
{ eapply (rfc_kept_call B _ _ _ _ _ _ _ _ _ _ lyc Sc _ _ _ _ _ KEPT HK ltac:(clear - HTS Has; lia) ltac:(clear; lia) HBb1 _ eq_refl ltac:(intros; reflexivity) _).
Unshelve.
- intros b m i Hb Hi [_ Hin]. pose proof (HsepB b m Hb) as Hd. clear - Hd Hi Hin. lia.
- intros c p a Hcp Ha [Hnz Hin]. destruct Ha as [Ha | Ha].
+ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) c p HAR7 (HresIn Hnz) ltac:(rewrite Hfrs7; exact Hcp)) as D.
rewrite EFA7 in D. unfold zdisjoint, frame_rng, in_zr in D, Ha. cbn [fst snd] in D, Ha. clear - D Ha Hin. lia.
+ destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ c p HAR7 ltac:(rewrite Hfrs7; exact Hcp)) as (F0 & Fc & Fh). rewrite EFA7 in F0, Fc, Fh.
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow. clear - Hlow Hin HrHi Hrql2 C2 C3. unfold rboxed in HrHi. lia. }
assert (HnotBb : ~ In (res, 3 * nlp) Bb) by (intros Hb; pose proof (HsepB _ _ Hb) as Hd; clear - Hd Hrql1; lia).
clear KEPT HK Hlive1.
lazymatch type of Rres with ew ?Ex ?nx = _ =>
pose proof (st_ok_add_fact tfibsegs Ex _ _ nx (mkAF 4096 140737479966720 4) HS
ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Rres, unsigned_lit_small by lia;
change (2 ^ 4) with 16; clear - Hr4096 HrCeil Hr16 Hrql1 Hrql2 C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
norm_ss HS. reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ7 SHOK RBspan A_readdata.
all: try (oblDST RAdst7 E11 E32).
{ awrRFC Uspn E10n E11n Hown EFA7. }
unrunRD HFr Zsm Usp B10 Usp UN7. clear HF HFr HG PR.
vkeepUN UN7 Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT7 HSEP UN7 ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT7s. clear KEPT7.
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ ly7 S7 W7 ?mm _ _ |- _ =>
assert (RAstC : range_addressable (aview tfibsegs (w_H W7) mm) SHADOW_OFF st 24)
by (apply (RA_stack B LAWS ly7 S7 W7 mm _ st 24 (proj1 HJc)); [rewrite Elo7; clear - Hst1 Hwlo Hslo Hstk0 HTS Has; lia | rewrite Ehi7; clear - Hst2 Hshi; lia | exact Hst8 | reflexivity | clear; lia]);
pose proof (proj1 HJc) as HARc end.
destruct (al_blocks _ _ LAWS _ _ _ _ _ pdata nb (proj1 HJ7) (HBin _ (HBb1 _ _ Hpd))) as (_ & _ & _ & _ & Hppres7 & _).
rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2. rreg HS (1%bv : bv 5) Rra.
rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) _) _ =>
eapply (aj_readdata_at B TL LAWS AMEMCPY _ (ms_regs msX) (ms_mem msX) STK sp0 FP ly S W0 mem0 md0 own ly7 S7 _ (k + 1)
st res (3 * nlp) pdata nb cur5 (spZ regs - 96 - sp0) (Z_to_bv 64 RFC_PRD));
[ lazymatch goal with H : ajournal _ _ _ _ _ _ _ _ _ _ _ ly7 S7 W7 (ms_mem msX) _ _ |- _ => exact H end
| rewrite Ra0; enorm; agnorm; rewrite E10; reflexivity
| rewrite Ra1; enorm; agnorm; rewrite Rres; reflexivity
| rewrite Ra2; enorm; agnorm; unfold w64; rewrite <- (denot_mul3 _ 135%nat nlp Enlp Rnlp); cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| rewrite Rgp; enorm; agnorm; rewrite E3; reflexivity
| rewrite Rtp; enorm; agnorm; rewrite E4; reflexivity
| exact Rra
| vm_compute; reflexivity
| unfold spZ; rewrite Rsp; enorm; agnorm; rewrite unsigned_lit_small by (rewrite Usp; clear - HSPB C1 HTS Has; lia); rewrite Usp; unfold spZ; lia
| replace (spZ regs - 96 - sp0) with (spZ regs - sp0 + (-6) * 16) by lia; rewrite Z_mod_plus_full, Zminus_mod, Hal16, Hsp0al; reflexivity
| lia
| clear - Hwlo HTS Has Hes; lia
| exact Hst8
| clear - Hst1; lia
| exact Hst2
| exact RAstC
| exact Vp | exact Vn | exact Vc
| left; split; [exact Hnb | exact (HBin _ (HBb1 _ _ Hpd))] | clear - Hcb5 Hcur; lia
| clear - Rnlp; lia | clear - Hr4096; lia
| intros a Ha; split; [replace a with (res + (a - res)) by lia; apply Apal; [exact HrIn | clear - Ha Hrql2; lia] | clear - Ha HrCeil Hrql2 HSPB C1 HTS Has Hes; lia]
| apply (amem_range_of_block tfibsegs B LAWS ly7 S7 W7 _ _ res (3 * nlp) _ _ HAR7 HrIn); clear - Hrql2; lia
| apply (range_addressable_of_block tfibsegs B LAWS ly7 S7 W7 _ _ res (3 * nlp) _ _ HARc HrIn); clear - Hrql2; lia
| intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly7 S7 W7 _ _ res (3 * nlp) _ _ HARc HrIn); clear - Hrql2 Hn0; lia
| right; left; clear - HrCeil Hrql2 HSTB; lia
| pose proof (HsepB pdata nb Hpd) as Hd; clear - Hd Hrql2 Hrq2; lia ] end. }
cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & rpal & cur6 & -> & HJ8 & HP8 & Ha08 & Hr6 & Vp8 & Vn8 & Vc8 & Hfr8 & Hpres8 & Hio8).
assert (HIOc' : same_io mdc md8) by (io_after Hio8). clear Hio8 HIOc. rename HIOc' into HIOc.
replace (sp0 + (spZ regs - 96 - sp0)) with (spZ regs - 96) in Hfr8 by lia.
clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp Vp Vn Vc. rename Vp8 into Vp. rename Vn8 into Vn. rename Vc8 into Vc.
destruct (al_const _ _ LAWS _ _ _ _ _ HARc) as (Kcell0 & _ & Kgot0 & _). rewrite HBgot, HBcell in Kgot0. rewrite HBcell in Kcell0.
destruct (al_const _ _ LAWS _ _ _ _ _ (proj1 HJ8)) as (Kcell1 & _ & Kgot1 & _). rewrite HBgot, HBcell in Kgot1. rewrite HBcell in Kcell1.
assert (Hfin8 : In (cid, pos) (frames S7)) by (rewrite Hfrs7; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos (proj1 HJ8) Hfin8) as (_ & _ & HFpres8 & _). rewrite !EFA7 in HFpres8.
reseatL HS HJ8 HP8 [0; 1; 2; 3]%nat AG
ltac:(first [ eapply region_kept_aview;
[ evalER AG
| intros a Ha; apply Hfr8;
[ clear - Ha HSPB HDST0 HDSTC HTS Has C1; lia
| first [ clear - Ha HSPB HDST0 HDSTC HrCeil Hrql2 HTS Has C1; lia | intros X; apply (HnewF a); [clear - Ha Hdst1 Hdst2; lia | split; [clear - Hr4096; lia | clear - X Hrql2; lia]] ]
| first [ clear - Ha Hst1; lia | clear - Ha Hsd; unfold rboxed in Hsd; lia ]
| clear - Ha HSPB HDST0 HDSTC HTS Has C1; unfold ESTACK; lia ]
| first [ exact Hpres8 | intros a Ha; apply Hpres8; apply (proj1 (HFpres8 a ltac:(clear - Ha Hdst1 Hdst2; lia))) ] ]
| apply (region_kept_val tfibsegs _ _ _ A_GOT_shadow 8 A_shadow_glob); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kgot1) | lia]
| apply (region_kept_val tfibsegs _ _ _ A_shadow_glob 8 SHADOW_OFF); [exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell0) | exact (val_mem_of_rdword tfibsegs _ _ _ _ Kcell1) | lia]
| match goal with |- ?g => idtac "KEPTFAIL" g end ]).
clear Kcell0 Kgot0 Kcell1 Kgot1.
renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
reshok_bx HS 32%nat.
rreg HS (10%bv : bv 5) Rr6. cbn [ms_regs] in Rr6. rewrite Ha08 in Rr6. symmetry in Rr6. unfold w64 in Rr6.
assert (Hcb6 : cur <= cur6 <= nb) by (clear - Hr6 Hcb5 Hnb Hcur Rnlp; destruct Hr6 as [(_ & X & -> & _)|(_ & _ & -> & _)]; lia).
assert (Hrc6 : rboxed ((rpal = 0 /\ cur6 = cur5 + 3 * nlp /\ cur5 + 3 * nlp <= nb) \/ (rpal = 2 ^ 64 - 1 /\ cur6 = nb /\ nb < cur5 + 3 * nlp))) by (clear - Hr6; unfold rboxed; destruct Hr6 as [(A1 & X & A2 & _)|(A1 & X & A2 & _)]; [left; split; [exact A1 | split; [exact A2 | exact X]] | right; split; [exact A1 | split; [exact A2 | exact X]]]).
assert (Hrr6 : 0 <= rpal < 2 ^ 64) by (unfold rboxed in Hrc6; clear - Hrc6; lia).
assert (RDP : rpal = 0 -> forall i, 0 <= i < 3 * nlp -> aview tfibsegs (w_H W7) mem8 (res + i) = aview tfibsegs (w_H W) memc (pdata + (cur5 + i))).
{ intros Hz i Hi. destruct Hr6 as [(_ & Hle & _ & Hcp)|(Hne & _)]; [|exfalso; clear - Hne Hz; lia].
rewrite (Hcp i Hi). replace (pdata + cur5 + i) with (pdata + (cur5 + i)) by (clear; lia).
apply (proj1 (proj2 KEPT7s) pdata nb (cur5 + i) Hpd). clear - Hi Hle Hcb5 Hcur Hnb; unfold req_size; destruct (Z.eqb_spec nb 0); lia. }
assert (DRF : res + req_size (3 * nlp) <= frame_addr lyc cid pos \/ frame_addr lyc cid pos + fs_frame_bytes cid <= res).
{ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) cid pos HAR7 HrIn Hfin7) as D. rewrite EFA7 in D. unfold zdisjoint, block_rng, frame_rng in D. cbn [fst snd] in D. clear - D. lia. }
clear Hr6 Ha08.
aj_run_to_tok tfibtbl_lib_ok HS HJ8 SHOK RBspan RFC_I.
{ awrRFC Uspn E10n E11n Hown EFA7. }
unrunRD HFr Zsm Usp B10 Usp UNf. clear HF HFr HG.
vkeepUN UNf Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1 Hsd; unfold rboxed in Hsd; lia]).
lazymatch type of UNf with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
rkeep RDP (w_H W7) m2 ltac:(apply UNf; [clear - Hi Hr4096 HrCeil Hrql2 C1; lia | subst Zsm; cbn beta; clear - Hi Hrql2 DRF Hdst1 Hdst2 Hr4096 HrCeil HSPB HTS Has C1; lia]) end.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msX) =>
assert (SHKI : forall a, SB <= a < kHighShadowEnd -> aview tfibsegs (w_H W7) (ms_mem msX) a = aview tfibsegs (w_H W7) mem7 a) end.
{ intros a Ha. rewrite (UNf a) by first [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)].
rewrite (Hfr8 a); [| clear - Ha C2; unfold SB in Ha; lia | clear - Ha HrHi Hrql2 C2 C3; unfold rboxed in HrHi; unfold SB in Ha; lia | clear - Ha HSTB C1 C2; unfold SB in Ha; lia | clear - Ha HSPB HTS Has Hes C1 C2; unfold SB in Ha; lia].
apply UN7; [clear - Ha C2; unfold SB in Ha; lia | exact (ZBsm a Ha)]. }
pose proof (RA_kept_band _ _ dst 32 SHKI ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst7) as RAdstI. clear SHKI.
lazymatch type of Hfr8 with forall a, _ -> _ -> _ -> _ -> aview _ _ _ a = aview _ _ ?mY a =>
assert (UN8 : forall a, 0 <= a < 2 ^ 64 -> ~ (res <= a < res + 3 * nlp \/ st + 16 <= a < st + 24 \/ spZ regs - 96 - 32 - ESTACK <= a < spZ regs - 96) ->
aview tfibsegs (w_H W7) mem8 a = aview tfibsegs (w_H W7) mY a) end.
{ intros a Ha Hn. apply (Hfr8 a Ha); clear - Hn; lia. }
pose proof (rfc_kept_stepE B _ _ _ _ _ _ _ _ _ _ _ _ (fun a => res <= a < res + req_size (3 * nlp)) KEPT7s HSEP UN8
ltac:(intros a Ha; cbn beta in Ha |- *; clear - Ha Hrql2 HTS Has Hes; lia) ltac:(clear - HSPB; lia) ltac:(intros a Ha; cbn beta in Ha |- *; clear - Ha HrCeil; lia)
ltac:(intros b m i Hb Hi Hin; cbn beta in Hin; pose proof (HsepB b m Hb) as Hd; clear - Hd Hi Hin; lia)
ltac:(intros c p a Hcp Ha Hin; cbn beta in Hin; destruct Ha as [Ha | Ha];
[ pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ res (3 * nlp) c p HAR7 (HresIn ltac:(clear - Hr4096; lia)) ltac:(rewrite Hfrs7; exact Hcp)) as D;
rewrite EFA7 in D; unfold zdisjoint, frame_rng, in_zr in D, Ha; cbn [fst snd] in D, Ha; clear - D Ha Hin; lia
| destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ c p HAR7 ltac:(rewrite Hfrs7; exact Hcp)) as (F0 & Fc & Fh); rewrite EFA7 in F0, Fc, Fh;
pose proof (frame_shadow_low (frame_addr lyc c p) c a ltac:(clear - F0; lia) Fc Ha) as Hlow; clear - Hlow Hin HrHi Hrql2 C2 C3; unfold rboxed in HrHi; lia ])
ltac:(intros a Ha Him; cbn beta in Ha; pose proof (tfib_img_range a Him) as Hir; clear - Ha Hir HrHi Hrql2; unfold rboxed in HrHi; lia)) as KEPT8.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zsm KEPT8 HSEP UNf ltac:(intros a Ha; subst Zsm; cbn beta in Ha; clear - Ha HTS Has; lia) ltac:(clear - HSPB; lia)) as KEPT.
clear KEPT7s KEPT8 UN8 UNf UN7.
rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4. rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9.
rreg HS (18%bv : bv 5) Q18. rreg HS (20%bv : bv 5) Q20. rreg HS (25%bv : bv 5) Q25. rreg HS (26%bv : bv 5) Q26. rreg HS (27%bv : bv 5) Q27.
pose proof (rfcA_Z_lor_bound racc rpal 64 ltac:(clear; lia) Hl5 Hrr6) as Hl6.
lazymatch type of Q20 with getr ?rg _ = _ => assert (HRACC : bv_unsigned (getr rg 20) = Z.lor racc rpal) end.
{ rewrite Q20. cbn [ms_regs]. enorm. agnorm. rewrite Rr1, Rr2, Rr3, Rr4, Rr5, Rr6.
rewrite (rfcA_alu_or_lits r2 r1 Hrr2 Hrr1), (rfcA_alu_or_lits r3 r4 Hrr3 Hrr4), (rfcA_alu_or_lits _ _ Hl21 Hl34), (rfcA_alu_or_lits _ _ Hl4 Hrr5).
subst racc. rewrite (rfcA_alu_or_lits _ _ Hrr6 Hl5), (Z.lor_comm rpal). apply unsigned_lit_small. clear - Hl6. lia. }
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRd; cbn [ms_mem restrict] in HRd;
pose proof (st_ok_region_nth Ex ssx (restrict _ msX) 1%nat _ HS ltac:(vm_compute; reflexivity)) as HRs; cbn [ms_mem restrict] in HRs end.
let nres := lazymatch type of Rres with ew _ ?nx = _ => nx end in
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 0 8 (SOff nres 0) res HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite Rres, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; clear - Hr4096 HrCeil Hrql1 C1; lia) ltac:(cbn; lia)) as Vl.
pose proof (zero_of_region _ _ 11%nat dst _ _ _ _ _ 8 8 (dst + 8) 8 HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as Vz.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 16 4 (SOff 132 0) fattr HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Efattr, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfa.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 20 4 (SOff 133 0) fgen HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Efgen, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vfg.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 24 2 (SOff 134 0) delay HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Edelay, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vde.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 26 2 (SOff 135 0) nlp HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Enlp, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vnl.
pose proof (field_of_region _ _ 11%nat dst _ _ _ _ _ 28 1 (SOff 136 0) tidx HRd ltac:(enorm; agnorm; exact B11) ltac:(cbn; tauto) ltac:(cbn [sv_denot]; enorm; agnorm; rewrite ?Etidx, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vti.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vl, Vfa, Vfg, Vde, Vnl, Vti. rewrite ?Z.add_0_r in Vl.
pose proof (rfc_frame_of_stackA _ _ regs _ _ _ _ _ HRs ltac:(enorm; agnorm; exact Usp)
ltac:(intros j Hj; do 11 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 11 (destruct j as [|j]; [cbn [nth rfc_saved Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; enorm; agnorm; rewrite (proj1 HAE) by lia; apply ew_Ereg_nat; reflexivity|]); exfalso; clear - Hj; lia)) as HFR.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc]. change (Z_to_bv 64 526976) with (Z_to_bv 64 RFC_I).
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
eapply (RI STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
W7 (ms_regs msX) (ms_mem msX) mdX ly7 S7 (k + 1) (bv_unsigned (getr (ms_regs msX) 20)) cur6 res nlp fattr fgen delay tidx [(res, 3 * nlp)] T (0 + mo_malloc MT (3 * nlp)) P);
[ exact RC | exact HPL | exact (mle_station MT Sc Sc S7 0 (mo_malloc MT (3 * nlp)) MTL HMLE HMLE7)
| pose proof (mo_malloc_mono MT MTL (3 * nlp) 196605 ltac:(clear - Rnlp; lia)) as Hmm; clear - Hmm; lia
| exact Hhdrv
|
rewrite HRACC; unfold rfc_progP, palsz; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [Hb0|Hb0']; [exfalso; exact (Hbit Hb0)|];
unfold rboxed in Hrc6;
destruct (Z.eq_dec (Z.lor racc rpal) 0) as [Hz|Hnz];
[ pose proof (proj1 (Z.lor_eq_0_iff _ _) Hz) as [Hz1 Hz2]; left;
destruct HprogH as [(_ & Hfit & Ecv) | (Hne & _)]; [| exfalso; exact (Hne Hz1)];
split; [exact Hz|]; split; [clear - Hz2 Hrc6 Hfit Ecv; lia|]; split; [clear - Hz2 Hrc6 Ecv; lia|];
intros _; apply garr8_of_aview; intros j Hj;
rewrite firstn_length_le in Hj by (rewrite length_skipn; clear - Hz2 Hrc6 Ecv HlenP Hcur Rnlp; lia);
rewrite slice_nth by (rewrite firstn_length_le by (rewrite length_skipn; clear - Hz2 Hrc6 Ecv HlenP Hcur Rnlp; lia); exact Hj);
rewrite (RDP Hz2 (Z.of_nat j)) by (clear - Hj; lia);
replace (pdata + (cur5 + Z.of_nat j)) with (pdata + Z.of_nat (Z.to_nat (cur + 9) + j)) by (clear - Ecv Hcur; lia);
rewrite (garr8_aview _ _ _ _ HPL) by (clear - Hj Hz2 Hrc6 Ecv HlenP Hcur; lia); reflexivity
| right; split; [exact Hnz|];
assert (Hcase : racc <> 0 \/ rpal <> 0) by (destruct (Z.eq_dec racc 0) as [Z0|Z0]; [right; intros Zp; apply Hnz; rewrite Z0, Zp; reflexivity | left; exact Z0]);
destruct HprogH as [(Hz1 & Hfit & Ecv) | (Hne & Hsh & Ecv)];
[ destruct Hcase as [X|X]; [exfalso; exact (X Hz1) | clear - X Hrc6 Hfit Ecv Rnlp; lia]
| clear - Hrc6 Hsh Ecv Rnlp Hcb5; lia ] ]
| exact HJ8 | clear; lia | exact Hfrs7 | exact HPerm7
|   unfold rfc_pal; destruct (Z.eqb_spec (Z.land fattr 1) 0) as [X|X]; [exfalso; exact (Hbit X)|];
split; [reflexivity|]; split; [intros X2; exfalso; exact (Hbit X2)|]; split;
[ intros b [<-|[]]; split; [exact Tpal | intros lyq blc i Hin Hi; cbn [fst snd] in Hin, Hi |- *; exact (Apal blc i lyq Hin Hi)]
| intros b m [Hb|[]]; injection Hb as <- <-; split; [exact Hr4096 | exact HnotBb] ]
|   unfold rfc_vals; split; [pose proof (bv_unsigned_in_range 64 (getr (ms_regs msX) 20)) as HR; change (bv_modulus 64) with (2 ^ 64) in HR; exact HR|];
split; [exact Hcb6|]; split; [clear - Hr4096 HrCeil Hrql1 C1; lia|]; split; [exact Rnlp|]; split; [exact Rfattr|]; split; [exact Rfgen|]; split; [exact Rdelay|]; clear - Rtidx; lia
|   unfold I_regs_at, w64; rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q25, Q26, Q27; enorm; agnorm;
rewrite E3, E4, E11, E12, E10, E32, Usp, Z_to_bv_bv_unsigned, (EE 26%nat 26%bv eq_refl), (EE 27%nat 27%bv eq_refl);
repeat split; try reflexivity; f_equal; lia
| exact HFR
| unfold rfc_memI; split; [exact Vp|]; split; [exact Vn|]; split; [exact Vc|]; split; [exact Vl|]; split; [exact Vz|]; split; [exact Vfa|]; split; [exact Vfg|]; split; [exact Vde|]; split; [exact Vnl | exact Vti]
| exact RAdstI
| exact KEPT
| io_now ] end.
Qed.
End RA.
End d.
