(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YI09 YI0m YI0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI00 YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v ACef AF0l ACej ACeh ACem ACei ACep.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YCeo.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACes ACew ACex ACey.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
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
Ltac oblPD HJx Hpdc EQx E32x btac :=
lazymatch goal with |- range_addressable _ (U ?Ex _) (U _ (SOff ?q ?c)) _ =>
rewrite (U_atom_off Ex q _ c ltac:(first [exact EQx | enorm; exact EQx | enorm; agnorm; exact EQx])) by btac;
eapply obl_of_range;
[ let LAWSx := aj_laws in eapply (range_addressable_of_block _ _ LAWSx); [exact (proj1 HJx) | exact Hpdc | apply Z.le_refl | apply Z.le_refl]
| rewrite (U_atom Ex 32 SB ltac:(enorm; agnorm; exact E32x)) by (unfold SB; lia); reflexivity | btac | btac ] end.
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
Lemma rfcA_geu_atoms : forall E a b c va vb, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va < 2 ^ 64 -> 0 <= vb < 2 ^ 64 -> 0 <= vb + c < 2 ^ 64 ->
  branch_taken BC_GEU (sv_denot E (SOff a 0)) (sv_denot E (SOff b c)) = (vb + c <=? va).
Proof.
intros E a b c va vb Ha Hb Ra Rb Rbc. rewrite branch_geu_U, (U_atom E a va Ha Ra), (U_atom_off E b vb c Hb Rb Rbc).
destruct (Z.ltb_spec va (vb + c)), (Z.leb_spec (vb + c) va); cbn [negb]; first [reflexivity | lia].
Qed.
Ltac geuDec Hc va vb Ea Eb btac :=
  lazymatch type of Hc with branch_taken BC_GEU (sv_denot ?Ex (SOff ?a 0)) (sv_denot _ (SOff ?b ?c)) = _ =>
  rewrite (rfcA_geu_atoms Ex a b c va vb) in Hc by first [enorm; agnorm; exact Ea | enorm; agnorm; exact Eb | btac];
  first [apply Z.leb_le in Hc | apply Z.leb_gt in Hc] end.
Ltac geuDecA Hc nbv curv Enb Ecur btac :=
  lazymatch type of Hc with
  | branch_taken BC_GEU (sv_denot _ (SOff 34 0)) (sv_denot _ (SOff 35 _)) = _ => geuDec Hc nbv curv Enb Ecur btac
  | branch_taken BC_GEU (sv_denot _ (SOff 34 0)) (sv_denot _ (SOff 34 _)) = _ => geuDec Hc nbv nbv Enb Enb btac end.
Lemma byte_of_region : forall E m n b cs lo hi wlo whi od e v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem tfibsegs m (b + od) 1 (v mod 256).
Proof.
intros E m n b cs lo hi wlo whi od e v (_ & _ & _ & Hcs) Hn Hc He Hv.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
intros k Hk. assert (k = 0%nat) as -> by lia.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. rewrite He in Hb1. injection Hb1 as <-.
change (Z.of_nat 0) with 0. rewrite Z.add_0_r in Hb2 |- *. rewrite Hb2. f_equal.
pose proof (Z.mod_pos_bound v 256 ltac:(lia)) as Hm.
rewrite YI04.le_byte_small by (cbn; lia). change (8 * Z.of_nat 0) with 0. unfold byte_of_word. change (8 * 0) with 0.
rewrite !Z.shiftr_0_r, unsigned_lit_small by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rfcA_lor_pair : forall v0 v1, 0 <= v0 < 256 -> 0 <= v1 -> Z.lor (Z.shiftl v1 8) v0 = v0 + 256 * v1.
Proof.
intros v0 v1 R0 R1.
assert (Hs : Z.shiftl v1 8 = v1 * 2 ^ 8) by (apply Z.shiftl_mul_pow2; lia).
assert (Hland : Z.land v0 (Z.shiftl v1 8) = 0).
{ apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.ltb k 8) eqn:Ek.
  - apply Z.ltb_lt in Ek. rewrite Hs, Z.mul_pow2_bits_low by lia. apply andb_false_r.
  - apply Z.ltb_ge in Ek. replace (Z.testbit v0 k) with false; [reflexivity|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|].
    split; [lia|]. eapply Z.lt_le_trans; [apply R0|]. change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia. }
rewrite Z.lor_comm, <- Z.lxor_lor by exact Hland. rewrite <- Z.add_nocarry_lxor by exact Hland. rewrite Hs. lia.
Qed.
Definition sv_pair (a0 a1 : nat) : sv := SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff a1 0)) (SLit 8)) (SExt false 8 (SOff a0 0)).
Lemma U_pair : forall E a0 a1 v0 v1, ew E a0 = Z_to_bv 64 v0 -> ew E a1 = Z_to_bv 64 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  U E (sv_pair a0 a1) = v0 + 256 * v1.
Proof.
intros E a0 a1 v0 v1 H0 H1 R0 R1. unfold sv_pair. rewrite !U_SAlu. cbn [zalu_raw].
rewrite !U_SExt, U_SLit, (U_atom E a0 v0 H0), (U_atom E a1 v1 H1) by lia. cbn [Z.of_N].
rewrite (Z.mod_small v0), (Z.mod_small v1) by lia.
rewrite (zcanon_id v0), (zcanon_id v1), (zcanon_id 8) by (unfold M64; lia). change (Z.land 8 63) with 8.
rewrite (zcanon_id (Z.shiftl v1 8)) by (rewrite Z.shiftl_mul_pow2 by lia; unfold M64; lia).
rewrite rfcA_lor_pair by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma denot_pair : forall E a0 a1 v0 v1, ew E a0 = Z_to_bv 64 v0 -> ew E a1 = Z_to_bv 64 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  sv_denot E (sv_pair a0 a1) = Z_to_bv 64 (v0 + 256 * v1).
Proof. intros E a0 a1 v0 v1 H0 H1 R0 R1. rewrite denot_lit_U. f_equal. exact (U_pair E a0 a1 v0 v1 H0 H1 R0 R1). Qed.
Lemma denot_pair_hi : forall E a0 a1 v0 v1, ew E a0 = Z_to_bv 64 v0 -> ew E a1 = Z_to_bv 64 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  sv_denot E (SAlu ALU_SRL (sv_pair a0 a1) (SLit 8)) = Z_to_bv 64 v1.
Proof.
intros E a0 a1 v0 v1 H0 H1 R0 R1. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_pair E a0 a1 v0 v1 H0 H1 R0 R1), U_SLit, (zcanon_id 8) by (unfold M64; lia). change (Z.land 8 63) with 8.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace ((v0 + 256 * v1) / 256) with v1 by (apply (Z.div_unique (v0 + 256 * v1) 256 v1 v0); lia).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma pair_of_region : forall E m n b cs lo hi wlo whi od a0 a1 v0 v1,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (sv_pair a0 a1))) cs -> In (YP09.mkChunk (od + 1) (CVal 1 (SAlu ALU_SRL (sv_pair a0 a1) (SLit 8)))) cs ->
  ew E a0 = Z_to_bv 64 v0 -> ew E a1 = Z_to_bv 64 v1 -> 0 <= v0 < 256 -> 0 <= v1 < 256 ->
  val_mem tfibsegs m (b + od) 2 (v0 + 256 * v1).
Proof.
intros E m n b cs lo hi wlo whi od a0 a1 v0 v1 HR Hn Hc0 Hc1 H0 H1 R0 R1.
pose proof (byte_of_region E m n b cs lo hi wlo whi od _ _ HR Hn Hc0 (denot_pair E a0 a1 v0 v1 H0 H1 R0 R1) ltac:(lia)) as V0.
pose proof (byte_of_region E m n b cs lo hi wlo whi (od + 1) _ _ HR Hn Hc1 (denot_pair_hi E a0 a1 v0 v1 H0 H1 R0 R1) ltac:(lia)) as V1.
replace ((v0 + 256 * v1) mod 256) with v0 in V0 by (apply (Z.mod_unique (v0 + 256 * v1) 256 v1 v0); lia).
rewrite (Z.mod_small v1) in V1 by lia. replace (b + (od + 1)) with (b + od + 1) in V1 by lia.
exact (val_mem_bytes2 _ _ _ _ V0 V1 R0 R1).
Qed.
Fixpoint ridx (n : nat) (rs : list YP09.region) : nat :=
  match rs with
  | [] => O
  | r :: rs' => match YP09.r_base r with Some m => if Nat.eqb m n then O else S (ridx n rs') | None => S (ridx n rs') end
  end.
Fixpoint zfind (o w : Z) (cs : list YP09.chunk) : option (Z * Z) :=
  match cs with
  | [] => None
  | c :: cs' => match YP09.c_val c with
    | CZero len => if (YP09.c_off c <=? o) && (o + w <=? YP09.c_off c + len) then Some (YP09.c_off c, len) else zfind o w cs'
    | _ => zfind o w cs' end
  end.
Ltac regionOf HS n Hn :=
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let i := eval vm_compute in (ridx n (ss_mem ssx)) in
  pose proof (st_ok_region_nth Ex ssx (restrict _ msX) i _ HS ltac:(vm_compute; reflexivity)) as Hn; cbn [ms_mem restrict] in Hn end.
Ltac zeroAt HR Bx o w V :=
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ ?cs) =>
  lazymatch type of Bx with bv_unsigned _ = ?b =>
  lazymatch eval vm_compute in (zfind o (Z.of_nat w) cs) with Some (?od, ?len) =>
  pose proof (zero_of_region _ _ n b _ _ _ _ _ od len (b + o) w HR ltac:(first [exact Bx | enorm; agnorm; exact Bx]) ltac:(cbn; tauto) ltac:(lia) ltac:(cbn; lia)) as V end end end.
Ltac rregS HS r Hr :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let rg := eval cbn [ms_regs restrict mkst] in (ms_regs ms) in
  assert (Hr : getr rg r = sv_denot E e) by (exact (st_ok_restrict_reg segs H E ss ms r HS)) end.
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
Lemma rfc_A_ok : RFC_C1_stmt B MT -> trfc_specX B MT.
Proof.
intros RC1. unfold trfc_specX.
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
change (Z_to_bv 64 334456) with (Z_to_bv 64 A_asan_memset_tfb).
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
assert (D32 : forall i, 0 <= i < 32 -> aview tfibsegs (w_H W) mem1 (dst + i) = Some 0) by (intros i Hi; rewrite (Heff1 i ltac:(lia)); reflexivity).
clear Heff1 Hfr1 Hpres1 Ha01.
norm_ss HS. renv HS AG E10 E11 E32 Usp st dst E10n E11n E32n Uspn B10n B11n.
reshok_bx HS 32%nat.
shkOf KE ZB SHK.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan (A_read_frameconfig + 132).
all: try (oblRD RAstN E10 E32).
{ awrRFC Uspn E10n E11n Hown EFA0. }
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs.
dkeep D16 UNs ltac:(first [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]).
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ => dhkeep DH (w_H W) m2 ltac:(apply UNs; [clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
lazymatch type of UNs with forall a, _ -> _ -> aview _ _ ?m2 a = _ =>
  assert (D32' : forall i, 0 <= i < 32 -> aview tfibsegs (w_H W) m2 (dst + i) = Some 0)
  by (intros i Hi; rewrite (UNs (dst + i)); [exact (D32 i Hi) | clear - Hi HDST0 HDSTC C1; lia | subst Zsm; cbn beta; clear - Hi HDSTC HSPB HTS Has C1; lia]) end.
clear D32. rename D32' into D32.
vkeepUN UNs Vp Vn Vc ltac:(first [clear - Hi HSTB C1; lia | subst Zsm; cbn beta; clear - Hi Hst1; lia]). clear UNs.
clear Zsm. set (Zsm := fun a : Z => spZ regs - 96 <= a < spZ regs \/ dst + 16 <= a < dst + 29 \/ st + 16 <= a < st + 24).
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (st_region 10 (SOff 33 0) (SOff 34 0) (SOff 35 0)) HS eq_refl
  ltac:(unfold st_region, region_ok; cbn [Nat.add YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    enorm; agnorm; rewrite B10;
    split; [clear - HSTB C1; lia|]; split; [clear - HSTB C1; lia|]; split;
    [ intros q Hq; apply (apresent_writable tfibsegs); apply PR; apply Hpres; clear - Hq Hst1 Hst2 Hwlo HTS Has; lia
    | apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      [ apply (chunk_ok_val tfibsegs _ _ st 0 8 _ pdata); [cbn [sv_denot]; enorm; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | rewrite Z.add_0_r; exact Vp]
      | apply (chunk_ok_val tfibsegs _ _ st 8 8 _ nb); [cbn [sv_denot]; enorm; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn]
      | apply (chunk_ok_val tfibsegs _ _ st 16 8 _ cur); [cbn [sv_denot]; enorm; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vc] ] ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold st_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    enorm; agnorm; rewrite B10, Usp;
    unfold A_GOT_shadow, A_shadow_glob; clear - HSPB HSTB Hst1 HTS Has C1; repeat split; lia)) as HS2 end.
clear HS; rename HS2 into HS; norm_ss HS.
lazymatch type of HS with st_ok _ ?Ev _ _ =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (YP09.mkRegion (Some 11%nat) 0 32 16 29 [YP09.mkChunk 0 (CZero 32)]) HS eq_refl
  ltac:(unfold region_ok; cbn [Nat.add YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
    enorm; agnorm; rewrite B11;
    split; [clear - HDST0 HDSTC C1; lia|]; split; [clear - HDST0 HDSTC C1; lia|]; split;
    [ intros q Hq; apply (apresent_writable tfibsegs); apply PR; apply (proj1 (HFpres (dst + q) ltac:(clear - Hq Hdst1 Hdst2; lia)))
    | apply Forall_cons; [|apply Forall_nil];
      apply (chunk_ok_zero tfibsegs); intros i Hi; rewrite Z.add_0_r;
      destruct (aview_byte tfibsegs (w_H W) _ (dst + i) 0 (D32 i Hi)) as (bb & Hbb & Hv & _); rewrite Hbb; f_equal; apply bv_eq; rewrite Z_to_bv_unsigned; change (bv_wrap 8 0) with 0; clear - Hv; lia ])
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    enorm; agnorm; rewrite B11, B10, Usp;
    unfold A_GOT_shadow, A_shadow_glob; clear - HSPB HDST0 HDSTC HDSTI HDSTH Hsd HTS Has C1; unfold rboxed in HDSTI, HDSTH, Hsd; repeat split; lia)) as HS2 end.
clear HS; rename HS2 into HS; norm_ss HS.
clear D16 DH D32.
destruct (Z_le_gt_dec (cur + 2) nb) as [HC2|HC2].
{
assert (GB : forall j, 0 <= j < 2 -> aview tfibsegs (w_H W) (ms_mem ms0) (pdata + (cur + j)) = Some (hb P cur j)).
{ intros j Hj. rewrite (KE (pdata + (cur + j))).
  - unfold hb. replace (pdata + (cur + j)) with (pdata + Z.of_nat (Z.to_nat (cur + j))) by (clear - Hj Hcur; lia).
    apply (garr8_aview _ _ _ _ HPL). clear - Hj Hcur HC2 HlenP. lia.
  - clear - Hj Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia.
  - subst Zs; cbn beta; unfold rboxed in Hpdst; clear - Hj Hcur HC2 Hp4096 Hpceil Hrq2 HSPB Hpdst Hdst1 Hdst2 Hst1 HTS Has; lia. }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
let WS := constr:(map (Z_to_bv 64) ((pdata + cur) :: map (fun i => hb P cur (Z.of_nat i)) (seq 0 2))) in
pose proof (st_ok_havoc_win tfibsegs K Ev ssv msv WS HS ltac:(vm_compute; reflexivity)) as HS3; clear HS; rename HS3 into HS;
assert (EQ : ew (havoc Ev K WS) K = Z_to_bv 64 (pdata + cur)) by (exact (ew_havoc_new Ev K WS 0 (Z_to_bv 64 0) ltac:(cbn; clear; lia)));
assert (EBy : forall i, (i < 2)%nat -> ew (havoc Ev K WS) (K + (1 + i)) = Z_to_bv 64 (hb P cur (Z.of_nat i)))
  by (intros i Hi; rewrite (ew_havoc_new Ev K WS (1 + i) (Z_to_bv 64 0)) by (cbn [length map seq]; clear - Hi; lia);
      do 2 (destruct i as [|i]; [reflexivity|]); clear - Hi; lia)
end.
assert (HBR : forall j, 0 <= j < 2 -> 0 <= hb P cur j < 256)
  by (intros j Hj; destruct (aview_byte tfibsegs _ _ _ _ (GB j Hj)) as (bb & _ & _ & Hr); exact Hr).
assert (VB2 : forall i, (i < 2)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms0)) (pdata + cur + Z.of_nat i) 1 (hb P cur (Z.of_nat i))).
{ intros i Hi. replace (pdata + cur + Z.of_nat i) with (pdata + (cur + Z.of_nat i)) by (clear; lia).
  exact (val_mem1_of_aview _ _ _ _ (GB (Z.of_nat i) ltac:(clear - Hi; lia))). }
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_alias tfibsegs Ev ssv msv (SAlu ALU_ADD (SOff 33 0) (SOff 35 0)) (SOff 52 0) HS
  ltac:(transitivity (Z_to_bv 64 (pdata + cur));
        [ apply denot_add_atoms; [enorm; exact E33 | enorm; exact E35 | clear - Hp4096; lia | clear - Hcur; lia | clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia]
        | cbn [sv_denot]; rewrite EQ, unsigned_lit_small by (clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia); rewrite Z.add_0_r; reflexivity ])) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (st_ok_add_fact tfibsegs Ev ssv msv 52%nat (mkAF 4096 0x7fffff800000 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite EQ, unsigned_lit_small by (clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia);
        rewrite Z.pow_0_r, Z.mod_1_r; unfold alloc_ceiling in *; clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia)) as HS3;
clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
pose proof (ast_ok_add_region tfibsegs _ _ _ (src_region 52 2) HS eq_refl
  (src_region_ok Ev _ 52 2 (pdata + cur) (fun i => hb P cur (Z.of_nat i))
     ltac:(rewrite EQ; apply unsigned_lit_small; clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia)
     ltac:(clear - Hcur Hp4096; lia) ltac:(cbn; clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia)
     ltac:(intros i Hi; split; [exact (EBy i Hi) | split; [exact (HBR (Z.of_nat i) ltac:(clear - Hi; lia)) | exact (VB2 i Hi)]]))
  ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
    unfold src_region; cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite EQ, unsigned_lit_small by (clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB C1; lia);
    enorm; agnorm; rewrite B11, B10, Usp;
    unfold A_GOT_shadow, A_shadow_glob, off_img in *; unfold rboxed in *;
    clear - Hcur HC2 Hp4096 Hpceil Hrq2 HSPB Hpdst Hdst1 Hdst2 Hst1 Hph_img HTS Has C1; cbn; repeat split; lia)) as HS3;
clear HS; rename HS3 into HS end.
pose proof (EBy 0%nat ltac:(lia)) as EB0. pose proof (EBy 1%nat ltac:(lia)) as EB1. cbn [Nat.add Z.of_nat] in EB0, EB1. clear EBy GB VB2.
clear Vp Vn Vc.
reshok_bx HS 32%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblRD RAstN E10 E32). all: try (oblDST RAdstN E11 E32). all: try (oblPD HJ1 Hpdc EQ E32 ltac:(clear - Hcur HC2 Hrq1 Hrq2 Hp4096 Hpceil HSPB C1; unfold alloc_ceiling in *; lia)).
all: try (awrRFC Uspn E10n E11n Hown EFA0).
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs. clear UNs.
shkOf KE ZB SHK. clear RAstN RAdstN.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
all: geuDecA Hc nb cur E34 E35 ltac:(clear - Hcur Hnb HnbM; lia).
2: { exfalso; clear - Hc HC2; lia. }
rename Hc into Hb1.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan (A_read_frameconfig + 304).
all: try (oblRD RAstN E10 E32). all: try (oblDST RAdstN E11 E32). all: try (oblPD HJ1 Hpdc EQ E32 ltac:(clear - Hcur HC2 Hrq1 Hrq2 Hp4096 Hpceil HSPB C1; unfold alloc_ceiling in *; lia)).
all: try (awrRFC Uspn E10n E11n Hown EFA0).
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs. clear UNs.
shkOf KE ZB SHK. try clear RAstN. try clear RAdstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstF. clear SHK.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zs (rfc_kept_refl B W memc (spZ regs) Bb lyc Sc st dst) HSEP KE ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT.
lazymatch type of HS with st_ok _ ?Ef _ _ =>
assert (F3 : ew Ef 3 = Z_to_bv 64 (as_gp B)) by (enorm; agnorm; exact E3);
assert (F4 : ew Ef 4 = Z_to_bv 64 (as_tp B)) by (enorm; agnorm; exact E4);
assert (F2 : ew Ef 2 = Z_to_bv 64 (spZ regs)) by (enorm; agnorm; rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
assert (F10 : ew Ef 10 = Z_to_bv 64 st) by (enorm; agnorm; exact E10);
assert (F11 : ew Ef 11 = Z_to_bv 64 dst) by (enorm; agnorm; exact E11);
assert (F12 : ew Ef 12 = Z_to_bv 64 N) by (enorm; agnorm; exact E12);
assert (F32 : ew Ef 32 = Z_to_bv 64 SB) by (enorm; agnorm; exact E32);
assert (F33 : ew Ef 33 = Z_to_bv 64 pdata) by (enorm; agnorm; exact E33);
assert (F34 : ew Ef 34 = Z_to_bv 64 nb) by (enorm; agnorm; exact E34);
assert (F35 : ew Ef 35 = Z_to_bv 64 cur) by (enorm; agnorm; exact E35);
assert (F27 : ew Ef 27 = getr regs 27) by (enorm; agnorm; exact (EE 27%nat 27%bv eq_refl));
assert (B10f : bv_unsigned (ew Ef 10) = st) by (rewrite F10; apply unsigned_lit_small; lia);
assert (B11f : bv_unsigned (ew Ef 11) = dst) by (rewrite F11; apply unsigned_lit_small; lia);
assert (B2f : bv_unsigned (ew Ef 2) = spZ regs) by (enorm; agnorm; exact Usp)
end.
regionOf HS 11%nat HRd. regionOf HS 10%nat HRt. regionOf HS 2%nat HRs.
pose proof (field_of_region _ _ 10%nat st _ _ _ _ _ 0 8 (SOff 33 0) pdata HRt B10f ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vp.
pose proof (field_of_region _ _ 10%nat st _ _ _ _ _ 8 8 (SOff 34 0) nb HRt B10f ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vn.
pose proof (field_of_region _ _ 10%nat st _ _ _ _ _ 16 8 (SOff 35 0) cur HRt B10f ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp, Vn, Vc. rewrite Z.add_0_r in Vp.
zeroAt HRd B11f 0 8%nat Vl. rewrite Z.add_0_r in Vl.
zeroAt HRd B11f 8 8%nat Vz. zeroAt HRd B11f 20 4%nat Vfg. zeroAt HRd B11f 24 2%nat Vde. zeroAt HRd B11f 26 2%nat Vnl. zeroAt HRd B11f 28 1%nat Vti.
pose proof (rfc_frame_of_stackA _ _ regs _ _ _ _ _ HRs B2f
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; enorm; agnorm; rewrite (proj1 HAE) by lia; apply ew_Ereg_nat; reflexivity|]); exfalso; clear - Hj; lia)) as HFR.
rregS HS (2%bv : bv 5) Q2. rregS HS (3%bv : bv 5) Q3. rregS HS (4%bv : bv 5) Q4. rregS HS (8%bv : bv 5) Q8. rregS HS (9%bv : bv 5) Q9.
rregS HS (10%bv : bv 5) Q10. rregS HS (13%bv : bv 5) Q13. rregS HS (14%bv : bv 5) Q14. rregS HS (15%bv : bv 5) Q15.
rregS HS (18%bv : bv 5) Q18. rregS HS (19%bv : bv 5) Q19. rregS HS (20%bv : bv 5) Q20. rregS HS (22%bv : bv 5) Q22.
rregS HS (23%bv : bv 5) Q23. rregS HS (24%bv : bv 5) Q24. rregS HS (27%bv : bv 5) Q27.
pose proof (HBR 0 ltac:(lia)) as HB0. pose proof (HBR 1 ltac:(lia)) as HB1.
pose proof (pair_of_region _ _ 11%nat dst _ _ _ _ _ 16 53 54 (hb P cur 0) (hb P cur 1) HRd B11f ltac:(cbn; tauto) ltac:(cbn; tauto) ltac:(enorm; agnorm; exact EB0) ltac:(enorm; agnorm; exact EB1) HB0 HB1) as V16.
zeroAt HRd B11f 18 2%nat V18. replace (dst + 18) with (dst + 16 + 2) in V18 by lia.
pose proof (val_mem_half2 _ _ _ _ V16 V18 ltac:(lia) ltac:(lia)) as Vfa. rewrite Z.mul_0_r, Z.add_0_r in Vfa.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_RD1 end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_mem msX) _ _ |- _ =>
eapply (RC1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
  W (ms_regs msX) (ms_mem msX) mdX 0 (cur + 2) (hb P cur 0 + 256 * hb P cur 1) T P);
[ exact RC | exact HPL | exact HJc
| unfold hdr1; split; [left; reflexivity|]; split; [left; split; [reflexivity|]; split; [exact HC2|]; split; reflexivity | lia]
| unfold C1_regs_at, I_regs_at; repeat match goal with |- _ /\ _ => split end;
  first
  [ rewrite Q23, (denot_shx _ 10 32 16 st SB F10 F32) by (try unfold SB; lia); reflexivity
  | rewrite Q24, (denot_shx _ 10 32 8 st SB F10 F32) by (try unfold SB; lia); reflexivity
  | rewrite Q14, (denot_srl3 _ 11 16 dst F11) by lia; reflexivity
  | rewrite Q15; cbn [sv_denot]; unfold w64; f_equal; lia
  | first [rewrite Q2 | rewrite Q3 | rewrite Q4 | rewrite Q8 | rewrite Q9 | rewrite Q10 | rewrite Q13 | rewrite Q18 | rewrite Q19 | rewrite Q20 | rewrite Q22 | rewrite Q27];
    cbn [sv_denot]; rewrite ?F2, ?F3, ?F4, ?F10, ?F11, ?F12, ?F32, ?F34, ?F35, ?F27; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    first [reflexivity | rewrite unsigned_lit_small by lia; unfold w64; f_equal; lia]
  | unfold w64; symmetry; apply Z_to_bv_bv_unsigned ]
| exact HFR
| unfold rfc_memI; exact (conj Vp (conj Vn (conj Vc (conj Vl (conj Vz (conj Vfa (conj Vfg (conj Vde (conj Vnl Vti)))))))))
| exact RAdstF
| exact KEPT
| io_now ] end end.
}
{
clear Vp Vn Vc.
reshok_bx HS 32%nat.
aj_run_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan.
all: try (oblRD RAstN E10 E32). all: try (oblDST RAdstN E11 E32).
all: try (awrRFC Uspn E10n E11n Hown EFA0).
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs. clear UNs.
shkOf KE ZB SHK. clear RAstN RAdstN.
pose proof (RA_kept_band _ _ st 24 SHK ltac:(lia) ltac:(clear - HSTB C4; lia) RAst) as RAstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstN. clear SHK.
srr_branch_tok tfibtbl_lib_ok HS SHOK RBspan.
all: geuDecA Hc nb cur E34 E35 ltac:(clear - Hcur Hnb HnbM; lia).
1: { exfalso; clear - Hc HC2; lia. }
rename Hc into Hb1.
reshok_bx HS 32%nat.
aj_run_to_tok tfibtbl_lib_ok HS HJ1 SHOK RBspan (A_read_frameconfig + 304).
all: try (oblRD RAstN E10 E32). all: try (oblDST RAdstN E11 E32).
all: try (awrRFC Uspn E10n E11n Hown EFA0).
keStepS HF HFr HG KE PR Zs Zsm Usp B10 Usp UNs. clear UNs.
shkOf KE ZB SHK. try clear RAstN. try clear RAdstN.
pose proof (RA_kept_band _ _ dst 32 SHK ltac:(lia) ltac:(clear - HDST0 HDSTC C1 C4; lia) RAdst) as RAdstF. clear SHK.
pose proof (rfc_kept_step B _ _ _ _ _ _ _ _ _ _ _ Zs (rfc_kept_refl B W memc (spZ regs) Bb lyc Sc st dst) HSEP KE ltac:(intros a Ha; exact Ha) ltac:(clear - HSPB; lia)) as KEPT.
lazymatch type of HS with st_ok _ ?Ef _ _ =>
assert (F3 : ew Ef 3 = Z_to_bv 64 (as_gp B)) by (enorm; agnorm; exact E3);
assert (F4 : ew Ef 4 = Z_to_bv 64 (as_tp B)) by (enorm; agnorm; exact E4);
assert (F2 : ew Ef 2 = Z_to_bv 64 (spZ regs)) by (enorm; agnorm; rewrite <- Usp; symmetry; apply Z_to_bv_bv_unsigned);
assert (F10 : ew Ef 10 = Z_to_bv 64 st) by (enorm; agnorm; exact E10);
assert (F11 : ew Ef 11 = Z_to_bv 64 dst) by (enorm; agnorm; exact E11);
assert (F12 : ew Ef 12 = Z_to_bv 64 N) by (enorm; agnorm; exact E12);
assert (F32 : ew Ef 32 = Z_to_bv 64 SB) by (enorm; agnorm; exact E32);
assert (F33 : ew Ef 33 = Z_to_bv 64 pdata) by (enorm; agnorm; exact E33);
assert (F34 : ew Ef 34 = Z_to_bv 64 nb) by (enorm; agnorm; exact E34);
assert (F35 : ew Ef 35 = Z_to_bv 64 cur) by (enorm; agnorm; exact E35);
assert (F27 : ew Ef 27 = getr regs 27) by (enorm; agnorm; exact (EE 27%nat 27%bv eq_refl));
assert (B10f : bv_unsigned (ew Ef 10) = st) by (rewrite F10; apply unsigned_lit_small; lia);
assert (B11f : bv_unsigned (ew Ef 11) = dst) by (rewrite F11; apply unsigned_lit_small; lia);
assert (B2f : bv_unsigned (ew Ef 2) = spZ regs) by (enorm; agnorm; exact Usp)
end.
regionOf HS 11%nat HRd. regionOf HS 10%nat HRt. regionOf HS 2%nat HRs.
pose proof (field_of_region _ _ 10%nat st _ _ _ _ _ 0 8 (SOff 33 0) pdata HRt B10f ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite F33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vp.
pose proof (field_of_region _ _ 10%nat st _ _ _ _ _ 8 8 (SOff 34 0) nb HRt B10f ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite F34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vn.
pose proof (field_of_region _ _ 10%nat st _ _ _ _ _ 16 8 (SOff 35 0) cur HRt B10f ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite F35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Vc.
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vp, Vn, Vc. rewrite Z.add_0_r in Vp.
zeroAt HRd B11f 0 8%nat Vl. rewrite Z.add_0_r in Vl.
zeroAt HRd B11f 8 8%nat Vz. zeroAt HRd B11f 20 4%nat Vfg. zeroAt HRd B11f 24 2%nat Vde. zeroAt HRd B11f 26 2%nat Vnl. zeroAt HRd B11f 28 1%nat Vti.
pose proof (rfc_frame_of_stackA _ _ regs _ _ _ _ _ HRs B2f
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn; tauto|]); exfalso; clear - Hj; lia)
ltac:(intros j Hj; do 12 (destruct j as [|j]; [cbn [nth rfc_saved Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; enorm; agnorm; rewrite (proj1 HAE) by lia; apply ew_Ereg_nat; reflexivity|]); exfalso; clear - Hj; lia)) as HFR.
rregS HS (2%bv : bv 5) Q2. rregS HS (3%bv : bv 5) Q3. rregS HS (4%bv : bv 5) Q4. rregS HS (8%bv : bv 5) Q8. rregS HS (9%bv : bv 5) Q9.
rregS HS (10%bv : bv 5) Q10. rregS HS (13%bv : bv 5) Q13. rregS HS (14%bv : bv 5) Q14. rregS HS (15%bv : bv 5) Q15.
rregS HS (18%bv : bv 5) Q18. rregS HS (19%bv : bv 5) Q19. rregS HS (20%bv : bv 5) Q20. rregS HS (22%bv : bv 5) Q22.
rregS HS (23%bv : bv 5) Q23. rregS HS (24%bv : bv 5) Q24. rregS HS (27%bv : bv 5) Q27.
zeroAt HRd B11f 16 4%nat Vfa.
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 ?p) _ _) _) _ => change p with RFC_RD1 end.
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem _) _) ?mdX) _ =>
lazymatch goal with HJc : ajournal _ _ _ _ _ _ _ _ _ _ _ lyc Sc W (ms_mem msX) _ _ |- _ =>
eapply (RC1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs Bb st dst N pdata nb cur cid pos
  W (ms_regs msX) (ms_mem msX) mdX (2 ^ 64 - 1) nb 0 T P);
[ exact RC | exact HPL | exact HJc
| unfold hdr1; split; [right; reflexivity|]; split; [right; split; [lia|]; split; [lia|reflexivity] | lia]
| unfold C1_regs_at, I_regs_at; repeat match goal with |- _ /\ _ => split end;
  first
  [ rewrite Q23, (denot_shx _ 10 32 16 st SB F10 F32) by (try unfold SB; lia); reflexivity
  | rewrite Q24, (denot_shx _ 10 32 8 st SB F10 F32) by (try unfold SB; lia); reflexivity
  | rewrite Q14, (denot_srl3 _ 11 16 dst F11) by lia; reflexivity
  | rewrite Q15; cbn [sv_denot]; unfold w64; f_equal; lia
  | first [rewrite Q2 | rewrite Q3 | rewrite Q4 | rewrite Q8 | rewrite Q9 | rewrite Q10 | rewrite Q13 | rewrite Q18 | rewrite Q19 | rewrite Q20 | rewrite Q22 | rewrite Q27];
    cbn [sv_denot]; rewrite ?F2, ?F3, ?F4, ?F10, ?F11, ?F12, ?F32, ?F34, ?F35, ?F27; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
    first [reflexivity | rewrite unsigned_lit_small by lia; unfold w64; f_equal; lia]
  | unfold w64; symmetry; apply Z_to_bv_bv_unsigned ]
| exact HFR
| unfold rfc_memI; exact (conj Vp (conj Vn (conj Vc (conj Vl (conj Vz (conj Vfa (conj Vfg (conj Vde (conj Vnl Vti)))))))))
| exact RAdstF
| exact KEPT
| io_now ] end end.
}
Qed.
End RA.
End d.
