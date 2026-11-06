(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/put_dec.v, with its module paths and module names changed; 726 of its 801 lines of code are new or changed and 3265 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalar.v, with its numbers changed; 325 of its 488 lines of code are new or changed and 638 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1g YC1h YC4b YC85 YC88 DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JsonScalarBase.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Definition rs_hold (A : Prop) : Prop := A.
Lemma rs_hide : forall A : Prop, A -> rs_hold A. Proof. intros A H. exact H. Qed.
Ltac rs_hide_all := repeat match goal with
  | H : _ \/ _ |- _ => apply rs_hide in H
  | H : _ mod _ = _ |- _ => apply rs_hide in H end.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
Section h.
Context {B : asyms}.
Section J.
Context {fq : YK11.FPState} {STK sp0 : Z} {FP : list (Z * Z)} {ly : alayout} {S : astate} {W0 : world SEGS}
  {mem0 : word -> option byte} {md0 : Model} {own : list (Z * Z)} {lyc : alayout} {Sc : astate} {W : world SEGS}
  {memc : word -> option byte} {k : Z} {regs0 : bvmap 5 word} {b i n v : Z} {BS : list byte} {mdc : Model}.
Context `{JHI : @JH rc SK PI B fq STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs0 b i n v BS mdc}.
Let LAWS : AR_laws SEGS B := jh_LAWS.
Let HJ0 : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k := jh_HJ0.
Let Hvimg : off_img v 20 := jh_Hvimg.
Let Hsp16 : spZ regs0 mod 16 = 0 := jh_Hsp16.
Let HspSTK : sp0 - STK <= spZ regs0 - TJSON_SCALAR_STK := jh_HspSTK.
Let Hsp0 : spZ regs0 <= sp0 := jh_Hsp0.
Let Hv0 : 0 < v := jh_Hv0.
Let Hv8 : v mod 8 = 0 := jh_Hv8.
Let Hv63 : v + 20 <= 2 ^ 63 := jh_Hv63.
Let Hvw : spZ regs0 <= v \/ v + 20 <= spZ regs0 - TJSON_SCALAR_STK := jh_Hvw.
Let Hra : YK0s.ret_ok (getr regs0 1) := jh_Hra.
Let RUN := paj_run (fx := fq) B LAWS.
Let RUNTO := paj_run_to (fx := fq) B LAWS.
Let BR := paj_branch (fx := fq) (PI := PI).
Let HLn : Z.of_nat (length BS) = n := jh_HLn.
Let HBS : garr8 SEGS (mrestrict (w_H W) memc) b BZ := jh_HBS.
Let Hb0 : 0 < b := jh_Hb0.
Let Hbam : amem_range b n := jh_Hbam.
Let Hbw : b + n <= spZ regs0 - TJSON_SCALAR_STK \/ spZ regs0 <= b := jh_Hbw.
Let Hvam : amem_range v 20 := jh_Hvam.
Let Hvra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF v 20 := jh_Hvra.
Let Hvaw : forall a, v <= a < v + 20 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
  apresent (w_H W) memc a := jh_Hvaw.
Let Hbv : b + n <= v \/ v + 20 <= b := jh_Hbv.
Let Hbra : range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF b n := jh_Hbra.
Lemma Lbr_e : forall E (nn : nat) c, bv_unsigned (ew E nn) = c -> 0 <= c < 256 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_OR (SOff nn 0) (SLit 32))) (sv_denot E (SLit 101)) = negb ((c =? 101) || (c =? 69)).
Proof.
intros E nn c Hc Hr. rewrite branch_ne_U, U_SAlu, U_SOff, !U_SLit, Hc. cbn [zalu_raw].
pose proof (jbrute (fun c => Bool.eqb (negb (zcanon (Z.lor (zcanon (c + 0)) (zcanon 32)) =? zcanon 101)) (negb ((c =? 101) || (c =? 69))))
  ltac:(vm_compute; reflexivity) c Hr) as X.
apply Bool.eqb_prop in X. exact X.
Qed.
Lemma Lbr_nd : forall E (nn : nat) c z, bv_unsigned (ew E nn) = c -> 0 <= c < 256 -> zcanon z = 18446744073709551606 ->
  branch_taken BC_LTU (sv_denot E (SOff nn (-58))) (sv_denot E (SLit z)) = negb (jdigit c).
Proof.
intros E nn c z Hc Hr Hz. rewrite branch_ltu_U, U_SOff, U_SLit, Hc, Hz.
pose proof (jbrute (fun c => Bool.eqb (zcanon (c + -58) <? 18446744073709551606) (negb (jdigit c))) ltac:(vm_compute; reflexivity) c Hr) as X.
apply Bool.eqb_prop in X. exact X.
Qed.
Lemma Lbr_ne_off : forall E (na nb : nat) xa xb c, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  0 <= xb + c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff na 0)) (sv_denot E (SOff nb c)) = negb (xa =? xb + c).
Proof.
intros E na nb xa xb c Ha Hb Hr. rewrite branch_ne_U, !U_SOff, Ha, Hb, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E na)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma jdigits_end : forall L j f, jlen L <= j -> jdigits L j f = j.
Proof. intros L j [|f] H; [reflexivity|]. cbn [jdigits]. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.
Lemma jdigits_stop : forall L j f, jdigit (jbyte L j) = false -> jdigits L j (Datatypes.S f) = j.
Proof. intros L j f H. cbn [jdigits]. rewrite H, andb_false_r. reflexivity. Qed.
Lemma jdigits_step : forall L j f, j < jlen L -> jdigit (jbyte L j) = true -> jdigits L j (Datatypes.S f) = jdigits L (j + 1) f.
Proof. intros L j f H1 H2. cbn [jdigits]. rewrite (proj2 (Z.ltb_lt _ _) H1), H2. reflexivity. Qed.
Ltac jdec :=
  rewrite ?jlen_BZ;
  repeat first
  [ progress cbn [negb andb orb]
  | match goal with H : jdigit ?x = _ |- context [jdigit ?x] => rewrite H end
  | match goal with H : (?x =? 101) || (?x =? 69) = _ |- context [(?x =? 101) || (?x =? 69)] => rewrite H end
  | match goal with |- context [Z.ltb ?x ?y] =>
      first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ] end
  | match goal with |- context [Z.eqb ?x ?y] =>
      first [ rewrite (proj2 (Z.eqb_eq x y)) by lia | rewrite (proj2 (Z.eqb_neq x y)) by lia ] end ].
Ltac jcv Hc :=
  let jU := idtac; lazymatch goal with AGx : forall kk, (kk < 512)%nat -> ew _ kk = ew _ kk |- _ => first [eassumption | rewrite AGx by lia; eassumption] end in
  let jR := idtac; first [lia | lazymatch goal with Hz : forall t, _ -> 0 <= jbyte _ t < 256 |- _ => apply Hz; lia end] in
  lazymatch type of Hc with
  | branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_OR (SOff ?nn 0) (SLit 32))) (sv_denot _ (SLit 101)) = _ =>
    rewrite (Lbr_e Ex nn _ ltac:(jU) ltac:(jR)) in Hc;
    try (rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc);
    let BF := fresh "BF" in rename Hc into BF
  | branch_taken BC_LTU (sv_denot ?Ex (SOff ?nn (-58))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_nd Ex nn _ z ltac:(jU) ltac:(jR) ltac:(vm_compute; reflexivity)) in Hc;
    try (rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc);
    let BF := fresh "BF" in rename Hc into BF
  | branch_taken BC_NE (sv_denot ?Ex (SOff ?na 0)) (sv_denot _ (SOff ?nb ?c)) = _ =>
    rewrite (Lbr_ne_off Ex na nb _ _ c ltac:(jU) ltac:(jU) ltac:(lia)) in Hc;
    try (rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc);
    try (rewrite ?Z.eqb_eq, ?Z.eqb_neq in Hc);
    let BF := fresh "BF" in rename Hc into BF
  | ?T => first [jconv Hc | idtac "JCFAIL" T; fail]
  end.
Lemma js_C_store : js_C_store_stmt.
Proof.
intros Q HQ R M md j3 (HI & H18 & H15 & H16) H10 Hij Hjn Hjs.
rs_hide_all.
pose proof Hb0 as Hb0'. pose proof Hv0 as Hv0'. pose proof Hvam as Hvam'.
pose proof (jvstate R M md JS_CST j3 16 16%bv [] HI ltac:(lia) ltac:(lia) eq_refl H16 I) as HS.
pose proof (jvshok R M md j3 16 16%bv HI ltac:(lia) ltac:(lia) eq_refl H16) as SHOK.
pose proof HI as (HJ & HSL & HK & HPR & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam'; lia).
assert (UV : bv_unsigned (ew (JE R j3 0) 16) = v) by (apply (jU_reg R j3 0 16 16%bv); [lia | reflexivity | exact H16 | lia]).
assert (Usp : bv_unsigned (ew (JE R j3 0) 2) = spZ regs0 - 128) by (apply (jU_reg R j3 0 2 2%bv); [lia | reflexivity | exact H2 | lia]).
assert (U18 : bv_unsigned (ew (JE R j3 0) 18) = b + i) by (apply (jU_reg R j3 0 18 18%bv); [lia | reflexivity | exact H18 | lia]).
assert (U10 : bv_unsigned (ew (JE R j3 0) 10) = j3) by (apply (jU_reg R j3 0 10 10%bv); [lia | reflexivity | exact H10 | lia]).
assert (U15 : bv_unsigned (ew (JE R j3 0) 15) = i) by (apply (jU_reg R j3 0 15 15%bv); [lia | reflexivity | exact H15 | lia]).
assert (E3 : ew (JE R j3 0) 3 = getr R 3) by (apply jE_low; [lia | reflexivity]).
assert (E4 : ew (JE R j3 0) 4 = getr R 4) by (apply jE_low; [lia | reflexivity]).
assert (E10 : ew (JE R j3 0) 10 = getr R 10) by (apply jE_low; [lia | reflexivity]).
set (E := JE R j3 0) in *.
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
paj_run_to_tok RUNTO HS HJ SHOK JBspan JS_EPI.
- cbn [ss_mem].
  apply (awr_ok_cons_gen E (vreg 16) _ STK sp0 FP _ _ lyc own 16%nat v); [reflexivity | exact UV | intros a Ha; apply Hvaw; cbn in Ha; lia |].
  apply (awr_ok_cons_stack_off E jframe _ STK sp0 FP _ _ lyc own 2%nat (spZ regs0 - 128 - sp0)); [reflexivity | rewrite Usp; lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- assert (HWR : forall a, in_wrange E [vreg 16; jframe; jbytes 0] a ->
    (spZ regs0 - TJSON_SCALAR_STK <= a < spZ regs0) \/ (v <= a < v + 20)).
  { intros a (rg & Hin & Ha). cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[]]]];
    cbn [vreg jframe jbytes YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?UV, ?Usp in Ha; lia. }
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ => set (E2 := En) in HS end.
  assert (AG : forall kk, (kk < 512)%nat -> ew E2 kk = ew E kk)
    by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; reflexivity).
  assert (UV2 : bv_unsigned (ew E2 16) = v) by (rewrite AG by lia; exact UV).
  assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs0 - 128) by (rewrite AG by lia; exact Usp).
  assert (U18' : bv_unsigned (ew E2 18) = b + i) by (rewrite AG by lia; exact U18).
  assert (U10' : bv_unsigned (ew E2 10) = j3) by (rewrite AG by lia; exact U10).
  assert (U15' : bv_unsigned (ew E2 15) = i) by (rewrite AG by lia; exact U15).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (10%bv : bv 5) Q10.
  pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
  pmkst HS.
  apply (HQ (ms_regs ms) (ms_mem ms) _ j3 HJ).
  + rewrite Q2. rewrite ?AG by lia. apply bv_eq. rewrite Usp. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  + rewrite Q3. rewrite ?AG by lia. rewrite E3. exact H3.
  + rewrite Q4. rewrite ?AG by lia. rewrite E4. exact H4.
  + rewrite Q10. rewrite ?AG by lia. rewrite E10. exact H10.
  + lia.
  + apply (jslots_of E2 _ ms 1 _ HS eq_refl).
    * intros c Hc. cbn [jframe_chunks In] in Hc |- *. tauto.
    * exact Usp2.
    * intros t Ht. rewrite AG by lia. apply jE_X. exact Ht.
  + exact (jpres_of _ _ HG HPR).
  + unfold JRES. change (map bv_unsigned BS) with BZ. rewrite Hjs. split; [reflexivity|].
    split; [|split; [|split]].
    * pose proof (field_of_region E2 _ 16 v _ 0 20 0 20 0 8 (SOff 18 0) (b + i) HR0 UV2
        ltac:(cbn [In]; tauto) ltac:(rewrite (jdenot_soff E2 18 (b + i) 0 U18'); f_equal; lia) ltac:(lia) ltac:(cbn; lia)) as Hv.
      rewrite Z.add_0_r in Hv. exact Hv.
    * exact (field_of_region E2 _ 16 v _ 0 20 0 20 8 8 _ (j3 - i) HR0 UV2
        ltac:(cbn [In]; tauto) ltac:(rewrite (jdenot_sub E2 10 15 j3 i U10' U15') by lia; f_equal; lia) ltac:(lia) ltac:(cbn; lia)).
    * exact (field_of_region E2 _ 16 v _ 0 20 0 20 16 4 (SLit 2) 2 HR0 UV2
        ltac:(cbn [In]; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
    * exact (jkeepv_of E _ M (ms_mem ms) HFr HWR HK).
Qed.
Definition jal_d3 : list (sv * sv) := [(SAlu ALU_ADD (SOff 20 0) (SOff 12 0), SOff 45 0)].
Lemma jal_d3_ok : forall R j la, getr R 20 = w64 b -> getr R 12 = w64 j -> 0 <= j < n -> alias_ok (JE R j la) jal_d3.
Proof.
intros R j la H20 H12 Hj. pose proof jb_hi as Hbhi. pose proof Hb0 as Hb0'.
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U12 : bv_unsigned (ew (JE R j la) 12) = j) by (apply (jU_reg R j la 12 12%bv); [lia | reflexivity | exact H12 | lia]).
unfold jal_d3. cbn [alias_ok].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U12 UP); f_equal; lia|].
exact I.
Qed.
Lemma js_L_d3 : js_L_d3_stmt.
Proof.
intros HCS Q HQ R M md j f. revert R M md j.
induction f as [|f IH]; intros R M md j HN H12 H11 Hij Hjn Hf HJS; [cbn in Hf; lia|].
all: rs_hide_all.
destruct HN as (HI & H18 & H15 & H16).
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof Hb0 as Hb0'.
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
pose proof (jstate R M md JS_LD3 j 1 jal_d3 HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_d3_ok R j 1 H20 H12 ltac:(lia))) as HS.
jpin HS 11 JM10 H11.
assert (U2 : bv_unsigned (ew (JE R j 1) 2) = spZ regs0 - 128) by (apply (jU_reg R j 1 2 2%bv); [lia | reflexivity | exact H2 | lia]).
assert (U9 : bv_unsigned (ew (JE R j 1) 9) = SHADOW_OFF) by (apply (jU_reg R j 1 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]).
assert (U19 : bv_unsigned (ew (JE R j 1) 19) = n) by (apply (jU_reg R j 1 19 19%bv); [lia | reflexivity | exact H19 | lia]).
assert (U20 : bv_unsigned (ew (JE R j 1) 20) = b) by (apply (jU_reg R j 1 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U12 : bv_unsigned (ew (JE R j 1) 12) = j) by (apply (jU_reg R j 1 12 12%bv); [lia | reflexivity | exact H12 | lia]).
assert (U45 : bv_unsigned (ew (JE R j 1) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (EF2 : ew (JE R j 1) 2 = getr R 2) by (apply jE_low; [lia | reflexivity]).
assert (EF3 : ew (JE R j 1) 3 = getr R 3) by (apply jE_low; [lia | reflexivity]).
assert (EF4 : ew (JE R j 1) 4 = getr R 4) by (apply jE_low; [lia | reflexivity]).
assert (EF9 : ew (JE R j 1) 9 = getr R 9) by (apply jE_low; [lia | reflexivity]).
assert (EF12 : ew (JE R j 1) 12 = getr R 12) by (apply jE_low; [lia | reflexivity]).
assert (EF15 : ew (JE R j 1) 15 = getr R 15) by (apply jE_low; [lia | reflexivity]).
assert (EF16 : ew (JE R j 1) 16 = getr R 16) by (apply jE_low; [lia | reflexivity]).
assert (EF18 : ew (JE R j 1) 18 = getr R 18) by (apply jE_low; [lia | reflexivity]).
assert (EF19 : ew (JE R j 1) 19 = getr R 19) by (apply jE_low; [lia | reflexivity]).
assert (EF20 : ew (JE R j 1) 20 = getr R 20) by (apply jE_low; [lia | reflexivity]).
pose proof (jE_C R j 1 0 ltac:(lia) ltac:(lia)) as EC0. cbn [Nat.add Z.of_nat] in EC0. rewrite ?Z.add_0_r in EC0.
assert (UC0 : bv_unsigned (ew (JE R j 1) 46) = jbyte BZ j) by (rewrite EC0; apply unsigned_lit_small; pose proof (HnZ j ltac:(lia)); lia).
set (E0 := JE R j 1) in *.
assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 9 0) [] E0 (mrestrict (w_H W) (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_LD3)) M (seg_rom SEGS))))) by apply Forall_nil.
set (Ec0 := E0) in HS, SHOK, HEI.
assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity).
clearbody Ec0.
change (JKEEP M) with (JKEEP (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_LD3)) M (seg_rom SEGS)))) in MEQ.
change (JPRES M) with (JPRES (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_LD3)) M (seg_rom SEGS)))) in PRS.
let rec go T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK JBspan T;
  [ lazymatch goal with
    | |- range_addressable _ _ (U _ (SOff 45 ?t)) 1 =>
      cbn [ms_mem mkst]; apply (jobl _ _ j t MEQ); [rewrite AG by lia; exact U9 | rewrite AG by lia; exact U45 | lia | lia | lia]
    | |- awr_ok _ _ _ _ _ _ _ _ _ => apply jawr_std; [vm_compute; reflexivity | rewrite AG by lia; exact U2]
    | |- ?g => idtac "OBLFAIL" g; fail
    end ..
  | jpost Ecur ]
  end
with jpost Ecur :=
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (jkeep_run Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(rewrite AG by lia; exact U2) HFr MEQ) as MEQ2;
    clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ => jrebase En Ecur end;
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 13396 => jexit_st
    | 13272 => jexit_loop
    | 13300 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv Hc; tryif (exfalso; lia) then idtac else go JS_CST | jcv Hc; tryif (exfalso; lia) then idtac else go JS_LD3]
    | 13308 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv Hc; tryif (exfalso; lia) then idtac else go JS_LD3 | jcv Hc; tryif (exfalso; lia) then idtac else go JS_CST]
    | ?p => idtac "PCFAIL" p; fail
    end
  end
with jrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  (let E2 := fresh "Ec" in set (E2 := En) in *;
   let AG2 := fresh "AG" in
   assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
     by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
   clear AG; rename AG2 into AG)
with jrg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; rewrite ?AG by lia;
    first [ reflexivity
          | rewrite ?EF2, ?EF3, ?EF4, ?EF9, ?EF12, ?EF15, ?EF16, ?EF18, ?EF19, ?EF20; assumption
          | rewrite ?U12; unfold w64; f_equal; lia
          | apply bv_eq; rewrite ?U2, ?U9, ?U12, ?U19, ?U20, ?U45; unfold w64; rewrite unsigned_lit_small by lia; lia
          | match goal with |- ?g => idtac "JREGFAIL" g; fail end ]
  end
with jnpre HS Ec msx :=
  split;
  [ split; [exact HJ|]; split;
    [ apply (jslots_of Ec _ msx 0 _ HS eq_refl);
      [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; tauto
      | rewrite AG by lia; exact U2
      | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by lia; apply jE_X; exact Ht ]
    | split; [exact MEQ|]; split; [exact PRS|]; repeat split; jrg HS ]
  | repeat split; jrg HS ]
with jexit_st :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict _ ?msx) |- _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ss) (10%bv : bv 5)) in
  lazymatch e10 with
  | SOff 12%nat _ =>
    pmkst HS;
    apply (HCS Q HQ (ms_regs msx) (ms_mem msx) _ j);
    [ jnpre HS Ec msx | jrg HS | lia | lia
    | rewrite HJS, (jdigits_stop BZ j f) by assumption; reflexivity ]
  | SOff 19%nat _ =>
    pmkst HS;
    apply (HCS Q HQ (ms_regs msx) (ms_mem msx) _ n);
    [ jnpre HS Ec msx | jrg HS | lia | lia
    | rewrite HJS, (jdigits_step BZ j f) by first [rewrite jlen_BZ; lia | assumption];
      rewrite (jdigits_end BZ (j + 1) f) by (rewrite jlen_BZ; lia);
      let Hn1 := fresh in assert (Hn1 : n = j + 1) by lia; rewrite Hn1; reflexivity ]
  | ?x => idtac "E10FAIL" x; fail
  end
  end
with jexit_loop :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (IH (ms_regs msx) (ms_mem msx) _ (j + 1));
  [ jnpre HS Ec msx | jrg HS | jrg HS | lia | lia | lia
  | rewrite HJS, (jdigits_step BZ j f) by first [rewrite jlen_BZ; lia | assumption]; reflexivity ]
  end in
go JS_CST.
Qed.
Definition jal_ce : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 20 0) (SOff 10 0), SOff 45 0); (SAlu ALU_ADD (SOff 20 0) (SOff 10 1), SOff 45 1);
   (SAlu ALU_ADD (SOff 20 0) (SOff 10 2), SOff 45 2)].
Lemma jal_ce_ok : forall R j la, getr R 20 = w64 b -> getr R 10 = w64 j -> 0 <= j <= n -> alias_ok (JE R j la) jal_ce.
Proof.
intros R j la H20 H10 Hj. pose proof jb_hi as Hbhi. pose proof Hb0 as Hb0'.
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U10 : bv_unsigned (ew (JE R j la) 10) = j) by (apply (jU_reg R j la 10 10%bv); [lia | reflexivity | exact H10 | lia]).
unfold jal_ce. cbn [alias_ok].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U10 UP); f_equal; lia|].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U10 UP); f_equal; lia|].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U10 UP); f_equal; lia|].
exact I.
Qed.
Lemma js_C_exp : js_C_exp_stmt.
Proof.
intros HLD3 HCS Q HQ R M md j2 HN H10 Hij Hjn HJS.
rs_hide_all.
destruct HN as (HI & H18 & H15 & H16).
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof Hb0 as Hb0'.
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
assert (HLB : Z.of_nat (length BZ) = n) by (pose proof jlen_BZ as X; unfold jlen in X; exact X).
assert (Hla : n - j2 = 0 \/ n - j2 = 1 \/ n - j2 = 2 \/ 3 <= n - j2) by lia.
let rec go T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur ?ss0 _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK JBspan T;
  [ lazymatch goal with
    | |- range_addressable _ _ (U _ (SOff 45 ?t)) 1 =>
      cbn [ms_mem mkst]; apply (jobl _ _ j2 t MEQ); [rewrite AG by lia; exact U9 | rewrite AG by lia; exact U45 | lia | lia | lia]
    | |- awr_ok _ _ _ _ _ _ _ _ _ => apply jawr_std; [vm_compute; reflexivity | rewrite AG by lia; exact U2]
    | |- ?g => idtac "OBLFAIL" g; fail
    end ..
  | jpost Ecur ]
  end
with jpost Ecur :=
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (jkeep_run Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(rewrite AG by lia; exact U2) HFr MEQ) as MEQ2;
    clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ => jrebase En Ecur end;
  lazymatch goal with
  | HS : st_ok_pi _ _ _ ?ss _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 12740 => jexit_epi
    | 13396 => jexit_st
    | 13272 => jexit_ld3
    | 13140 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv Hc; tryif (exfalso; lia) then idtac else go JS_CST | jcv Hc; tryif (exfalso; lia) then idtac else go JS_EPI]
    | 13176 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv Hc; tryif (exfalso; lia) then idtac else go JS_CST | jcv Hc; tryif (exfalso; lia) then idtac else go JS_EPI]
    | 13268 => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv Hc; tryif (exfalso; lia) then idtac else go JS_EPI | jcv Hc; tryif (exfalso; lia) then idtac else go JS_LD3]
    | _ => psrr_branch_tok RUN BR HS SHOK JBspan;
               [jcv Hc; tryif (exfalso; lia) then idtac else go JS_EPI | jcv Hc; tryif (exfalso; lia) then idtac else go JS_EPI]
    end
  end
with jrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  (let E2 := fresh "Ec" in set (E2 := En) in *;
   let AG2 := fresh "AG" in
   assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
     by (intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
   clear AG; rename AG2 into AG)
with jrg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; rewrite ?AG by lia;
    first [ reflexivity
          | rewrite ?EF2, ?EF3, ?EF4, ?EF9, ?EF10, ?EF15, ?EF16, ?EF18, ?EF19, ?EF20; assumption
          | rewrite ?U10; unfold w64; f_equal; lia
          | apply bv_eq; rewrite ?U2, ?U9, ?U10, ?U19, ?U20, ?U45; unfold w64; rewrite unsigned_lit_small by lia; lia
          | match goal with |- ?g => idtac "JREGFAIL" g; fail end ]
  end
with jnpre HS Ec msx :=
  split;
  [ split; [exact HJ|]; split;
    [ apply (jslots_of Ec _ msx 0 _ HS eq_refl);
      [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; tauto
      | rewrite AG by lia; exact U2
      | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by lia; apply jE_X; exact Ht ]
    | split; [exact MEQ|]; split; [exact PRS|]; repeat split; jrg HS ]
  | repeat split; jrg HS ]
with jtd := idtac; unfold jtail, jexp; cbv zeta; unfold jdig_at; jdec
with jexit_epi :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (HQ (ms_regs msx) (ms_mem msx) _ 0 HJ);
  [ jrg HS | jrg HS | jrg HS | jrg HS | lia
  | apply (jslots_of Ec _ msx 0 _ HS eq_refl);
    [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; tauto
    | rewrite AG by lia; exact U2
    | let t := fresh in let Ht := fresh in intros t Ht; rewrite AG by lia; apply jE_X; exact Ht ]
  | exact PRS
  | unfold JRES; change (map bv_unsigned BS) with BZ; rewrite HJS; jtd; split; [reflexivity | exact MEQ] ]
  end
with jexit_st :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict _ ?msx) |- _ =>
  pmkst HS;
  apply (HCS Q HQ (ms_regs msx) (ms_mem msx) _ j2);
  [ jnpre HS Ec msx | jrg HS | lia | lia | rewrite HJS; jtd; reflexivity ]
  end
with jexit_ld3 :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict _ ?msx) |- _ =>
  let e12 := eval vm_compute in (sr_get (ss_regs ss) (12%bv : bv 5)) in
  let kk := lazymatch e12 with SOff 10%nat ?c => constr:(j2 + c) | ?x => idtac "E12FAIL" x; fail end in
  pmkst HS;
  apply (HLD3 Q HQ (ms_regs msx) (ms_mem msx) _ kk (length BZ));
  [ jnpre HS Ec msx | jrg HS | jrg HS | lia | lia | lia | rewrite HJS; jtd; reflexivity ]
  end in
let cbody la :=
  pose proof (jstate R M md JS_CEXP j2 la jal_ce HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_ce_ok R j2 la H20 H10 ltac:(lia))) as HS;
  assert (U2 : bv_unsigned (ew (JE R j2 la) 2) = spZ regs0 - 128) by (apply (jU_reg R j2 la 2 2%bv); [lia | reflexivity | exact H2 | lia]);
  assert (U9 : bv_unsigned (ew (JE R j2 la) 9) = SHADOW_OFF) by (apply (jU_reg R j2 la 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]);
  assert (U19 : bv_unsigned (ew (JE R j2 la) 19) = n) by (apply (jU_reg R j2 la 19 19%bv); [lia | reflexivity | exact H19 | lia]);
  assert (U20 : bv_unsigned (ew (JE R j2 la) 20) = b) by (apply (jU_reg R j2 la 20 20%bv); [lia | reflexivity | exact H20 | lia]);
  assert (U10 : bv_unsigned (ew (JE R j2 la) 10) = j2) by (apply (jU_reg R j2 la 10 10%bv); [lia | reflexivity | exact H10 | lia]);
  assert (U45 : bv_unsigned (ew (JE R j2 la) 45) = b + j2) by (rewrite jE_P; apply unsigned_lit_small; lia);
  assert (EF2 : ew (JE R j2 la) 2 = getr R 2) by (apply jE_low; [lia | reflexivity]);
  assert (EF3 : ew (JE R j2 la) 3 = getr R 3) by (apply jE_low; [lia | reflexivity]);
  assert (EF4 : ew (JE R j2 la) 4 = getr R 4) by (apply jE_low; [lia | reflexivity]);
  assert (EF9 : ew (JE R j2 la) 9 = getr R 9) by (apply jE_low; [lia | reflexivity]);
  assert (EF10 : ew (JE R j2 la) 10 = getr R 10) by (apply jE_low; [lia | reflexivity]);
  assert (EF15 : ew (JE R j2 la) 15 = getr R 15) by (apply jE_low; [lia | reflexivity]);
  assert (EF16 : ew (JE R j2 la) 16 = getr R 16) by (apply jE_low; [lia | reflexivity]);
  assert (EF18 : ew (JE R j2 la) 18 = getr R 18) by (apply jE_low; [lia | reflexivity]);
  assert (EF19 : ew (JE R j2 la) 19 = getr R 19) by (apply jE_low; [lia | reflexivity]);
  assert (EF20 : ew (JE R j2 la) 20 = getr R 20) by (apply jE_low; [lia | reflexivity]);
  try (pose proof (jE_C R j2 la 0 ltac:(lia) ltac:(lia)) as EC0; cbn [Nat.add Z.of_nat] in EC0; rewrite ?Z.add_0_r in EC0;
       assert (UC0 : bv_unsigned (ew (JE R j2 la) 46) = jbyte BZ j2) by (rewrite EC0; apply unsigned_lit_small; pose proof (HnZ j2 ltac:(lia)); lia));
  try (pose proof (jE_C R j2 la 1 ltac:(lia) ltac:(lia)) as EC1; cbn [Nat.add Z.of_nat] in EC1;
       assert (UC1 : bv_unsigned (ew (JE R j2 la) 47) = jbyte BZ (j2 + 1)) by (rewrite EC1; apply unsigned_lit_small; pose proof (HnZ (j2 + 1) ltac:(lia)); lia));
  try (pose proof (jE_C R j2 la 2 ltac:(lia) ltac:(lia)) as EC2; cbn [Nat.add Z.of_nat] in EC2;
       assert (UC2 : bv_unsigned (ew (JE R j2 la) 48) = jbyte BZ (j2 + 2)) by (rewrite EC2; apply unsigned_lit_small; pose proof (HnZ (j2 + 2) ltac:(lia)); lia));
  set (E0 := JE R j2 la) in *;
  assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env;
  assert (SHOK : sh_ok SEGS (SOff 9 0) [] E0 (mrestrict (w_H W) (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_CEXP)) M (seg_rom SEGS))))) by apply Forall_nil;
  set (Ec0 := E0) in HS, SHOK, HEI;
  assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity);
  clearbody Ec0;
  change (JKEEP M) with (JKEEP (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_CEXP)) M (seg_rom SEGS)))) in MEQ;
  change (JPRES M) with (JPRES (ms_mem (mkst R (Z_to_bv 64 (BASE + JS_CEXP)) M (seg_rom SEGS)))) in PRS;
  go JS_EPI in
destruct Hla as [Hla|[Hla|[Hla|Hla]]]; [cbody 0%nat | cbody 1%nat | cbody 2%nat | cbody 3%nat].
Qed.
End J.
End h.
End f.
End d.
