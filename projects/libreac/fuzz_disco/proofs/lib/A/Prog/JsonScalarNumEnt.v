(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v, with its module paths and module names changed; 593 of its 625 lines of code are new or changed and 459 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalarStr.v; 231 of its 332 lines of code are new or changed and 524 lines of the source are left out. *)
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
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import JsonScalarBase.
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

Lemma ne_dS : forall L j f, jdigits L j (Datatypes.S f) = if (j <? jlen L) && jdigit (jbyte L j) then jdigits L (j + 1) f else j.
Proof. reflexivity. Qed.
Lemma ne_fuel : forall L j f, jlen L - j <= Z.of_nat f -> jdigits L j f = jdigits L j (Datatypes.S f).
Proof.
intros L j f. revert j. induction f as [|f IH]; intros j H.
- rewrite ne_dS. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
- rewrite (ne_dS L j (Datatypes.S f)), (ne_dS L j f).
  destruct ((j <? jlen L) && jdigit (jbyte L j)); [apply IH; lia | reflexivity].
Qed.
Lemma ne_sh_addr : forall x y : word, bv_unsigned x = b + i -> bv_unsigned y = SHADOW_OFF -> 0 <= i < n ->
  alu64 ALU_ADD (alu64 ALU_SRL x (Z_to_bv 64 3)) y = w64 (SHADOW_OFF + (b + i) / 8).
Proof.
intros x y Hx Hy Hin. pose proof jb_hi as Hbhi. pose proof Hb0 as Hb0'. apply bv_eq.
rewrite !alu64_unsigned. cbn [zalu_raw]. rewrite Hx, Hy. rewrite (unsigned_lit_small 3) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= (b + i) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (bv_wrap_small 64 ((b + i) / 8)) by (unfold bv_modulus; cbn [Z.of_N]; lia).
unfold w64. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
rewrite Z.add_comm. apply bv_wrap_small. unfold bv_modulus, SHADOW_OFF. cbn [Z.of_N]. lia.
Qed.
Lemma Lbr_dge : forall E (nn : nat) c z, bv_unsigned (ew E nn) = c -> 0 <= c < 256 -> zcanon z = JM10 ->
  branch_taken BC_GEU (sv_denot E (SOff nn (-58))) (sv_denot E (SLit z)) = jdigit c.
Proof.
intros E nn c z Hc Hr Hz. rewrite branch_geu_U, U_SOff, U_SLit, Hc, Hz.
pose proof (jbrute (fun c => Bool.eqb (negb (zcanon (c + -58) <? JM10)) (jdigit c)) ltac:(vm_compute; reflexivity) c Hr) as X.
cbv beta in X. apply Bool.eqb_prop in X. exact X.
Qed.
Definition ne_al0 : list (sv * sv) := [(SAlu ALU_ADD (SOff 20 0) (SOff 10 0), SOff 45 0)].
Lemma ne_al0_ok : forall R j la, getr R 20 = w64 b -> getr R 10 = w64 j -> 0 <= j <= n -> alias_ok (JE R j la) ne_al0.
Proof.
intros R j la H20 H10 Hj. pose proof jb_hi as Hbhi. pose proof Hb0 as Hb0'.
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U10 : bv_unsigned (ew (JE R j la) 10) = j) by (apply (jU_reg R j la 10 10%bv); [lia | reflexivity | exact H10 | lia]).
unfold ne_al0. cbn [alias_ok].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U10 UP); f_equal; lia|].
exact I.
Qed.
Ltac nAG := lazymatch goal with AG : forall kk, (kk < 512)%nat -> ew _ kk = ew _ kk |- _ => rewrite ?AG by lia end.
Ltac nobl j :=
  lazymatch goal with
  | MEQ : JKEEP _ |- range_addressable _ _ (U _ (SOff 45 ?t)) 1 =>
    cbn [ms_mem mkst]; apply (jobl _ _ j t MEQ); [nAG; assumption | nAG; assumption | lia | lia | lia]
  | |- awr_ok _ _ _ _ _ _ _ _ _ => apply jawr_std; [vm_compute; reflexivity | nAG; assumption]
  end.
Ltac nrebase En Ecur :=
  tryif constr_eq En Ecur then idtac else
  lazymatch goal with AG : forall kk, (kk < 512)%nat -> ew _ kk = ew ?E0 kk |- _ =>
  let E2 := fresh "Ec" in set (E2 := En) in *;
  let AG2 := fresh "AG" in
  assert (AG2 : forall kk, (kk < 512)%nat -> ew E2 kk = ew E0 kk)
    by (let kk := fresh in let Hkk := fresh in intros kk Hkk; subst E2; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; apply AG; exact Hkk);
  clear AG; rename AG2 into AG end.
Ltac npost Ecur :=
  lazymatch goal with HFr : frame_of ?Eh ?rs (mrestrict _ ?m1) (mrestrict _ ?m2), MEQ : JKEEP ?m1 |- _ =>
    let MEQ2 := fresh "MEQ" in
    pose proof (jkeep_run Eh rs m1 m2 ltac:(vm_compute; reflexivity) ltac:(nAG; assumption) HFr MEQ) as MEQ2;
    clear MEQ; rename MEQ2 into MEQ
  end;
  lazymatch goal with HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2), PRS : JPRES ?m1 |- _ =>
    let PRS2 := fresh "PRS" in pose proof (jpres_of m1 m2 HG PRS) as PRS2; clear PRS; rename PRS2 into PRS
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ => nrebase En Ecur end.
Ltac nrun j T :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ecur _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK JBspan T; [ nobl j .. | npost Ecur ] end.
Ltac nconv Hc :=
  let jU := idtac; lazymatch goal with AGx : forall kk, (kk < 512)%nat -> ew _ kk = ew _ kk |- _ => first [eassumption | rewrite AGx by lia; eassumption] end in
  let jR := idtac; first [lia | lazymatch goal with Hz : forall t, _ -> 0 <= jbyte _ t < 256 |- _ => apply Hz; lia end] in
  lazymatch type of Hc with
  | branch_taken BC_GEU (sv_denot ?Ex (SOff ?nn (-58))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_dge Ex nn _ z ltac:(jU) ltac:(jR) ltac:(vm_compute; reflexivity)) in Hc
  | branch_taken BC_NE (sv_denot ?Ex (SOff ?nn 0)) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_ne_lit Ex nn _ z ltac:(jU) ltac:(lia)) in Hc
  | branch_taken BC_GEU (sv_denot ?Ex (SOff ?na ?c)) (sv_denot _ (SOff ?nb 0)) = _ =>
    rewrite (Lbr_geu_off Ex na nb _ _ c ltac:(jU) ltac:(jU) ltac:(lia)) in Hc
  end;
  try (rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc);
  try (rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?Z.ltb_lt, ?Z.ltb_ge in Hc).
Ltac nU := repeat match goal with U : bv_unsigned (ew ?E ?q) = _ |- context [bv_unsigned (ew ?E ?q)] => rewrite U end.
Ltac nrg HS :=
  lazymatch goal with |- getr _ ?r = _ =>
    let Q := fresh "Q" in prreg HS r Q; rewrite Q; clear Q; nAG;
    first [ reflexivity
          | (repeat match goal with EF : ew ?E ?q = getr _ _ |- context [ew ?E ?q] => rewrite EF end); assumption
          | nU; unfold w64; f_equal; lia
          | apply bv_eq; nU; unfold w64; rewrite unsigned_lit_small by lia; lia
          | unfold w64; apply bv_eq; rewrite !unsigned_lit; vm_compute; reflexivity ]
  end.
Ltac nslots HS :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec _ (restrict _ ?msx) |- _ =>
  apply (jslots_of Ec _ msx 0 _ HS eq_refl);
  [ let c := fresh in let Hc0 := fresh in intros c Hc0; cbn [jframe_chunks In] in Hc0 |- *; tauto
  | nAG; assumption
  | let t := fresh in let Ht := fresh in intros t Ht; nAG; apply jE_X; exact Ht ] end.
Ltac njnpre HS :=
  split; [split; [eassumption|]; split; [nslots HS | split; [assumption|]; split; [assumption|]; repeat split; nrg HS] | repeat split; nrg HS].
Ltac nsetup R M j la pc HnZ :=
  lazymatch goal with H2 : getr R 2 = _, H9 : getr R 9 = _, H19 : getr R 19 = _, H20 : getr R 20 = _,
    HS : st_ok_pi _ _ _ _ _, MEQ : JKEEP M, PRS : JPRES M |- _ =>
  assert (U2 : bv_unsigned (ew (JE R j la) 2) = spZ regs0 - 128) by (apply (jU_reg R j la 2 2%bv); [lia | reflexivity | exact H2 | lia]);
  assert (U9 : bv_unsigned (ew (JE R j la) 9) = SHADOW_OFF) by (apply (jU_reg R j la 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]);
  assert (U19 : bv_unsigned (ew (JE R j la) 19) = n) by (apply (jU_reg R j la 19 19%bv); [lia | reflexivity | exact H19 | lia]);
  assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]);
  try (lazymatch goal with H10 : getr R 10 = w64 _ |- _ =>
    assert (U10 : bv_unsigned (ew (JE R j la) 10) = j) by (apply (jU_reg R j la 10 10%bv); [lia | reflexivity | exact H10 | lia]) end);
  assert (U45 : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia);
  assert (EF2 : ew (JE R j la) 2 = getr R 2) by (apply jE_low; [lia | reflexivity]);
  assert (EF3 : ew (JE R j la) 3 = getr R 3) by (apply jE_low; [lia | reflexivity]);
  assert (EF4 : ew (JE R j la) 4 = getr R 4) by (apply jE_low; [lia | reflexivity]);
  assert (EF9 : ew (JE R j la) 9 = getr R 9) by (apply jE_low; [lia | reflexivity]);
  assert (EF15 : ew (JE R j la) 15 = getr R 15) by (apply jE_low; [lia | reflexivity]);
  assert (EF16 : ew (JE R j la) 16 = getr R 16) by (apply jE_low; [lia | reflexivity]);
  assert (EF18 : ew (JE R j la) 18 = getr R 18) by (apply jE_low; [lia | reflexivity]);
  assert (EF19 : ew (JE R j la) 19 = getr R 19) by (apply jE_low; [lia | reflexivity]);
  assert (EF20 : ew (JE R j la) 20 = getr R 20) by (apply jE_low; [lia | reflexivity]);
  try (pose proof (jE_C R j la 0 ltac:(lia) ltac:(lia)) as EC0; cbn [Nat.add Z.of_nat] in EC0; rewrite ?Z.add_0_r in EC0;
       assert (UC0 : bv_unsigned (ew (JE R j la) 46) = jbyte BZ j) by (rewrite EC0; apply unsigned_lit_small; pose proof (HnZ j ltac:(lia)); lia));
  set (E0 := JE R j la) in *;
  assert (HEI : img_env VAL A_LIM E0) by apply Eimg_env;
  assert (SHOK : sh_ok SEGS (SOff 9 0) [] E0 (mrestrict (w_H W) (ms_mem (mkst R (Z_to_bv 64 (BASE + pc)) M (seg_rom SEGS))))) by apply Forall_nil;
  set (Ec0 := E0) in HS, SHOK, HEI;
  assert (AG : forall kk, (kk < 512)%nat -> ew Ec0 kk = ew E0 kk) by (intros; reflexivity);
  clearbody Ec0;
  change (JKEEP M) with (JKEEP (ms_mem (mkst R (Z_to_bv 64 (BASE + pc)) M (seg_rom SEGS)))) in MEQ;
  change (JPRES M) with (JPRES (ms_mem (mkst R (Z_to_bv 64 (BASE + pc)) M (seg_rom SEGS)))) in PRS
  end.
Ltac ndec := rewrite ?jlen_BZ;
  repeat first
  [ rewrite (proj2 (Z.ltb_lt _ _)) by lia
  | rewrite (proj2 (Z.ltb_ge _ _)) by lia
  | rewrite (proj2 (Z.eqb_eq _ _)) by lia
  | rewrite (proj2 (Z.eqb_neq _ _)) by lia
  | match goal with H : jdigit ?x = _ |- context [jdigit ?x] => rewrite H end
  | progress cbn [negb andb orb] ].
Ltac nex_epi HQ HJS HNone :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ =>
  pmkst HS; eapply (HQ _ _ _ 0);
  [ eassumption | nrg HS | nrg HS | nrg HS | nrg HS | lia | nslots HS | assumption
  | unfold JRES; change (map bv_unsigned BS) with BZ; rewrite HJS, HNone; split; [reflexivity | assumption] ] end.
Ltac nnum Hj0 := unfold jnum; cbv zeta; rewrite <- Hj0; unfold jdig_at; ndec.
Definition JS_NE1 : Z := 0x3198.
Lemma ne_tail : js_L_d1_spec -> js_C_frac_spec -> forall Q, JEPI_K Q -> forall R M md j0,
  JNPRE R M md -> getr R 10 = w64 j0 -> 0 <= i < n -> j0 = (if jbyte BZ i =? 45 then i + 1 else i) ->
  jscalar BZ i = jnum BZ i ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_NE1)) M (seg_rom SEGS)) md) Q.
Proof.
intros HD1 HCF Q HQ R M md j0 HN H10 Hin Hj0 HJS.
pose proof HN as (HI & H18 & H15 & H16).
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
assert (HLB : length BZ = length BS) by (unfold BZ; apply length_map).
assert (Hij : i <= j0 <= i + 1) by (destruct (jbyte BZ i =? 45); lia).
destruct (Z_lt_le_dec j0 n) as [Hjn|Hjn].
2:{
  pose proof (jstate R M md JS_NE1 j0 0 ne_al0 HI ltac:(lia) ltac:(lia) ltac:(lia) (ne_al0_ok R j0 0 H20 H10 ltac:(lia))) as HS.
  nsetup R M j0 0%nat JS_NE1 HnZ.
  nrun j0 JS_EPI.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  - nconv Hc. nrun j0 JS_EPI.
    assert (HNone : jnum BZ i = None) by (nnum Hj0; reflexivity).
    nex_epi HQ HJS HNone.
  - nconv Hc. exfalso. lia. }
pose proof (jstate R M md JS_NE1 j0 1 ne_al0 HI ltac:(lia) ltac:(lia) ltac:(lia) (ne_al0_ok R j0 1 H20 H10 ltac:(lia))) as HS.
nsetup R M j0 1%nat JS_NE1 HnZ.
nrun j0 JS_EPI.
psrr_branch_tok RUN BR HS SHOK JBspan.
- nconv Hc. exfalso. lia.
- nconv Hc. rename Hc into Hlt. nrun j0 JS_EPI.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  + nconv Hc. rename Hc into Hdig. nrun j0 JS_LD1.
    psrr_branch_tok RUN BR HS SHOK JBspan.
    * nconv Hc. nrun j0 JS_LD1.
      pmkst HS. eapply (HD1 Q HQ _ _ _ j0 (Datatypes.S (length BS))).
      -- njnpre HS.
      -- nrg HS.
      -- nrg HS.
      -- lia.
      -- lia.
      -- lia.
      -- rewrite HJS. nnum Hj0.
         rewrite (ne_fuel BZ j0 (length BZ)) by (unfold jlen; lia). rewrite HLB. unfold jtail1, jtail. reflexivity.
    * nconv Hc. nrun j0 JS_CFRAC.
      pmkst HS. eapply (HCF Q HQ _ _ _ (j0 + 1)).
      -- njnpre HS.
      -- nrg HS.
      -- lia.
      -- lia.
      -- rewrite HJS. nnum Hj0. unfold jtail1, jtail. reflexivity.
  + nconv Hc. nrun j0 JS_EPI.
    assert (HNone : jnum BZ i = None) by (nnum Hj0; reflexivity).
    nex_epi HQ HJS HNone.
Qed.
Lemma ne_ifsame : forall (A : Type) (c : bool) (x : A), (if c then x else x) = x.
Proof. intros A c x. destruct c; reflexivity. Qed.
Lemma ne_r10 : forall E c, bv_unsigned (ew E 46) = c -> 0 <= c < 256 -> 0 <= i -> i + 1 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SLit i) (SAlu ALU_SLTU (SOff 46 (-45)) (SLit 1))) = w64 (if c =? 45 then i + 1 else i).
Proof.
intros E c Hc Hr Hi0 Hi1. rewrite denot_lit_U. unfold w64. f_equal.
rewrite !U_SAlu, !U_SLit, U_SOff, Hc. cbn [zalu_raw].
pose proof (jbrute (fun c => Z.eqb (zcanon (if zcanon (c + -45) <? zcanon 1 then 1 else 0)) (if c =? 45 then 1 else 0))
  ltac:(vm_compute; reflexivity) c Hr) as X.
cbv beta in X. apply Z.eqb_eq in X. rewrite X.
rewrite (zcanon_id i) by (unfold M64; lia).
destruct (c =? 45); rewrite ?Z.add_0_r; apply zcanon_id; unfold M64; lia.
Qed.
Ltac ner10 HS :=
  lazymatch goal with HS : st_ok_pi _ _ ?Ec ?ss (restrict ?H ?ms) |- getr _ ?r = _ =>
    let Q := fresh "Q" in pose proof (st_ok_pi_restrict_reg H Ec ss ms r HS) as Q;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Q;
    rewrite Q; clear Q
  end;
  rewrite ?ne_ifsame; apply ne_r10;
  [nAG; eassumption | lazymatch goal with Hz : forall t, _ -> 0 <= jbyte _ t < 256 |- _ => apply Hz; lia end | lia | lia].
Definition jframe2 : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 128 0 128 (jframe_chunks ++ [YP09.mkChunk 8 (CVal 8 (SLit v)); YP09.mkChunk 16 (CVal 8 (SLit i))]).
Lemma js_nument : js_nument_stmt.
Proof.
intros HD1 HCF Q HQ R M md HI HSL2 H18 H8 Hin HJS.
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hb0 as Hb0'. pose proof Hv0 as Hv0'. pose proof Hvam as Hvam'.
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
assert (Hvhi : v + 20 <= 0x7fffffffffff) by (unfold amem_range in Hvam'; lia).
pose proof (jstate R M md JS_NUMENT i 1 [] HI ltac:(lia) ltac:(lia) ltac:(lia) I) as HS.
assert (V2 : bv_unsigned (ew (JE R i 1) 2) = spZ regs0 - 128) by (apply (jU_reg R i 1 2 2%bv); [lia | reflexivity | exact H2 | lia]).
assert (V9 : bv_unsigned (ew (JE R i 1) 9) = SHADOW_OFF) by (apply (jU_reg R i 1 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]).
assert (V45 : bv_unsigned (ew (JE R i 1) 45) = b + i) by (rewrite jE_P; apply unsigned_lit_small; lia).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RF0.
assert (RF : region_ok SEGS (JE R i 1) (ms_mem (restrict (w_H W) (mkst R (Z_to_bv 64 (BASE + JS_NUMENT)) M (seg_rom SEGS)))) jframe2).
{ destruct RF0 as (RA & RB & RC & RD). split; [exact RA|]. split; [exact RB|]. split; [exact RC|].
  unfold jframe2. cbn [YP09.r_chunks YP09.r_base base_val]. apply Forall_app. split; [exact RD|].
  destruct HSL2 as [Hs8 Hs16]. rewrite V2.
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS (JE R i 1) _ _ 8 8 (SLit v) v);
    [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hs8].
  - apply (chunk_ok_val SEGS (JE R i 1) _ _ 16 8 (SLit i) i);
    [reflexivity | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hs16]. }
pose proof (ast_ok_pi_set_region _ _ _ 0 jframe jframe2 HS eq_refl eq_refl ltac:(vm_compute; reflexivity) RF) as HS3.
clear HS RF RF0. rename HS3 into HS.
assert (E18 : sv_denot (JE R i 1) (SOff 45 0) = getr R 18).
{ rewrite H18. cbn [sv_denot]. rewrite V45, Z.add_0_r. reflexivity. }
pose proof (ast_ok_pi_set_reg_fp _ _ _ 18%bv (SOff 45 0) HS ltac:(vm_compute; reflexivity) E18) as HS3.
clear HS. rename HS3 into HS.
assert (E8 : sv_denot (JE R i 1) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 45 0) (SLit 3)) (SOff 9 0)) = getr R 8).
{ rewrite H8. cbn [sv_denot]. rewrite V45, V9, !Z.add_0_r.
  apply ne_sh_addr; [apply unsigned_lit_small; lia | apply unsigned_lit_small; unfold SHADOW_OFF; lia | lia]. }
pose proof (ast_ok_pi_set_reg_fp _ _ _ 8%bv _ HS ltac:(vm_compute; reflexivity) E8) as HS3.
clear HS. rename HS3 into HS. jnorm HS.
clear V2 V9 V45 E18 E8.
nsetup R M i 1%nat JS_NUMENT HnZ.
nrun i JS_NE1.
pmkst HS. eapply (ne_tail HD1 HCF Q HQ _ _ _ (if jbyte BZ i =? 45 then i + 1 else i)).
- njnpre HS.
- ner10 HS.
- lia.
- reflexivity.
- exact HJS.
Qed.
End J. End h. End f. End d.
