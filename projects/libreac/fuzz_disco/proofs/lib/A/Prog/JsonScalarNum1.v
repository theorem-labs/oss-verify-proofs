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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/JsonScalar.v; 316 of its 406 lines of code are new or changed and 711 lines of the source are left out. *)
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
Lemma jdigits_end : forall L j f, jlen L <= j -> jdigits L j f = j.
Proof. intros L j [|f] H; [reflexivity|]. cbn [jdigits]. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity. Qed.
Lemma jdigits_nd : forall L j f, jdigit (jbyte L j) = false -> jdigits L j f = j.
Proof. intros L j [|f] H; [reflexivity|]. cbn [jdigits]. rewrite H, andb_false_r. reflexivity. Qed.
Lemma jdigits_d : forall L j f, j < jlen L -> jdigit (jbyte L j) = true -> jdigits L j (Datatypes.S f) = jdigits L (j + 1) f.
Proof. intros L j f H1 H2. cbn [jdigits]. rewrite (proj2 (Z.ltb_lt _ _) H1), H2. reflexivity. Qed.
Lemma jtail_end : jtail n = Some (n, 2, i, n - i).
Proof. unfold jtail, jexp. rewrite jlen_BZ, Z.ltb_irrefl. reflexivity. Qed.
Lemma jtail1_end : jtail1 n = Some (n, 2, i, n - i).
Proof. unfold jtail1, jfrac. rewrite jlen_BZ, Z.ltb_irrefl. cbn [andb]. exact jtail_end. Qed.
Lemma Lbr_nd : forall E (nn : nat) c z, bv_unsigned (ew E nn) = c -> 0 <= c < 256 -> zcanon z = JM10 ->
  branch_taken BC_LTU (sv_denot E (SOff nn (-58))) (sv_denot E (SLit z)) = negb (jdigit c).
Proof.
intros E nn c z Hc Hr Hz. rewrite branch_ltu_U, U_SOff, U_SLit, Hc, Hz.
pose proof (jbrute (fun c => Bool.eqb (zcanon (c + -58) <? JM10) (negb (jdigit c))) ltac:(vm_compute; reflexivity) c Hr) as X.
apply Bool.eqb_prop in X. exact X.
Qed.
Lemma Lbr_ltu_off : forall E (na nb : nat) xa xb c, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  0 <= xa + c < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff na c)) (sv_denot E (SOff nb 0)) = (xa + c <? xb).
Proof.
intros E na nb xa xb c Ha Hb Hr. rewrite branch_ltu_U, !U_SOff, Ha, Hb, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E nb)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Lemma Lbr_ne_off : forall E (na nb : nat) xa xb c, bv_unsigned (ew E na) = xa -> bv_unsigned (ew E nb) = xb ->
  0 <= xb + c < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff na 0)) (sv_denot E (SOff nb c)) = negb (xa =? xb + c).
Proof.
intros E na nb xa xb c Ha Hb Hr. rewrite branch_ne_U, !U_SOff, Ha, Hb, Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E na)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
rewrite !zcanon_id by (unfold M64; lia). reflexivity.
Qed.
Definition jal_n0 : list (sv * sv) := [(SAlu ALU_ADD (SOff 20 0) (SOff 10 0), SOff 45 0)].
Definition jal_n1 : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 20 0) (SOff 10 0), SOff 45 0); (SAlu ALU_ADD (SOff 20 0) (SOff 10 1), SOff 45 1)].
Lemma jal_n0_ok : forall R j la, getr R 20 = w64 b -> getr R 10 = w64 j -> 0 <= j <= n -> alias_ok (JE R j la) jal_n0.
Proof.
intros R j la H20 H10 Hj. pose proof jb_hi as Hbhi.
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U10 : bv_unsigned (ew (JE R j la) 10) = j) by (apply (jU_reg R j la 10 10%bv); [lia | reflexivity | exact H10 | lia]).
unfold jal_n0. cbn [alias_ok].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U10 UP); f_equal; lia|].
exact I.
Qed.
Lemma jal_n1_ok : forall R j la, getr R 20 = w64 b -> getr R 10 = w64 j -> 0 <= j <= n -> alias_ok (JE R j la) jal_n1.
Proof.
intros R j la H20 H10 Hj. pose proof jb_hi as Hbhi.
assert (UP : bv_unsigned (ew (JE R j la) 45) = b + j) by (rewrite jE_P; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]).
assert (U10 : bv_unsigned (ew (JE R j la) 10) = j) by (apply (jU_reg R j la 10 10%bv); [lia | reflexivity | exact H10 | lia]).
unfold jal_n1. cbn [alias_ok].
split; [apply (jalias_add _ _ _ _ _ _ _ _ _ U20 U10 UP); f_equal; lia|].
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
  | branch_taken BC_LTU (sv_denot ?Ex (SOff ?nn (-58))) (sv_denot _ (SLit ?z)) = _ =>
    rewrite (Lbr_nd Ex nn _ z ltac:(jU) ltac:(jR) ltac:(vm_compute; reflexivity)) in Hc
  | branch_taken BC_LTU (sv_denot ?Ex (SOff ?na ?c)) (sv_denot _ (SOff ?nb 0)) = _ =>
    rewrite (Lbr_ltu_off Ex na nb _ _ c ltac:(jU) ltac:(jU) ltac:(lia)) in Hc
  | branch_taken BC_NE (sv_denot ?Ex (SOff ?na 0)) (sv_denot _ (SOff ?nb ?c)) = _ =>
    rewrite (Lbr_ne_off Ex na nb _ _ c ltac:(jU) ltac:(jU) ltac:(lia)) in Hc
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
          | apply bv_eq; nU; unfold w64; rewrite unsigned_lit_small by lia; lia ]
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
  lazymatch goal with H2 : getr R 2 = _, H9 : getr R 9 = _, H19 : getr R 19 = _, H20 : getr R 20 = _, H10 : getr R 10 = _,
    HS : st_ok_pi _ _ _ _ _, MEQ : JKEEP M, PRS : JPRES M |- _ =>
  assert (U2 : bv_unsigned (ew (JE R j la) 2) = spZ regs0 - 128) by (apply (jU_reg R j la 2 2%bv); [lia | reflexivity | exact H2 | lia]);
  assert (U9 : bv_unsigned (ew (JE R j la) 9) = SHADOW_OFF) by (apply (jU_reg R j la 9 9%bv); [lia | reflexivity | exact H9 | unfold SHADOW_OFF; lia]);
  assert (U19 : bv_unsigned (ew (JE R j la) 19) = n) by (apply (jU_reg R j la 19 19%bv); [lia | reflexivity | exact H19 | lia]);
  assert (U20 : bv_unsigned (ew (JE R j la) 20) = b) by (apply (jU_reg R j la 20 20%bv); [lia | reflexivity | exact H20 | lia]);
  assert (U10 : bv_unsigned (ew (JE R j la) 10) = j) by (apply (jU_reg R j la 10 10%bv); [lia | reflexivity | exact H10 | lia]);
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
  try (pose proof (jE_C R j la 1 ltac:(lia) ltac:(lia)) as EC1; cbn [Nat.add Z.of_nat] in EC1;
       assert (UC1 : bv_unsigned (ew (JE R j la) 47) = jbyte BZ (j + 1)) by (rewrite EC1; apply unsigned_lit_small; pose proof (HnZ (j + 1) ltac:(lia)); lia));
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
Lemma js_L_d1 : js_L_d1_stmt.
Proof.
intros HCF HCS Q HQ.
assert (G : forall (m : nat) R M md j f, Z.of_nat m = n - j -> JNPRE R M md -> getr R 10 = w64 j -> getr R 12 = w64 JM10 ->
  0 <= i <= j -> j < n -> n - j < Z.of_nat f -> jscalar BZ i = jtail1 (jdigits BZ j f) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_LD1)) M (seg_rom SEGS)) md) Q).
2:{ intros R M md j f HN H10 H12 Hij Hjn Hf HJS. exact (G (Z.to_nat (n - j)) R M md j f ltac:(lia) HN H10 H12 Hij Hjn Hf HJS). }
induction m as [m IH] using lt_wf_ind.
intros R M md j f Hm HN H10 H12 Hij Hjn Hf HJS.
destruct f as [|f]; [cbn in Hf; lia|].
pose proof HN as (HI & H18 & H15 & H16).
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
pose proof (jstate R M md JS_LD1 j 1 jal_n0 HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_n0_ok R j 1 H20 H10 ltac:(lia))) as HS.
jpin HS 12 JM10 H12.
nsetup R M j 1%nat JS_LD1 HnZ.
nrun j JS_CFRAC.
psrr_branch_tok RUN BR HS SHOK JBspan.
- nconv Hc.
  nrun j JS_CFRAC.
  pmkst HS.
  eapply (HCF Q HQ _ _ _ j).
  + njnpre HS.
  + nrg HS.
  + lia.
  + lia.
  + rewrite HJS. rewrite (jdigits_nd BZ j (Datatypes.S f) Hc). reflexivity.
- nconv Hc. rename Hc into BFd.
  nrun j JS_CST.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  + nconv Hc.
    nrun j JS_LD1.
    pmkst HS.
    eapply (IH (Z.to_nat (n - (j + 1))) ltac:(lia) _ _ _ (j + 1) f).
    * lia.
    * njnpre HS.
    * nrg HS.
    * nrg HS.
    * lia.
    * lia.
    * lia.
    * rewrite HJS. rewrite (jdigits_d BZ j f ltac:(rewrite jlen_BZ; lia) BFd). reflexivity.
  + nconv Hc.
    nrun j JS_CST.
    pmkst HS.
    eapply (HCS Q HQ _ _ _ n).
    * njnpre HS.
    * nrg HS.
    * lia.
    * lia.
    * rewrite HJS. rewrite (jdigits_d BZ j f ltac:(rewrite jlen_BZ; lia) BFd).
      rewrite (jdigits_end BZ (j + 1) f ltac:(rewrite jlen_BZ; lia)). replace (j + 1) with n by lia. exact jtail1_end.
Qed.
Lemma js_L_d2 : js_L_d2_stmt.
Proof.
intros HCE HCS Q HQ.
assert (G : forall (m : nat) R M md j f, Z.of_nat m = n - j -> JNPRE R M md -> getr R 10 = w64 j -> getr R 12 = w64 JM10 ->
  0 <= i <= j -> j < n -> n - j < Z.of_nat f -> jscalar BZ i = jtail (jdigits BZ j f) ->
  SRr SEGS W (mkCfg (mkst R (Z_to_bv 64 (BASE + JS_LD2)) M (seg_rom SEGS)) md) Q).
2:{ intros R M md j f HN H10 H12 Hij Hjn Hf HJS. exact (G (Z.to_nat (n - j)) R M md j f ltac:(lia) HN H10 H12 Hij Hjn Hf HJS). }
induction m as [m IH] using lt_wf_ind.
intros R M md j f Hm HN H10 H12 Hij Hjn Hf HJS.
destruct f as [|f]; [cbn in Hf; lia|].
pose proof HN as (HI & H18 & H15 & H16).
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
pose proof (jstate R M md JS_LD2 j 1 jal_n0 HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_n0_ok R j 1 H20 H10 ltac:(lia))) as HS.
jpin HS 12 JM10 H12.
nsetup R M j 1%nat JS_LD2 HnZ.
nrun j JS_CEXP.
psrr_branch_tok RUN BR HS SHOK JBspan.
- nconv Hc.
  nrun j JS_CEXP.
  pmkst HS.
  eapply (HCE Q HQ _ _ _ j).
  + njnpre HS.
  + nrg HS.
  + lia.
  + lia.
  + rewrite HJS. rewrite (jdigits_nd BZ j (Datatypes.S f) Hc). reflexivity.
- nconv Hc. rename Hc into BFd.
  nrun j JS_CST.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  + nconv Hc.
    nrun j JS_LD2.
    pmkst HS.
    eapply (IH (Z.to_nat (n - (j + 1))) ltac:(lia) _ _ _ (j + 1) f).
    * lia.
    * njnpre HS.
    * nrg HS.
    * nrg HS.
    * lia.
    * lia.
    * lia.
    * rewrite HJS. rewrite (jdigits_d BZ j f ltac:(rewrite jlen_BZ; lia) BFd). reflexivity.
  + nconv Hc.
    nrun j JS_CST.
    pmkst HS.
    eapply (HCS Q HQ _ _ _ n).
    * njnpre HS.
    * nrg HS.
    * lia.
    * lia.
    * rewrite HJS. rewrite (jdigits_d BZ j f ltac:(rewrite jlen_BZ; lia) BFd).
      rewrite (jdigits_end BZ (j + 1) f ltac:(rewrite jlen_BZ; lia)). replace (j + 1) with n by lia. exact jtail_end.
Qed.
Lemma js_C_frac : js_C_frac_stmt.
Proof.
intros HD2 HCE Q HQ R M md j1 HN H10 Hij Hjn HJS.
pose proof HN as (HI & H18 & H15 & H16).
pose proof HI as (HJ & HSL & MEQ & PRS & H2 & H3 & H4 & H9 & H19 & H20).
pose proof jb_hi as Hbhi. pose proof jsp_hi as Hsph. pose proof jwin_lo as Hwl.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : TJSON_SCALAR_STK = 128 + 2 * 4096) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HnZ : forall t, 0 <= t < n -> 0 <= jbyte BZ t < 256) by (intros t Ht; exact (proj2 (jbyte_mem M t MEQ Ht))).
assert (HLB : length BZ = length BS) by (unfold BZ; apply length_map).
destruct (Z_lt_le_dec j1 n) as [Hj1|Hj1].
2:{
  pose proof (jstate R M md JS_CFRAC j1 0 jal_n1 HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_n1_ok R j1 0 H20 H10 ltac:(lia))) as HS.
  nsetup R M j1 0%nat JS_CFRAC HnZ.
  nrun j1 JS_CEXP.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  - nconv Hc. nrun j1 JS_CEXP.
    pmkst HS. eapply (HCE Q HQ _ _ _ j1); [njnpre HS | nrg HS | lia | lia | rewrite HJS; unfold jtail1, jfrac; ndec; reflexivity].
  - nconv Hc. exfalso. lia. }
destruct (Z_lt_le_dec (j1 + 1) n) as [Hj2|Hj2].
- pose proof (jstate R M md JS_CFRAC j1 2 jal_n1 HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_n1_ok R j1 2 H20 H10 ltac:(lia))) as HS.
  nsetup R M j1 2%nat JS_CFRAC HnZ.
  nrun j1 JS_CEXP.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  + nconv Hc. exfalso. lia.
  + nconv Hc. rename Hc into Hlt1. nrun j1 JS_CEXP.
    psrr_branch_tok RUN BR HS SHOK JBspan.
    * nconv Hc. nrun j1 JS_CEXP.
      pmkst HS. eapply (HCE Q HQ _ _ _ j1); [njnpre HS | nrg HS | lia | lia | rewrite HJS; unfold jtail1, jfrac; ndec; reflexivity].
    * nconv Hc. rename Hc into Hdot. nrun j1 JS_EPI.
      psrr_branch_tok RUN BR HS SHOK JBspan.
      -- nconv Hc. exfalso. lia.
      -- nconv Hc. rename Hc into Hlt2. nrun j1 JS_LD2.
         psrr_branch_tok RUN BR HS SHOK JBspan.
         ++ nconv Hc. nrun j1 JS_EPI.
            assert (HNone : jtail1 j1 = None) by (unfold jtail1, jfrac, jdig_at; ndec; reflexivity).
            nex_epi HQ HJS HNone.
         ++ nconv Hc. nrun j1 JS_LD2.
            pmkst HS. eapply (HD2 Q HQ _ _ _ (j1 + 1) (length BS)).
            ** njnpre HS.
            ** nrg HS.
            ** nrg HS.
            ** lia.
            ** lia.
            ** lia.
            ** rewrite HJS. unfold jtail1, jfrac, jdig_at. ndec. rewrite HLB. reflexivity.
- pose proof (jstate R M md JS_CFRAC j1 1 jal_n1 HI ltac:(lia) ltac:(lia) ltac:(lia) (jal_n1_ok R j1 1 H20 H10 ltac:(lia))) as HS.
  nsetup R M j1 1%nat JS_CFRAC HnZ.
  nrun j1 JS_CEXP.
  psrr_branch_tok RUN BR HS SHOK JBspan.
  + nconv Hc. exfalso. lia.
  + nconv Hc. rename Hc into Hlt1. nrun j1 JS_CEXP.
    psrr_branch_tok RUN BR HS SHOK JBspan.
    * nconv Hc. nrun j1 JS_CEXP.
      pmkst HS. eapply (HCE Q HQ _ _ _ j1); [njnpre HS | nrg HS | lia | lia | rewrite HJS; unfold jtail1, jfrac; ndec; reflexivity].
    * nconv Hc. rename Hc into Hdot. nrun j1 JS_EPI.
      psrr_branch_tok RUN BR HS SHOK JBspan.
      -- nconv Hc. nrun j1 JS_EPI.
         assert (HNone : jtail1 j1 = None) by (unfold jtail1, jfrac, jdig_at; ndec; reflexivity).
         nex_epi HQ HJS HNone.
      -- nconv Hc. exfalso. lia.
Qed.
End J. End h. End f. End d.
