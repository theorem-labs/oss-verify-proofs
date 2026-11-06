(* The values of the index expressions that the compiler emitted inside reac_headamp_tx_next, as the
   symbolic engine of lib/A/Prog builds them: idx / 3 and idx mod 3 by multiply-and-shift, and the two
   byte addresses tx + 288 + idx and tx + idx. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP0i YCbn YI04.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import NextLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition IDX : sv := SOff 46 0.
Definition Q3 : sv := SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND IDX (SLit 255)) (SLit 171)) (SLit 9).
Definition T3Q : sv := SAlu ALU_ADD (SAlu ALU_SLL Q3 (SLit 1)) Q3.
Definition RMraw : sv := SAlu ALU_SUB IDX T3Q.
Definition RM : sv := SAlu ALU_AND RMraw (SLit 255).
Definition DEXPR : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 288) T3Q) RM.
Definition VEXPR : sv := SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 0) T3Q) RM.

Definition JJ : sv := SOff 51 0.
Definition MJ : sv := SMd M_MUL JJ (SLit 1431655766).
Definition D3 : sv := SAlu ALU_ADD (SAlu ALU_SRL MJ (SLit 32)) (SAlu ALU_SRL MJ (SLit 63)).
Definition PP : sv := SAlu ALU_SUB (SAlu ALU_SUB JJ D3) (SAlu ALU_SLL D3 (SLit 1)).

Lemma U_IDX : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E IDX = i.
Proof. intros E i Hi R. unfold IDX. apply (U_atom E 46 i Hi). lia. Qed.

Lemma U_Q3 : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E Q3 = i / 3.
Proof.
intros E i Hi R. unfold Q3.
rewrite (U_SAlu E ALU_SRL (SMd M_MUL (SAlu ALU_AND IDX (SLit 255)) (SLit 171)) (SLit 9)). cbn [zalu_raw].
rewrite (U_SMd E M_MUL (SAlu ALU_AND IDX (SLit 255)) (SLit 171)). cbn [zmd_raw].
rewrite (U_and_lit E IDX 255) by lia. rewrite (U_IDX E i Hi R), !U_SLit.
change (zcanon 171) with 171. change (Z.land (zcanon 9) 63) with 9.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 9) with 512.
change (zcanon (Z.land i 255 * 171)) with ((Z.land i 255 * 171) mod 18446744073709551616).
rewrite (div3_171 i R). apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.

Lemma U_T3Q : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E T3Q = 3 * (i / 3).
Proof.
intros E i Hi R. unfold T3Q.
rewrite (U_SAlu E ALU_ADD (SAlu ALU_SLL Q3 (SLit 1)) Q3). cbn [zalu_raw].
rewrite (U_SAlu E ALU_SLL Q3 (SLit 1)). cbn [zalu_raw].
rewrite (U_Q3 E i Hi R), U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (i / 3 * 2)) by (unfold M64; Z.div_mod_to_equations; lia).
rewrite zcanon_id by (unfold M64; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma U_RMraw : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E RMraw = i mod 3.
Proof.
intros E i Hi R. unfold RMraw.
rewrite (U_SAlu E ALU_SUB IDX T3Q). cbn [zalu_raw].
rewrite (U_IDX E i Hi R), (U_T3Q E i Hi R).
rewrite Z.mod_eq by lia. apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.

Lemma U_RM : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 -> U E RM = i mod 3.
Proof.
intros E i Hi R. unfold RM. rewrite (U_and_lit E RMraw 255) by lia. rewrite (U_RMraw E i Hi R).
apply land255. pose proof (Z.mod_pos_bound i 3 ltac:(lia)). lia.
Qed.

Lemma U_JJ : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 144 -> U E JJ = j.
Proof. intros E j Hj R. unfold JJ. apply (U_atom E 51 j Hj). lia. Qed.

Lemma U_MJ : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 144 -> U E MJ = j * 1431655766.
Proof.
intros E j Hj R. unfold MJ. rewrite (U_SMd E M_MUL JJ (SLit 1431655766)). cbn [zmd_raw].
rewrite (U_JJ E j Hj R), U_SLit. change (zcanon 1431655766) with 1431655766.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma U_D3 : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 144 -> U E D3 = j / 3.
Proof.
intros E j Hj R. unfold D3.
rewrite (U_SAlu E ALU_ADD (SAlu ALU_SRL MJ (SLit 32)) (SAlu ALU_SRL MJ (SLit 63))). cbn [zalu_raw].
rewrite (U_SAlu E ALU_SRL MJ (SLit 32)), (U_SAlu E ALU_SRL MJ (SLit 63)). cbn [zalu_raw].
rewrite (U_MJ E j Hj R), !U_SLit.
change (Z.land (zcanon 32) 63) with 32. change (Z.land (zcanon 63) 63) with 63.
rewrite !Z.shiftr_div_pow2 by lia.
change (2 ^ 32) with 4294967296. change (2 ^ 63) with 9223372036854775808.
rewrite (div3_hi j), (div3_sign j) by lia.
change (zcanon 0) with 0. rewrite Z.add_0_r.
rewrite (zcanon_id (j / 3)) by (unfold M64; Z.div_mod_to_equations; lia).
apply zcanon_id. unfold M64. Z.div_mod_to_equations. lia.
Qed.

Lemma U_PP : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 144 -> U E PP = j mod 3.
Proof.
intros E j Hj R. unfold PP.
rewrite (U_SAlu E ALU_SUB (SAlu ALU_SUB JJ D3) (SAlu ALU_SLL D3 (SLit 1))). cbn [zalu_raw].
rewrite (U_SAlu E ALU_SUB JJ D3), (U_SAlu E ALU_SLL D3 (SLit 1)). cbn [zalu_raw].
rewrite (U_JJ E j Hj R), (U_D3 E j Hj R), U_SLit. change (Z.land (zcanon 1) 63) with 1.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
rewrite (zcanon_id (j - j / 3)) by (unfold M64; Z.div_mod_to_equations; lia).
rewrite (zcanon_id (j / 3 * 2)) by (unfold M64; Z.div_mod_to_equations; lia).
rewrite zcanon_id by (unfold M64; Z.div_mod_to_equations; lia). rewrite Z.mod_eq by lia. lia.
Qed.

Lemma q3_denot : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 ->
  sv_denot E Q3 = Z_to_bv 64 (i / 3).
Proof. intros E i Hi R. rewrite denot_lit_U, (U_Q3 E i Hi R). reflexivity. Qed.

Lemma t3q_denot : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 ->
  sv_denot E T3Q = Z_to_bv 64 (3 * (i / 3)).
Proof. intros E i Hi R. rewrite denot_lit_U, (U_T3Q E i Hi R). reflexivity. Qed.

Lemma rm_denot : forall E i, ew E 46 = Z_to_bv 64 i -> 0 <= i < 144 ->
  sv_denot E RMraw = Z_to_bv 64 (i mod 3) /\ sv_denot E RM = Z_to_bv 64 (i mod 3).
Proof.
intros E i Hi R. split.
- rewrite denot_lit_U, (U_RMraw E i Hi R). reflexivity.
- rewrite denot_lit_U, (U_RM E i Hi R). reflexivity.
Qed.

Lemma dexpr_denot : forall E tx i, ew E 10 = Z_to_bv 64 tx -> ew E 46 = Z_to_bv 64 i ->
  0 <= i < 144 -> 0 <= tx -> tx + 460 <= 2 ^ 47 ->
  sv_denot E DEXPR = Z_to_bv 64 (tx + 288 + i) /\ sv_denot E VEXPR = Z_to_bv 64 (tx + i).
Proof.
intros E tx i Htx Hi R Rtx Rtx2. pose proof (Z.div_mod i 3 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound i 3 ltac:(lia)) as Hmb.
assert (Hq : 0 <= 3 * (i / 3) <= i) by lia.
split.
- rewrite denot_lit_U. f_equal. unfold DEXPR.
  rewrite (U_SAlu E ALU_ADD (SAlu ALU_ADD (SOff 10 288) T3Q) RM). cbn [zalu_raw].
  rewrite (U_SAlu E ALU_ADD (SOff 10 288) T3Q). cbn [zalu_raw].
  rewrite (U_atom_off E 10 tx 288 Htx) by lia.
  rewrite (U_T3Q E i Hi R), (U_RM E i Hi R).
  rewrite (zcanon_id (tx + 288 + 3 * (i / 3))) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
- rewrite denot_lit_U. f_equal. unfold VEXPR.
  rewrite (U_SAlu E ALU_ADD (SAlu ALU_ADD (SOff 10 0) T3Q) RM). cbn [zalu_raw].
  rewrite (U_SAlu E ALU_ADD (SOff 10 0) T3Q). cbn [zalu_raw].
  rewrite (U_atom E 10 tx Htx) by lia.
  rewrite (U_T3Q E i Hi R), (U_RM E i Hi R).
  rewrite (zcanon_id (tx + 3 * (i / 3))) by (unfold M64; lia).
  rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma d3_denot : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 144 ->
  sv_denot E D3 = Z_to_bv 64 (j / 3).
Proof. intros E j Hj R. rewrite denot_lit_U, (U_D3 E j Hj R). reflexivity. Qed.

Lemma pp_denot : forall E j, ew E 51 = Z_to_bv 64 j -> 0 <= j < 144 ->
  sv_denot E PP = Z_to_bv 64 (j mod 3).
Proof. intros E j Hj R. rewrite denot_lit_U, (U_PP E j Hj R). reflexivity. Qed.
