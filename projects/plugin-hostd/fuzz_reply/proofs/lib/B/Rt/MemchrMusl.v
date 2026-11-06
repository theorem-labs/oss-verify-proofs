(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/YE3a.v's walk of musl memchr, generalised to any byte c in a1 and to a window that may hold no c at all (the count runs out); YE3a's fetch/decode lemmas, constants and step tactics are used as YE3a states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_disco/lib/A/Rt/MemchrMusl.v
   (a working branch 3b8a77d146c, the general memchr), with its module paths changed (it carries no address: the musl memchr body is YE3a.v's fetch/decode lemmas, already at the image's musl memchr: fuzz_reply.asan 0x963d0 in lib/A, fuzz_reply.asan-ubsan 0x96950 in this file, through YE3a.v). *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/Rt/MemchrMusl.v (a working branch b499e5453f1): lib/A's cgif-layer modules replaced by their lib/B twins; it carries no address. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1w YE3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition SPL : Z := 72340172838076673.
Lemma u8_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz.
Qed.
Lemma unsigned_lit_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. apply u_Z2bv; lia. Qed.
Lemma zb_lxor : forall u w i, HZ.zb (Z.lxor u w) i = Z.lxor (HZ.zb u i) (HZ.zb w i).
Proof.
intros u w i. apply Z.bits_inj'. intros j Hj.
rewrite Z.lxor_spec, !zb_testbit, Z.lxor_spec by lia.
destruct (j <? 8); reflexivity.
Qed.
Lemma splat_bytes : forall cc, 0 <= cc < 256 ->
bytes_le_to_Z [Z_to_bv 8 cc; Z_to_bv 8 cc; Z_to_bv 8 cc; Z_to_bv 8 cc;
Z_to_bv 8 cc; Z_to_bv 8 cc; Z_to_bv 8 cc; Z_to_bv 8 cc] = cc * SPL.
Proof.
intros cc Hcc. rewrite bytes_le_to_Z_zdig. cbn [map HZ.zdig].
rewrite (u8_lit cc) by lia. unfold SPL. lia.
Qed.
Lemma zb_splat : forall cc i, 0 <= cc < 256 -> (i < 8)%nat -> HZ.zb (cc * SPL) i = cc.
Proof.
intros cc i Hcc Hi. rewrite <- (splat_bytes cc Hcc).
rewrite zb_of_bytes by (cbn [length]; lia).
do 8 (destruct i as [|i]; [cbn [nth]; apply u8_lit; lia|]). lia.
Qed.
Lemma splat_range : forall cc, 0 <= cc < 256 -> 0 <= cc * SPL < 2 ^ 64.
Proof. intros cc Hcc. unfold SPL. lia. Qed.
End G.
Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable p : word.
Variable n c k : Z.
Variable f : Z -> byte.
Variable mem rom : word -> option byte.
Definition MX : Z := bv_unsigned p.
Hypothesis Hc : 0 <= c < 256.
Hypothesis Hn0 : 0 <= n.
Hypothesis Hfit : MX + n + 8 < 2 ^ 64.
Hypothesis Hbytes : forall i, 0 <= i < n -> rdn tfibsegs mem (Z_to_bv 64 (MX + i)) 1 = Some [f i].
Hypothesis Hrom : forall a : Z,
tfib_D_const_HIGHS_0x8080808080808080 <= a < tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Hypothesis Hk : 0 <= k <= n.
Hypothesis Hbef : forall i, 0 <= i < k -> bv_unsigned (f i) <> c.
Hypothesis Hat : k < n -> bv_unsigned (f k) = c.
Definition RES : Z := if k <? n then MX + k else 0.
Lemma MX_range : 0 <= MX < 2 ^ 64.
Proof. unfold MX. apply u64_range. Qed.
Lemma kn_res_found : forall i0, 0 <= i0 < n -> bv_unsigned (f i0) = c -> i0 <= k -> RES = MX + i0 /\ k = i0.
Proof.
intros i0 Hi Hfc Hik.
assert (Hk0 : k = i0).
{ destruct (Z.eq_dec k i0) as [He|Hne]; [exact He|]. exfalso. apply (Hbef i0 ltac:(lia)). exact Hfc. }
split; [|exact Hk0]. unfold RES. rewrite Hk0.
replace (i0 <? n) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.
Lemma kn_res_none : k = n -> RES = 0.
Proof.
intros Hkn. unfold RES. rewrite Hkn.
replace (n <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma mg_tail : forall (d : nat) regs (i0 : Z),
Z.of_nat d = n - i0 -> 0 <= i0 -> i0 < n -> i0 <= k ->
getr regs 10 = Z_to_bv 64 (MX + i0) ->
getr regs 11 = Z_to_bv 64 c ->
getr regs 13 = Z_to_bv 64 (n - i0) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0xa0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
pose proof MX_range as HP.
induction d as [|d IH]; intros regs i0 Hd Hi0 Hin Hik H10 H11 H13; [lia|].
pose proof (u8_range (f i0)) as Hb8.
assert (HR : rdn tfibsegs mem (Z_to_bv 64 (MX + i0)) 1 = Some [f i0]) by (apply Hbytes; lia).
destruct (Z.eq_dec (bv_unsigned (f i0)) c) as [Heq|Hne].
-
destruct (kn_res_found i0 ltac:(lia) Heq Hik) as [HRES Hk0].
eexists. split.
+ norm_pc.
steplbu FM_0a0 DM_0a0 ltac:(rewrite H10; imm_norm; rewrite v_addi_0; exact HR).
stepbt FM_0a4 DM_0a4 ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_eq; exact Heq).
stepret FM_0b8 DM_0b8. msteps_done.
+ split; [gr; rewrite H10, HRES; reflexivity|].
intros r Hr10 Hr12 Hr13. rewrite !getr_other by assumption. reflexivity.
-
assert (Hk1 : i0 + 1 <= k).
{ destruct (Z.eq_dec k i0) as [Hke|Hne']; [exfalso; apply Hne; rewrite <- Hke; apply Hat; lia | lia]. }
destruct (Nat.eq_dec d 0) as [Hd0|Hd0].
+
assert (Hn1 : n - i0 = 1) by lia.
assert (HRES : RES = 0) by (apply kn_res_none; lia).
eexists. split.
* norm_pc.
steplbu FM_0a0 DM_0a0 ltac:(rewrite H10; imm_norm; rewrite v_addi_0; exact HR).
stepbf FM_0a4 DM_0a4 ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_neq; exact Hne).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 0)
ltac:(gr; rewrite H13, Hn1; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (MX + i0 + 1))
ltac:(gr; rewrite H10; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepbf FM_0b0 DM_0b0 ltac:(gr; cbn [branch_taken]; apply negb_false_iff; unfold bv_eqb;
rewrite !u_lit0; reflexivity).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; imm_norm; rewrite v_addi_0; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
* split; [gr; rewrite HRES; reflexivity|].
intros r Hr10 Hr12 Hr13. rewrite !getr_other by assumption. reflexivity.
+
set (regs1 := regupd (regupd (regupd regs 12 (Z_to_bv 64 (bv_unsigned (f i0))))
13 (Z_to_bv 64 (n - i0 - 1))) 10 (Z_to_bv 64 (MX + i0 + 1))).
destruct (IH regs1 (i0 + 1)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs1. gr. f_equal. lia. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. f_equal. lia. }
exists regs'. split.
* eapply msteps_trans;
[|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
steplbu FM_0a0 DM_0a0 ltac:(rewrite H10; imm_norm; rewrite v_addi_0; exact HR).
stepbf FM_0a4 DM_0a4 ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_neq; exact Hne).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 (n - i0 - 1))
ltac:(gr; rewrite H13; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (MX + i0 + 1))
ltac:(gr; rewrite H10; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepbt FM_0b0 DM_0b0 ltac:(gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite unsigned_lit_small, u_lit0 by lia; apply Z.eqb_neq; lia).
subst regs1. msteps_done.
* split; [exact H10'|].
intros r Hr10 Hr12 Hr13. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mg_t98 : forall regs (i0 : Z),
0 <= i0 <= n -> i0 <= k ->
getr regs 10 = Z_to_bv 64 (MX + i0) ->
getr regs 11 = Z_to_bv 64 c ->
getr regs 12 = Z_to_bv 64 (n - i0) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x98)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
intros regs i0 Hi0 Hik H10 H11 H12. pose proof MX_range as HP.
set (regs1 := regupd regs 13 (Z_to_bv 64 (n - i0))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x98)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0x9c)) mem rom)).
{ norm_pc.
stepiv' FM_098 DM_098 (Z_to_bv 64 (n - i0)) ltac:(gr; rewrite H12; imm_norm; apply v_addi_0).
subst regs1. msteps_done. }
destruct (Z.eq_dec i0 n) as [Hne|Hlt].
-
assert (HRES : RES = 0) by (apply kn_res_none; lia).
eexists. split.
+ eapply msteps_trans; [exact Hpre|]. norm_pc.
stepbt FM_09c DM_09c ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; unfold bv_eqb;
rewrite unsigned_lit_small, u_lit0 by lia; apply Z.eqb_eq; lia).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; imm_norm; rewrite v_addi_0; reflexivity).
replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
+ split; [gr; rewrite HRES; reflexivity|].
intros r Hr10 Hr12 Hr13. rewrite !getr_other by assumption. subst regs1.
rewrite !getr_other by assumption. reflexivity.
-
destruct (mg_tail (Z.to_nat (n - i0)) regs1 i0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_09c DM_09c ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; unfold bv_eqb;
rewrite unsigned_lit_small, u_lit0 by lia; apply Z.eqb_neq; lia).
subst regs1. msteps_done.
+ split; [exact H10'|].
intros r Hr10 Hr12 Hr13. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mg_found : forall regs (i0 : Z),
0 <= i0 -> i0 < n -> i0 <= k ->
getr regs 10 = Z_to_bv 64 (MX + i0) ->
getr regs 11 = Z_to_bv 64 c ->
getr regs 12 = Z_to_bv 64 (n - i0) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0xbc)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> getr regs' r = getr regs r).
Proof.
intros regs i0 Hi0 Hin Hik H10 H11 H12. pose proof MX_range as HP.
pose proof (u8_range (f i0)) as Hb8.
assert (HR : rdn tfibsegs mem (Z_to_bv 64 (MX + i0)) 1 = Some [f i0]) by (apply Hbytes; lia).
set (regs1 := regupd (regupd regs 13 (Z_to_bv 64 (n - i0))) 12 (Z_to_bv 64 (bv_unsigned (f i0)))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0xbc)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0xc4)) mem rom)).
{ norm_pc.
stepiv' FM_0bc DM_0bc (Z_to_bv 64 (n - i0)) ltac:(gr; rewrite H12; imm_norm; apply v_addi_0).
steplbu FM_0c0 DM_0c0 ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; exact HR).
subst regs1. msteps_done. }
destruct (Z.eq_dec (bv_unsigned (f i0)) c) as [Heq|Hne].
-
destruct (kn_res_found i0 ltac:(lia) Heq Hik) as [HRES Hk0].
eexists. split.
+ eapply msteps_trans; [exact Hpre|]. norm_pc.
stepbf FM_0c4 DM_0c4 ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken];
apply negb_false_iff; unfold bv_eqb; rewrite u_zext8, unsigned_lit_small by lia;
apply Z.eqb_eq; exact Heq).
stepj' FM_0c8 DM_0c8.
replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
+ subst regs1. split; [gr; rewrite H10, HRES; reflexivity|].
intros r Hr10 Hr12 Hr13. rewrite !getr_other by assumption. reflexivity.
-
assert (Hk1 : i0 + 1 <= k).
{ destruct (Z.eq_dec k i0) as [Hke|Hne']; [exfalso; apply Hne; rewrite <- Hke; apply Hat; lia | lia]. }
destruct (Z.eq_dec (n - i0) 1) as [Hn1|Hn1].
+
assert (HRES : RES = 0) by (apply kn_res_none; lia).
eexists. split.
* eapply msteps_trans; [exact Hpre|]. norm_pc.
stepbt FM_0c4 DM_0c4 ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken];
apply negb_true_iff; unfold bv_eqb; rewrite u_zext8, unsigned_lit_small by lia;
apply Z.eqb_neq; exact Hne).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 0)
ltac:(subst regs1; gr; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (MX + i0 + 1))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepbf FM_0b0 DM_0b0 ltac:(gr; cbn [branch_taken]; apply negb_false_iff; unfold bv_eqb;
rewrite !u_lit0; reflexivity).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; imm_norm; rewrite v_addi_0; reflexivity).
replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
* split; [gr; rewrite HRES; reflexivity|].
intros r Hr10 Hr12 Hr13. rewrite !getr_other by assumption. subst regs1.
rewrite !getr_other by assumption. reflexivity.
+
set (regs2 := regupd (regupd regs1 13 (Z_to_bv 64 (n - i0 - 1))) 10 (Z_to_bv 64 (MX + i0 + 1))).
destruct (mg_tail (Z.to_nat (n - i0 - 1)) regs2 (i0 + 1)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs2 regs1. gr. f_equal. lia. }
{ subst regs2 regs1. gr. exact H11. }
{ subst regs2 regs1. gr. f_equal. lia. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_0c4 DM_0c4 ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken];
apply negb_true_iff; unfold bv_eqb; rewrite u_zext8, unsigned_lit_small by lia;
apply Z.eqb_neq; exact Hne).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 (n - i0 - 1))
ltac:(subst regs1; gr; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (MX + i0 + 1))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepbt FM_0b0 DM_0b0 ltac:(gr; cbn [branch_taken]; apply negb_true_iff; unfold bv_eqb;
rewrite unsigned_lit_small, u_lit0 by lia; apply Z.eqb_neq; lia).
subst regs2 regs1. msteps_done.
* split; [exact H10'|].
intros r Hr10 Hr12 Hr13. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mg_word : forall q, MX <= q -> q + 8 <= MX + n ->
exists bs, rdn tfibsegs mem (Z_to_bv 64 q) 8 = Some bs /\ length bs = 8%nat /\
(forall i, (i < 8)%nat -> nth i bs NUL = f (q - MX + Z.of_nat i)).
Proof.
intros q Hlo Hhi. pose proof MX_range as HP.
destruct (rdn_total tfibsegs mem 8 (Z_to_bv 64 q)) as [bs Hbs].
{ intros j Hj. rewrite word_add_nat, u_Z2bv by lia.
replace (q + Z.of_nat j) with (MX + (q - MX + Z.of_nat j)) by lia.
rewrite Hbytes by lia. discriminate. }
exists bs. split; [exact Hbs|]. split; [exact (rdn_length _ _ _ _ _ Hbs)|].
intros i Hi.
pose proof (rdn_nth tfibsegs mem 8 (Z_to_bv 64 q) bs i Hbs ltac:(lia)) as H1.
rewrite word_add_nat, u_Z2bv in H1 by lia.
replace (q + Z.of_nat i) with (MX + (q - MX + Z.of_nat i)) in H1 by lia.
rewrite Hbytes in H1 by lia. injection H1 as H2. symmetry. exact H2.
Qed.
Lemma rd_ONES : exists bs,
rdn tfibsegs mem (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) 8 = Some bs /\ bytes_le_to_Z bs = C1.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros j Hj. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
Lemma rd_HIGH : exists bs,
rdn tfibsegs mem (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) 8 = Some bs /\ bytes_le_to_Z bs = HZ.HIGHS.
Proof.
rodc.
rewrite (rdn_ext1 tfibsegs 8 mem (fun _ : word => @None byte) (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080)).
- eexists. split; [vm_compute; reflexivity|]. vm_compute. reflexivity.
- intros j Hj. rewrite word_add_nat, u_Z2bv by lia. apply Hrom. lia.
Qed.
Lemma mg_words : forall (K : nat) regs (i0 : Z),
0 <= i0 -> 8 <= n - i0 -> n - i0 <= 8 * Z.of_nat K + 7 -> i0 <= k ->
getr regs 10 = Z_to_bv 64 (MX + i0) ->
getr regs 11 = Z_to_bv 64 c ->
getr regs 12 = Z_to_bv 64 (n - i0) ->
getr regs 13 = Z_to_bv 64 C1 ->
getr regs 14 = Z_to_bv 64 HZ.HIGHS ->
getr regs 15 = Z_to_bv 64 (c * SPL) ->
getr regs 16 = Z_to_bv 64 7 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x74)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Proof.
pose proof MX_range as HP. pose proof (splat_range c Hc) as HSP.
induction K as [|K IH]; intros regs i0 Hi0 H8 HK Hik H10 H11 H12 H13 H14 H15 H16; [lia|].
destruct (mg_word (MX + i0)) as (bs & Hbs & Hlen & Hnth); [lia|lia|].
set (x := bytes_le_to_Z bs).
pose proof (bytes_le_to_Z_range bs Hlen) as Hx. fold x in Hx.
set (v := Z_to_bv 64 x).
assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
set (sw := Z_to_bv 64 (c * SPL)).
set (zv := v_xor v sw).
assert (Hzb : forall i, (i < 8)%nat -> HZ.zb (bv_unsigned zv) i = Z.lxor (bv_unsigned (f (i0 + Z.of_nat i))) c).
{ intros i Hi. subst zv. unfold v_xor. rewrite zb_u64 by lia. rewrite zb_lxor.
rewrite Hv. subst sw. rewrite (u_Z2bv (c * SPL)) by lia.
rewrite (zb_splat c i Hc Hi). subst x. rewrite zb_of_bytes by lia.
fold NUL. rewrite (Hnth i Hi). replace (MX + i0 - MX + Z.of_nat i) with (i0 + Z.of_nat i) by lia. reflexivity. }
set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) zv) zv) (Z_to_bv 64 HZ.HIGHS)).
assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz (bv_unsigned zv)) by (subst tw; apply haszero_ref).
pose proof (HZ.Tz_range (bv_unsigned zv)) as HT.
pose proof (u64_range zv) as Hzr.
set (regs5 := regupd (regupd (regupd (regupd (regupd regs 17 v) 17 zv)
5 (v_sub (Z_to_bv 64 C1) zv)) 17 (v_or (v_sub (Z_to_bv 64 C1) zv) zv)) 17 tw).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x74)) mem rom)
(mkst regs5 (Z_to_bv 64 (tfib_A_musl_memchr + 0x88)) mem rom)).
{ norm_pc.
chain_step; [reflexivity | eapply step_ld with (bs := bs) (v := v);
[exact_lit FM_074 | reflexivity | exact DM_074
| rewrite H10; imm_norm; rewrite v_addi_0; exact Hbs
| rewrite Hv; reflexivity ] | step_simpl ].
stepov FM_078 DM_078 zv ltac:(rewrite alu_xor; gr; rewrite H15; reflexivity).
stepov FM_07c DM_07c (v_sub (Z_to_bv 64 C1) zv) ltac:(rewrite alu_sub; gr; rewrite H13; reflexivity).
stepov FM_080 DM_080 (v_or (v_sub (Z_to_bv 64 C1) zv) zv) ltac:(rewrite alu_or; gr; reflexivity).
stepov FM_084 DM_084 tw ltac:(rewrite alu_and; gr; rewrite H14; reflexivity).
subst regs5. msteps_done. }
destruct (Z_lt_le_dec (k - i0) 8) as [Hin8|Hout8].
-
assert (Hkn : k < n) by lia.
assert (HTnz : HZ.Tz (bv_unsigned zv) <> 0).
{ apply (HZ.Tz_haszero (bv_unsigned zv) (Z.to_nat (k - i0))); [lia|lia| |].
- rewrite Hzb by lia. replace (i0 + Z.of_nat (Z.to_nat (k - i0))) with k by lia.
rewrite (Hat Hkn). apply Z.lxor_nilpotent.
- intros j Hj. rewrite Hzb by lia. intros Hz0. apply (proj1 (Z.lxor_eq_0_iff _ _)) in Hz0.
apply (Hbef (i0 + Z.of_nat j) ltac:(lia)). exact Hz0. }
destruct (mg_found regs5 i0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs5. gr. exact H10. }
{ subst regs5. gr. exact H11. }
{ subst regs5. gr. exact H12. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs5 1) by (subst regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_088 DM_088 ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken];
apply negb_true_iff; unfold bv_eqb; rewrite Htw, unsigned_lit_small by (unfold HZ.HIGHS; lia);
apply Z.eqb_neq; lia).
msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs5.
rewrite !getr_other by assumption. reflexivity.
-
assert (HTz : HZ.Tz (bv_unsigned zv) = 0).
{ apply HZ.Tz_nozero; [lia|]. intros i Hi. rewrite Hzb by lia. intros Hz0.
apply (proj1 (Z.lxor_eq_0_iff _ _)) in Hz0. apply (Hbef (i0 + Z.of_nat i) ltac:(lia)). exact Hz0. }
set (regs7 := regupd (regupd regs5 12 (Z_to_bv 64 (n - i0 - 8))) 10 (Z_to_bv 64 (MX + i0 + 8))).
assert (Hmid : msteps tfibsegs (mkst regs5 (Z_to_bv 64 (tfib_A_musl_memchr + 0x88)) mem rom)
(mkst regs7 (Z_to_bv 64 (tfib_A_musl_memchr + 0x94)) mem rom)).
{ norm_pc.
stepbf FM_088 DM_088 ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken];
unfold bv_eqb; rewrite Htw, HTz, unsigned_lit_small by (unfold HZ.HIGHS; lia);
rewrite Z.sub_0_r, Z.eqb_refl; reflexivity).
stepiv' FM_08c DM_08c (Z_to_bv 64 (n - i0 - 8))
ltac:(subst regs5; gr; rewrite H12; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_090 DM_090 (Z_to_bv 64 (MX + i0 + 8))
ltac:(subst regs5; gr; rewrite H10; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
subst regs7 regs5. msteps_done. }
destruct (Z_lt_le_dec 7 (n - i0 - 8)) as [Hmore|Hlast].
+
destruct (IH regs7 (i0 + 8)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs7 regs5. gr. f_equal. lia. }
{ subst regs7 regs5. gr. exact H11. }
{ subst regs7 regs5. gr. f_equal. lia. }
{ subst regs7 regs5. gr. exact H13. }
{ subst regs7 regs5. gr. exact H14. }
{ subst regs7 regs5. gr. exact H15. }
{ subst regs7 regs5. gr. exact H16. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs7 1) by (subst regs7 regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_094 DM_094 ltac:(subst regs7 regs5; gr; rewrite H16; cbn [branch_taken];
rewrite ltu_w by lia; apply Z.ltb_lt; lia).
subst regs7 regs5. msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr17). subst regs7 regs5.
rewrite !getr_other by assumption. reflexivity.
+
destruct (mg_t98 regs7 (i0 + 8)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs7 regs5. gr. f_equal. lia. }
{ subst regs7 regs5. gr. exact H11. }
{ subst regs7 regs5. gr. f_equal. lia. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs7 1) by (subst regs7 regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_094 DM_094 ltac:(subst regs7 regs5; gr; rewrite H16; cbn [branch_taken];
rewrite ltu_w by lia; apply Z.ltb_ge; lia).
subst regs7 regs5. msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs7 regs5.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mg_aligned : forall regs (i0 : Z),
0 <= i0 <= n -> i0 <= k ->
getr regs 10 = Z_to_bv 64 (MX + i0) ->
getr regs 11 = Z_to_bv 64 c ->
getr regs 12 = Z_to_bv 64 (n - i0) ->
getr regs 14 = Z_to_bv 64 (if n - i0 =? 0 then 0 else 1) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x44)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs i0 Hi0 Hik H10 H11 H12 H14. pose proof MX_range as HP.
pose proof (splat_range c Hc) as HSP.
destruct (Z.eq_dec i0 n) as [Hzero|Hpos].
-
assert (HRES : RES = 0) by (apply kn_res_none; lia).
eexists. split.
+ norm_pc.
stepbt FM_044 DM_044 ltac:(gr; rewrite H14; replace (n - i0 =? 0) with true by (symmetry; apply Z.eqb_eq; lia);
cbn [branch_taken]; unfold bv_eqb; rewrite !u_lit0; reflexivity).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; imm_norm; rewrite v_addi_0; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
+ split; [gr; rewrite HRES; reflexivity|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite !getr_other by assumption. reflexivity.
-
pose proof (u8_range (f i0)) as Hb8.
assert (HR : rdn tfibsegs mem (Z_to_bv 64 (MX + i0)) 1 = Some [f i0]) by (apply Hbytes; lia).
set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned (f i0)))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x44)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0x4c)) mem rom)).
{ norm_pc.
stepbf FM_044 DM_044 ltac:(gr; rewrite H14; replace (n - i0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
cbn [branch_taken]; unfold bv_eqb; rewrite !u_lit0, unsigned_lit_small by lia; apply Z.eqb_neq; lia).
steplbu FM_048 DM_048 ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; exact HR).
subst regs1. msteps_done. }
destruct (Z.eq_dec (bv_unsigned (f i0)) c) as [Heq|Hne].
+
destruct (mg_t98 regs1 i0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. exact H12. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_04c DM_04c ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_eq; exact Heq).
subst regs1. msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
+
assert (Hk1 : i0 + 1 <= k).
{ destruct (Z.eq_dec k i0) as [Hke|Hne']; [exfalso; apply Hne; rewrite <- Hke; apply Hat; lia | lia]. }
set (regs2 := regupd regs1 13 (Z_to_bv 64 8)).
assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0x4c)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_memchr + 0x54)) mem rom)).
{ norm_pc.
stepbf FM_04c DM_04c ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_neq; exact Hne).
stepiv' FM_050 DM_050 (Z_to_bv 64 8) ltac:(gr; imm_norm; unfold v_addi; rewrite u_lit0; reflexivity).
subst regs2 regs1. msteps_done. }
destruct (Z_lt_le_dec (n - i0) 8) as [Hsmall|Hbig].
*
destruct (mg_t98 regs2 i0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs2 regs1. gr. exact H10. }
{ subst regs2 regs1. gr. exact H11. }
{ subst regs2 regs1. gr. exact H12. }
exists regs'. split.
-- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_054 DM_054 ltac:(subst regs2 regs1; gr; rewrite H12; cbn [branch_taken];
rewrite ltu_w by lia; apply Z.ltb_lt; lia).
subst regs2 regs1. msteps_done.
-- split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13).
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
*
destruct rd_ONES as (bs1 & Hbs1 & Hv1).
destruct rd_HIGH as (bs2 & Hbs2 & Hv2).
set (regs3 := regupd (regupd (regupd (regupd (regupd (regupd (regupd regs2
13 (Z_to_bv 64 tfib_memchr_aui1)) 13 (Z_to_bv 64 C1))
14 (Z_to_bv 64 tfib_memchr_aui2)) 14 (Z_to_bv 64 HZ.HIGHS))
15 (Z_to_bv 64 (C1 + 1))) 15 (Z_to_bv 64 (c * SPL))) 16 (Z_to_bv 64 7)).
destruct (mg_words (Z.to_nat n) regs3 i0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs3 regs2 regs1. gr. exact H10. }
{ subst regs3 regs2 regs1. gr. exact H11. }
{ subst regs3 regs2 regs1. gr. exact H12. }
{ subst regs3 regs2 regs1. gr. reflexivity. }
{ subst regs3 regs2 regs1. gr. reflexivity. }
{ subst regs3 regs2 regs1. gr. reflexivity. }
{ subst regs3 regs2 regs1. gr. reflexivity. }
exists regs'. split.
-- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_054 DM_054 ltac:(subst regs2 regs1; gr; rewrite H12; cbn [branch_taken];
rewrite ltu_w by lia; apply Z.ltb_ge; lia).
stepiv' FM_058 DM_058 (Z_to_bv 64 tfib_memchr_aui1) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs1) (v := Z_to_bv 64 C1);
[ exact_lit FM_05c | reflexivity | exact DM_05c
| gr; match goal with |- rdn _ _ ?a _ = _ =>
replace a with (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) by bveq end; exact Hbs1
| rewrite Hv1; reflexivity ] | step_simpl ].
stepiv' FM_060 DM_060 (Z_to_bv 64 tfib_memchr_aui2) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs2) (v := Z_to_bv 64 HZ.HIGHS);
[ exact_lit FM_064 | reflexivity | exact DM_064
| gr; match goal with |- rdn _ _ ?a _ = _ =>
replace a with (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) by bveq end; exact Hbs2
| rewrite Hv2; reflexivity ] | step_simpl ].
stepiv' FM_068 DM_068 (Z_to_bv 64 (C1 + 1)) ltac:(gr; reflexivity).
stepiv' FM_06c DM_06c (Z_to_bv 64 (c * SPL))
ltac:(subst regs2 regs1; gr; rewrite H11; unfold v_mul; rewrite !unsigned_lit_small by (unfold C1; lia);
f_equal; unfold C1, SPL; lia).
stepiv' FM_070 DM_070 (Z_to_bv 64 7) ltac:(gr; reflexivity).
subst regs3 regs2 regs1. msteps_done.
-- split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr17).
subst regs3 regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mg_prologue : forall (FU : nat) regs (i0 : Z),
Z.of_nat FU >= n - i0 -> 0 <= i0 -> i0 < n -> i0 <= k ->
getr regs 10 = Z_to_bv 64 (MX + i0) ->
getr regs 11 = Z_to_bv 64 c ->
getr regs 12 = Z_to_bv 64 (n - i0) ->
getr regs 15 = Z_to_bv 64 (MX + i0 + 1) ->
getr regs 16 = Z_to_bv 64 1 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x1c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv ->
r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
pose proof MX_range as HP.
induction FU as [|FU IH]; intros regs i0 HFU Hi0 Hin Hik H10 H11 H12 H15 H16; [lia|].
pose proof (u8_range (f i0)) as Hb8.
assert (HR : rdn tfibsegs mem (Z_to_bv 64 (MX + i0)) 1 = Some [f i0]) by (apply Hbytes; lia).
set (regs1 := regupd (regupd regs 14 (Z_to_bv 64 (bv_unsigned (f i0)))) 13 (Z_to_bv 64 (n - i0))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x1c)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0x24)) mem rom)).
{ norm_pc.
steplbu FM_01c DM_01c ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; exact HR).
stepiv' FM_020 DM_020 (Z_to_bv 64 (n - i0)) ltac:(gr; rewrite H12; imm_norm; apply v_addi_0).
subst regs1. msteps_done. }
destruct (Z.eq_dec (bv_unsigned (f i0)) c) as [Heq|Hne].
-
destruct (mg_tail (Z.to_nat (n - i0)) regs1 i0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs1. gr. exact H10. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_024 DM_024 ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_eq; exact Heq).
subst regs1. msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r Hr10 Hr12 Hr13). subst regs1.
rewrite !getr_other by assumption. reflexivity.
-
assert (Hk1 : i0 + 1 <= k).
{ destruct (Z.eq_dec k i0) as [Hke|Hne']; [exfalso; apply Hne; rewrite <- Hke; apply Hat; lia | lia]. }
assert (Hm8 : 0 <= (MX + i0 + 1) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs2 := regupd (regupd (regupd (regupd regs1
10 (Z_to_bv 64 (MX + i0 + 1)))
12 (Z_to_bv 64 (n - i0 - 1)))
17 (Z_to_bv 64 ((MX + i0 + 1) mod 8)))
14 (Z_to_bv 64 (if n - i0 - 1 =? 0 then 0 else 1))).
assert (Hmid : msteps tfibsegs (mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0x24)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_memchr + 0x38)) mem rom)).
{ norm_pc.
stepbf FM_024 DM_024 ltac:(subst regs1; gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, unsigned_lit_small by lia; apply Z.eqb_neq; exact Hne).
stepiv' FM_028 DM_028 (Z_to_bv 64 (MX + i0 + 1))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_02c DM_02c (Z_to_bv 64 (n - i0 - 1))
ltac:(subst regs1; gr; imm_norm; unfold v_addi; rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_030 DM_030 (Z_to_bv 64 ((MX + i0 + 1) mod 8))
ltac:(subst regs1; gr; rewrite H15; imm_norm; unfold v_andi;
rewrite unsigned_lit_small by lia; change (bv_wrap 64 7) with (Z.ones 3);
rewrite Z.land_ones by lia; reflexivity).
stepov FM_034 DM_034 (Z_to_bv 64 (if n - i0 - 1 =? 0 then 0 else 1))
ltac:(rewrite alu_sltu; subst regs1; gr; unfold v_sltu, c_ltu;
rewrite ltu_w by lia; destruct (Z.eq_dec (n - i0 - 1) 0) as [He0|He0];
[ replace (n - i0 - 1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia);
replace (0 <? n - i0 - 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
| replace (n - i0 - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
replace (0 <? n - i0 - 1) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity ]).
subst regs2 regs1. msteps_done. }
destruct (Z.eq_dec ((MX + i0 + 1) mod 8) 0) as [Hal|Hal].
+
destruct (mg_aligned regs2 (i0 + 1)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs2 regs1. gr. f_equal. lia. }
{ subst regs2 regs1. gr. exact H11. }
{ subst regs2 regs1. gr. f_equal. lia. }
{ subst regs2 regs1. gr. f_equal. replace (n - (i0 + 1)) with (n - i0 - 1) by lia. reflexivity. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_038 DM_038 ltac:(subst regs2; gr; rewrite Hal; cbn [branch_taken]; unfold bv_eqb;
rewrite !u_lit0; reflexivity).
subst regs2 regs1. msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
+
destruct (Z.eq_dec (n - i0) 1) as [Hlast|Hmore].
*
set (regs3 := regupd regs2 15 (Z_to_bv 64 (MX + i0 + 2))).
destruct (mg_aligned regs3 (i0 + 1)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs3 regs2 regs1. gr. f_equal. lia. }
{ subst regs3 regs2 regs1. gr. exact H11. }
{ subst regs3 regs2 regs1. gr. f_equal. lia. }
{ subst regs3 regs2 regs1. gr. f_equal. replace (n - (i0 + 1)) with (n - i0 - 1) by lia. reflexivity. }
exists regs'. split.
-- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_038 DM_038 ltac:(subst regs2; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_lit0, unsigned_lit_small by lia; apply Z.eqb_neq; lia).
stepiv' FM_03c DM_03c (Z_to_bv 64 (MX + i0 + 2))
ltac:(subst regs2 regs1; gr; rewrite H15; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepbf FM_040 DM_040 ltac:(subst regs2 regs1; gr; rewrite H16; cbn [branch_taken];
apply negb_false_iff; unfold bv_eqb; rewrite !unsigned_lit_small by lia;
apply Z.eqb_eq; lia).
subst regs3 regs2 regs1. msteps_done.
-- split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs3 regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
*
set (regs3 := regupd regs2 15 (Z_to_bv 64 (MX + i0 + 2))).
destruct (IH regs3 (i0 + 1)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs3 regs2 regs1. gr. f_equal. lia. }
{ subst regs3 regs2 regs1. gr. exact H11. }
{ subst regs3 regs2 regs1. gr. f_equal. lia. }
{ subst regs3 regs2 regs1. gr. f_equal. lia. }
{ subst regs3 regs2 regs1. gr. exact H16. }
exists regs'. split.
-- eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_038 DM_038 ltac:(subst regs2; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_lit0, unsigned_lit_small by lia; apply Z.eqb_neq; lia).
stepiv' FM_03c DM_03c (Z_to_bv 64 (MX + i0 + 2))
ltac:(subst regs2 regs1; gr; rewrite H15; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepbt FM_040 DM_040 ltac:(subst regs2 regs1; gr; rewrite H16; cbn [branch_taken];
apply negb_true_iff; unfold bv_eqb; rewrite !unsigned_lit_small by lia;
apply Z.eqb_neq; lia).
subst regs3 regs2 regs1. msteps_done.
-- split; [exact H10'|].
intros r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
rewrite (Hfr r Hr5 Hr10 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs3 regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mg_entry : forall regs,
getr regs 10 = p -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 RES
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H11 H12. pose proof MX_range as HP.
assert (H10' : getr regs 10 = Z_to_bv 64 (MX + 0)).
{ rewrite H10. unfold MX. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
assert (Hm8 : 0 <= MX mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd (regupd (regupd regs 11 (Z_to_bv 64 c)) 13 (Z_to_bv 64 (MX mod 8)))
14 (Z_to_bv 64 (if n =? 0 then 0 else 1))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x0)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0xc)) mem rom)).
{ norm_pc.
stepiv' FM_000 DM_000 (Z_to_bv 64 c)
ltac:(gr; rewrite H11; imm_norm; unfold v_andi; rewrite unsigned_lit_small by lia;
change (bv_wrap 64 255) with (Z.ones 8); rewrite Z.land_ones by lia;
rewrite Z.mod_small by lia; reflexivity).
stepiv' FM_004 DM_004 (Z_to_bv 64 (MX mod 8))
ltac:(gr; rewrite H10'; imm_norm; unfold v_andi; rewrite unsigned_lit_small by lia;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; f_equal; f_equal; lia).
stepov FM_008 DM_008 (Z_to_bv 64 (if n =? 0 then 0 else 1))
ltac:(rewrite alu_sltu; gr; rewrite H12; unfold v_sltu, c_ltu; rewrite ltu_w by lia;
destruct (Z.eq_dec n 0) as [He0|He0];
[ replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; lia);
replace (0 <? n) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity
| replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
replace (0 <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity ]).
subst regs1. msteps_done. }
destruct (Z.eq_dec (MX mod 8) 0) as [Hal|Hal].
-
destruct (mg_aligned regs1 0) as (regs' & Hms & Hr10 & Hfr); try lia.
{ subst regs1. gr. exact H10'. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. rewrite Z.sub_0_r. exact H12. }
{ subst regs1. gr. rewrite Z.sub_0_r. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_00c DM_00c ltac:(subst regs1; gr; rewrite Hal; cbn [branch_taken]; unfold bv_eqb;
rewrite !u_lit0; reflexivity).
subst regs1. msteps_done.
+ split; [exact Hr10|].
intros r Hr5 Hr10' Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
rewrite (Hfr r Hr5 Hr10' Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs1.
rewrite !getr_other by assumption. reflexivity.
-
destruct (Z.eq_dec n 0) as [Hn0e|Hnpos].
+
destruct (mg_aligned regs1 0) as (regs' & Hms & Hr10 & Hfr); try lia.
{ subst regs1. gr. exact H10'. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. rewrite Z.sub_0_r. exact H12. }
{ subst regs1. gr. rewrite Z.sub_0_r. reflexivity. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_00c DM_00c ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_lit0, unsigned_lit_small by lia; apply Z.eqb_neq; lia).
stepbt FM_010 DM_010 ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; unfold bv_eqb;
rewrite u_lit0, unsigned_lit_small by lia; apply Z.eqb_eq; lia).
subst regs1. msteps_done.
* split; [exact Hr10|].
intros r Hr5 Hr10' Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
rewrite (Hfr r Hr5 Hr10' Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs1.
rewrite !getr_other by assumption. reflexivity.
+
set (regs2 := regupd (regupd regs1 15 (Z_to_bv 64 (MX + 1))) 16 (Z_to_bv 64 1)).
destruct (mg_prologue (Z.to_nat n) regs2 0) as (regs' & Hms & Hr10 & Hfr); try lia.
{ subst regs2 regs1. gr. exact H10'. }
{ subst regs2 regs1. gr. reflexivity. }
{ subst regs2 regs1. gr. rewrite Z.sub_0_r. exact H12. }
{ subst regs2 regs1. gr. f_equal. lia. }
{ subst regs2 regs1. gr. reflexivity. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|].
eapply msteps_trans;
[|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_00c DM_00c ltac:(subst regs1; gr; cbn [branch_taken]; unfold bv_eqb;
rewrite u_lit0, unsigned_lit_small by lia; apply Z.eqb_neq; lia).
stepbf FM_010 DM_010 ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; unfold bv_eqb;
rewrite u_lit0, unsigned_lit_small by lia; apply Z.eqb_neq; lia).
stepiv' FM_014 DM_014 (Z_to_bv 64 (MX + 1))
ltac:(subst regs1; gr; rewrite H10'; imm_norm; unfold v_addi;
rewrite unsigned_lit_small by lia; f_equal; lia).
stepiv' FM_018 DM_018 (Z_to_bv 64 1) ltac:(gr; imm_norm; unfold v_addi; rewrite u_lit0; reflexivity).
subst regs2 regs1. msteps_done.
* split; [exact Hr10|].
intros r Hr5 Hr10' Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17.
rewrite (Hfr r Hr5 Hr10' Hr12 Hr13 Hr14 Hr15 Hr16 Hr17). subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
End H.
Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem disco_memchr :
forall (p : word) (n c k : Z) (f : Z -> byte) (mem rom : word -> option byte) regs,
0 <= c < 256 -> 0 <= n -> bv_unsigned p + n + 8 < 2 ^ 64 ->
(forall i, 0 <= i < n -> rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + i)) 1 = Some [f i]) ->
(forall a : Z, tfib_D_const_HIGHS_0x8080808080808080 <= a < tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
0 <= k <= n ->
(forall i, 0 <= i < k -> bv_unsigned (f i) <> c) ->
(k < n -> bv_unsigned (f k) = c) ->
getr regs 10 = p -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_memchr) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (if k <? n then bv_unsigned p + k else 0)
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros p n c k f mem rom regs Hc Hn0 Hfit Hbytes Hrom Hk Hbef Hat H10 H11 H12.
change (Z_to_bv 64 tfib_A_musl_memchr) with (Z_to_bv 64 (tfib_A_musl_memchr + 0x0)).
destruct (mg_entry p n c k f mem rom Hc Hn0 Hfit Hbytes Hrom Hk Hbef Hat regs H10 H11 H12)
as (regs' & Hms & Hr10 & Hfr).
exists regs'. split; [exact Hms|]. split; [|exact Hfr].
rewrite Hr10. unfold RES, MX. reflexivity.
Qed.
End I.
