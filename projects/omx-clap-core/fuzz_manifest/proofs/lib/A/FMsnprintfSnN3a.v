(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE3a.v, with its module paths, addresses and numbers changed; 271 of its 499 lines of code are new or changed and 825 lines of the source are left out. *)
(* musl memchr (fuzz_manifest.asan 0x924a8 = tfib_A_musl_memchr), the NOT-FOUND walk: memchr(p, 0, n) where none
   of the n bytes at p is 0 returns NULL, and every byte it reads lies in [p, p+n).  The fetch/decode lemmas,
   the step tactics, C1, haszero_ref, rd_C1 and rd_HIGHS are those of A/AE3a.v (found case, tfib_memchr). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK0w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AE3a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section nf.
Variable s : list byte.
Variable p n : word.
Variable mem rom : word -> option byte.
Hypothesis Hnul : ~ In NUL s.
Hypothesis Hlen : Z.of_nat (length s) = bv_unsigned n.
Hypothesis Hn1 : 1 <= bv_unsigned n.
Hypothesis Hfit : bv_unsigned p + bv_unsigned n <= 2 ^ 63.
Hypothesis Hstr : forall j, (j < length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j s NUL].
Hypothesis Hrom : forall a, tfib_D_const_HIGHS_0x8080808080808080 <= a < tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1.
Lemma mnf_str_nz : forall j, (j < length s)%nat -> nth j s NUL <> NUL.
Proof. intros j Hj Hc. apply Hnul. rewrite <- Hc. apply nth_In. exact Hj. Qed.
Lemma mnf_rd : forall (a : Z) j, a = bv_unsigned p + Z.of_nat j -> (j < length s)%nat ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = Some [nth j s NUL].
Proof. intros a j -> Hj. apply Hstr. exact Hj. Qed.
Lemma mnf_word_at : forall w, bv_unsigned p <= w -> w + 8 <= bv_unsigned p + bv_unsigned n ->
exists bs, rdn tfibsegs mem (Z_to_bv 64 w) 8 = Some bs /\ length bs = 8%nat /\
(forall i, (i < 8)%nat -> nth i bs NUL = nth (Z.to_nat (w - bv_unsigned p) + i) s NUL).
Proof.
intros w Hlo Hhi. pose proof (u64_range p) as Hp.
destruct (rdn_total tfibsegs mem 8 (Z_to_bv 64 w)) as [bs Hbs].
{ intros k Hk. rewrite word_add_nat, u_Z2bv by lia.
replace (w + Z.of_nat k) with (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + k)) by lia.
rewrite Hstr by lia. discriminate. }
exists bs. split; [exact Hbs|]. split; [exact (rdn_length _ _ _ _ _ Hbs)|].
intros i Hi.
pose proof (rdn_nth tfibsegs mem 8 (Z_to_bv 64 w) bs i Hbs ltac:(lia)) as H1.
rewrite word_add_nat, u_Z2bv in H1 by lia.
pose proof (Hstr (Z.to_nat (w - bv_unsigned p) + i)%nat ltac:(lia)) as H2.
replace (bv_unsigned p + Z.of_nat (Z.to_nat (w - bv_unsigned p) + i)) with (w + Z.of_nat i) in H2 by lia.
rewrite H1 in H2. injection H2 as H3. exact H3.
Qed.
(* Tail loop 0xa0..0xb0 with S d bytes left, none of them 0; it runs out and returns NULL through 0xb4. *)
Lemma mnf_tail : forall d regs,
(S d <= length s)%nat ->
getr regs 10 = Z_to_bv 64 (bv_unsigned p + bv_unsigned n - Z.of_nat (S d)) ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 13 = Z_to_bv 64 (Z.of_nat (S d)) ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0xa0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
induction d as [|d IH]; intros regs Hd H10 H11 H13.
all: pose proof (u64_range p) as Hp; pose proof (u64_range n) as Hn.
- set (b := nth (length s - 1) s NUL).
assert (Hb : b <> NUL) by (apply mnf_str_nz; lia).
eexists. split.
+ norm_pc.
steplbu FM_0a0 DM_0a0
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; apply (mnf_rd _ (length s - 1)); lia).
stepbf FM_0a4 DM_0a4
ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 0)
ltac:(gr; rewrite H13; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (bv_unsigned p + bv_unsigned n))
ltac:(gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepbf FM_0b0 DM_0b0 ltac:(gr; vm_compute; reflexivity).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
+ split; [gr; reflexivity|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite !getr_other by assumption. reflexivity.
- set (b := nth (length s - S (S d)) s NUL).
assert (Hb : b <> NUL) by (apply mnf_str_nz; lia).
set (regs1 := regupd (regupd (regupd regs 12 (Z_to_bv 64 (bv_unsigned b)))
13 (Z_to_bv 64 (Z.of_nat (S d)))) 10 (Z_to_bv 64 (bv_unsigned p + bv_unsigned n - Z.of_nat (S d)))).
destruct (IH regs1) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. exact H11. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
steplbu FM_0a0 DM_0a0
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; apply (mnf_rd _ (length s - S (S d))); lia).
stepbf FM_0a4 DM_0a4
ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FM_0a8 DM_0a8 (Z_to_bv 64 (Z.of_nat (S d)))
ltac:(gr; rewrite H13; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepiv' FM_0ac DM_0ac (Z_to_bv 64 (bv_unsigned p + bv_unsigned n - Z.of_nat (S d)))
ltac:(gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepbt FM_0b0 DM_0b0
ltac:(gr; cbn [branch_taken]; apply negb_true_iff; apply eqb_w_false; lia).
subst regs1 b. msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption. subst regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
(* Word loop 0x74..0x94 at w with c bytes left, 8 (S k) <= c < 8 (S k) + 8: S k words without a 0 byte, then
   the tail (c mod 8 bytes) or, for c mod 8 = 0, NULL through 0x9c -> 0xb4. *)
Lemma mnf_words : forall k regs (w c : Z),
w + c = bv_unsigned p + bv_unsigned n ->
bv_unsigned p <= w ->
8 * Z.of_nat (S k) <= c < 8 * Z.of_nat (S k) + 8 ->
getr regs 10 = Z_to_bv 64 w ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 c ->
getr regs 13 = Z_to_bv 64 C1 ->
getr regs 14 = Z_to_bv 64 HZ.HIGHS ->
getr regs 15 = Z_to_bv 64 0 ->
getr regs 16 = Z_to_bv 64 7 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x74)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
induction k as [|k IH]; intros regs w c Hwc Hpw Hk H10 H11 H12 H13 H14 H15 H16.
all: pose proof (u64_range p) as Hp; pose proof (u64_range n) as Hn.
all: destruct (mnf_word_at w) as (bs & Hbs & Hlen8 & Hnth); [lia|lia|].
all: set (x := bytes_le_to_Z bs).
all: pose proof (bytes_le_to_Z_range bs Hlen8) as Hx; fold x in Hx.
all: set (v := Z_to_bv 64 x).
all: assert (Hv : bv_unsigned v = x) by (subst v; apply u_Z2bv; lia).
all: set (tw := v_and (v_or (v_sub (Z_to_bv 64 C1) v) v) (Z_to_bv 64 HZ.HIGHS)).
all: set (regs5 := regupd (regupd (regupd (regupd (regupd regs 17 v) 17 v) 5 (v_sub (Z_to_bv 64 C1) v))
17 (v_or (v_sub (Z_to_bv 64 C1) v) v)) 17 tw).
all: assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x74)) mem rom)
(mkst regs5 (Z_to_bv 64 (tfib_A_musl_memchr + 0x88)) mem rom)).
1,3: norm_pc;
(chain_step; [reflexivity | eapply step_ld with (bs := bs) (v := v);
[exact_lit FM_074 | reflexivity | exact DM_074
| rewrite H10; imm_norm; rewrite v_addi_0; exact Hbs
| rewrite Hv; reflexivity ] | step_simpl ]);
stepov FM_078 DM_078 v ltac:(rewrite alu_xor; gr; rewrite H15; apply v_xor_0);
stepov FM_07c DM_07c (v_sub (Z_to_bv 64 C1) v) ltac:(rewrite alu_sub; gr; rewrite H13; reflexivity);
stepov FM_080 DM_080 (v_or (v_sub (Z_to_bv 64 C1) v) v) ltac:(rewrite alu_or; gr; reflexivity);
stepov FM_084 DM_084 tw ltac:(rewrite alu_and; gr; rewrite H14; reflexivity);
subst regs5; msteps_done.
all: assert (Htw : bv_unsigned tw = HZ.HIGHS - HZ.Tz x) by (subst tw; rewrite haszero_ref, Hv; reflexivity).
all: assert (HTz : HZ.Tz x = 0).
1,3: apply HZ.Tz_nozero; [lia|]; intros i Hi; subst x; rewrite zb_of_bytes by lia; fold NUL;
rewrite Hnth by lia; apply byte_nz_u; apply mnf_str_nz; lia.
all: set (regs7 := regupd (regupd regs5 12 (Z_to_bv 64 (c - 8))) 10 (Z_to_bv 64 (w + 8))).
all: assert (Hmid : msteps tfibsegs (mkst regs5 (Z_to_bv 64 (tfib_A_musl_memchr + 0x88)) mem rom)
(mkst regs7 (Z_to_bv 64 (tfib_A_musl_memchr + 0x94)) mem rom)).
1,3: norm_pc;
stepbf FM_088 DM_088
ltac:(subst regs5; gr; rewrite H14; cbn [branch_taken]; unfold bv_eqb;
rewrite Htw, HTz, u_Z2bv by (unfold HZ.HIGHS; lia); rewrite Z.sub_0_r, Z.eqb_refl; reflexivity);
stepiv' FM_08c DM_08c (Z_to_bv 64 (c - 8))
ltac:(subst regs5; gr; rewrite H12; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia);
stepiv' FM_090 DM_090 (Z_to_bv 64 (w + 8))
ltac:(subst regs5; gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity);
subst regs7 regs5; msteps_done.
-
destruct (Z.eq_dec (c - 8) 0) as [Hc0|Hc0].
+ eexists. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
norm_pc.
stepbf FM_094 DM_094
ltac:(subst regs7 regs5; gr; rewrite H16; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_ge; lia).
stepiv' FM_098 DM_098 (Z_to_bv 64 (c - 8)) ltac:(subst regs7; gr; imm_norm; apply v_addi_0).
stepbt FM_09c DM_09c ltac:(subst regs7; gr; cbn [branch_taken]; apply eqb_w_true; lia).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; reflexivity).
replace (getr regs 1) with (getr regs7 1) by (subst regs7 regs5; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
* split; [gr; reflexivity|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. subst regs7 regs5.
rewrite !getr_other by assumption. reflexivity.
+ set (regs8 := regupd regs7 13 (Z_to_bv 64 (c - 8))).
destruct (mnf_tail (Z.to_nat (c - 8) - 1) regs8) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs8 regs7. gr. f_equal. lia. }
{ subst regs8 regs7 regs5. gr. exact H11. }
{ subst regs8. gr. f_equal. lia. }
exists regs'. split.
* eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs8 1) by (subst regs8 regs7 regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_094 DM_094
ltac:(subst regs7 regs5; gr; rewrite H16; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_ge; lia).
stepiv' FM_098 DM_098 (Z_to_bv 64 (c - 8)) ltac:(subst regs7; gr; imm_norm; apply v_addi_0).
stepbf FM_09c DM_09c ltac:(subst regs7; gr; cbn [branch_taken]; apply eqb_w_false; lia).
subst regs8. msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption. subst regs8 regs7 regs5.
rewrite !getr_other by assumption. reflexivity.
-
destruct (IH regs7 (w + 8) (c - 8)) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs7 regs5; gr; first [reflexivity | assumption]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|]. eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs7 1) by (subst regs7 regs5; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_094 DM_094
ltac:(subst regs7 regs5; gr; rewrite H16; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_lt; lia).
msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption. subst regs7 regs5.
rewrite !getr_other by assumption. reflexivity.
Qed.
(* 0x44 with an 8-aligned q and c >= 1 bytes left (a4 = 1): byte check at q, then the word loop (c >= 8) or the
   tail (c < 8). *)
Lemma mnf_aligned : forall regs (q c : Z),
bv_unsigned p <= q -> q mod 8 = 0 -> q + c = bv_unsigned p + bv_unsigned n -> 1 <= c ->
getr regs 10 = Z_to_bv 64 q ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 c ->
getr regs 14 = Z_to_bv 64 1 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x44)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs q c Hpq Hq8 Hqc Hc1 H10 H11 H12 H14.
pose proof (u64_range p) as Hp. pose proof (u64_range n) as Hn.
set (b := nth (Z.to_nat (q - bv_unsigned p)) s NUL).
assert (Hb : b <> NUL) by (apply mnf_str_nz; lia).
set (regs1 := regupd regs 13 (Z_to_bv 64 (bv_unsigned b))).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x44)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0x50)) mem rom)).
{ norm_pc.
stepbf FM_044 DM_044 ltac:(gr; rewrite H14; vm_compute; reflexivity).
steplbu FM_048 DM_048
ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; apply (mnf_rd _ (Z.to_nat (q - bv_unsigned p))); lia).
stepbf FM_04c DM_04c
ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
subst regs1 b. msteps_done. }
destruct (Z_lt_le_dec c 8) as [Hc8|Hc8].
-
set (regs2 := regupd (regupd regs1 13 (Z_to_bv 64 8)) 13 (Z_to_bv 64 c)).
destruct (mnf_tail (Z.to_nat c - 1) regs2) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs2 regs1. gr. rewrite H10. f_equal. lia. }
{ subst regs2 regs1. gr. exact H11. }
{ subst regs2. gr. f_equal. lia. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepiv' FM_050 DM_050 (Z_to_bv 64 8) ltac:(gr; reflexivity).
stepbt FM_054 DM_054
ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_lt; lia).
stepiv' FM_098 DM_098 (Z_to_bv 64 c) ltac:(subst regs1; gr; rewrite H12; imm_norm; apply v_addi_0).
stepbf FM_09c DM_09c ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; apply eqb_w_false; lia).
subst regs2 regs1. msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption. subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
-
destruct (rd_C1 s p n mem rom Hrom) as (bs1 & Hbs1 & Hv1).
destruct (rd_HIGHS s p n mem rom Hrom) as (bs2 & Hbs2 & Hv2).
set (regs2 := regupd (regupd (regupd (regupd (regupd (regupd (regupd regs1
13 (Z_to_bv 64 8))
13 (Z_to_bv 64 tfib_memchr_aui1)) 13 (Z_to_bv 64 C1))
14 (Z_to_bv 64 tfib_memchr_aui2)) 14 (Z_to_bv 64 HZ.HIGHS))
15 (Z_to_bv 64 (C1 + 1))) 15 (Z_to_bv 64 0)).
set (regs3 := regupd regs2 16 (Z_to_bv 64 7)).
assert (Hcd : c = 8 * (c / 8) + c mod 8) by (apply Z.div_mod; lia).
assert (Hcm : 0 <= c mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (mnf_words (Z.to_nat (c / 8) - 1) regs3 q c) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs3 regs2 regs1; gr; first [reflexivity | assumption]).
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepiv' FM_050 DM_050 (Z_to_bv 64 8) ltac:(gr; reflexivity).
stepbf FM_054 DM_054
ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; rewrite ltu_w by lia; apply Z.ltb_ge; lia).
stepiv' FM_058 DM_058 (Z_to_bv 64 tfib_memchr_aui1) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs1) (v := Z_to_bv 64 C1);
[ exact_lit FM_05c | reflexivity | exact DM_05c
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 tfib_D_const_ONES_0x0101010101010100) by bveq end; exact Hbs1
| rewrite Hv1; reflexivity ] | step_simpl ].
stepiv' FM_060 DM_060 (Z_to_bv 64 tfib_memchr_aui2) ltac:(bveq).
chain_step; [reflexivity | eapply step_ld with (bs := bs2) (v := Z_to_bv 64 HZ.HIGHS);
[ exact_lit FM_064 | reflexivity | exact DM_064
| gr; match goal with |- rdn _ _ ?a _ = _ => replace a with (Z_to_bv 64 tfib_D_const_HIGHS_0x8080808080808080) by bveq end; exact Hbs2
| rewrite Hv2; reflexivity ] | step_simpl ].
stepiv' FM_068 DM_068 (Z_to_bv 64 (C1 + 1)) ltac:(gr; reflexivity).
stepiv' FM_06c DM_06c (Z_to_bv 64 0)
ltac:(subst regs1; gr; rewrite H11; unfold v_mul; rewrite u_lit0, Z.mul_0_l; reflexivity).
stepiv' FM_070 DM_070 (Z_to_bv 64 7) ltac:(gr; reflexivity).
subst regs3 regs2 regs1. msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption. subst regs3 regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
Qed.
(* Prologue loop 0x1c..0x40 at p + j (p not 8-aligned), n - j >= 1 bytes left, m steps to the 8-alignment: it
   stops at the alignment (then 0x44) or when the bytes run out (then 0x44 with a4 = 0 -> NULL). *)
Lemma mnf_prologue : forall m regs (j : nat),
bv_unsigned p mod 8 <> 0 ->
(0 < m)%nat -> Z.of_nat j + Z.of_nat m = 8 - bv_unsigned p mod 8 ->
(j < length s)%nat ->
getr regs 10 = Z_to_bv 64 (bv_unsigned p + Z.of_nat j) ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = Z_to_bv 64 (bv_unsigned n - Z.of_nat j) ->
getr regs 15 = Z_to_bv 64 (bv_unsigned p + Z.of_nat j + 1) ->
getr regs 16 = Z_to_bv 64 1 ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x1c)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
induction m as [|m IH]; intros regs j HA Hm Hjm Hj H10 H11 H12 H15 H16; [lia|].
pose proof (u64_range p) as Hp. pose proof (u64_range n) as Hn.
assert (HA8 : 0 <= bv_unsigned p mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (HP8 : bv_unsigned p = 8 * (bv_unsigned p / 8) + bv_unsigned p mod 8) by (apply Z.div_mod; lia).
set (b := nth j s NUL).
assert (Hb : b <> NUL) by (apply mnf_str_nz; exact Hj).
set (regs1 := regupd (regupd regs 14 (Z_to_bv 64 (bv_unsigned b))) 13 (Z_to_bv 64 (bv_unsigned n - Z.of_nat j))).
set (a4 := if 0 <? bv_unsigned n - Z.of_nat j - 1 then Z_to_bv 64 1 else Z_to_bv 64 0).
set (regs2 := regupd (regupd (regupd (regupd regs1
10 (Z_to_bv 64 (bv_unsigned p + Z.of_nat j + 1)))
12 (Z_to_bv 64 (bv_unsigned n - Z.of_nat j - 1)))
17 (Z_to_bv 64 ((bv_unsigned p + Z.of_nat j + 1) mod 8)))
14 a4).
assert (Hmid : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x1c)) mem rom)
(mkst regs2 (Z_to_bv 64 (tfib_A_musl_memchr + 0x38)) mem rom)).
{ norm_pc.
steplbu FM_01c DM_01c ltac:(gr; rewrite H10; imm_norm; rewrite v_addi_0; apply (mnf_rd _ j); lia).
stepiv' FM_020 DM_020 (Z_to_bv 64 (bv_unsigned n - Z.of_nat j)) ltac:(gr; rewrite H12; imm_norm; apply v_addi_0).
stepbf FM_024 DM_024
ltac:(gr; rewrite H11; cbn [branch_taken]; unfold bv_eqb;
rewrite u_zext8, u_lit0; apply Z.eqb_neq; apply byte_nz_u; exact Hb).
stepiv' FM_028 DM_028 (Z_to_bv 64 (bv_unsigned p + Z.of_nat j + 1))
ltac:(gr; rewrite H10; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; reflexivity).
stepiv' FM_02c DM_02c (Z_to_bv 64 (bv_unsigned n - Z.of_nat j - 1))
ltac:(gr; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepiv' FM_030 DM_030 (Z_to_bv 64 ((bv_unsigned p + Z.of_nat j + 1) mod 8))
ltac:(gr; rewrite H15; imm_norm; unfold v_andi; rewrite u_Z2bv by lia;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
stepov FM_034 DM_034 a4
ltac:(rewrite alu_sltu; gr; unfold v_sltu, c_ltu; rewrite ltu_w by lia; subst a4; reflexivity).
subst regs2 regs1 a4 b. msteps_done. }
assert (Hm8 : 0 <= (bv_unsigned p + Z.of_nat j + 1) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
destruct (Z.eq_dec (bv_unsigned n - Z.of_nat j - 1) 0) as [Hz|Hz].
- (* p + j is the last byte: NULL whichever way 0x38 goes *)
assert (Ha4 : a4 = Z_to_bv 64 0)
by (subst a4; destruct (Z.ltb_spec 0 (bv_unsigned n - Z.of_nat j - 1)); [lia|reflexivity]).
destruct (Z.eq_dec ((bv_unsigned p + Z.of_nat j + 1) mod 8) 0) as [Hal|Hal].
+ eexists. split.
* eapply msteps_trans; [exact Hmid|]. norm_pc.
stepbt FM_038 DM_038 ltac:(subst regs2; gr; rewrite Hal; vm_compute; reflexivity).
stepbt FM_044 DM_044 ltac:(subst regs2; gr; rewrite Ha4; vm_compute; reflexivity).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; reflexivity).
replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
* split; [gr; reflexivity|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
+ eexists. split.
* eapply msteps_trans; [exact Hmid|]. norm_pc.
stepbf FM_038 DM_038 ltac:(subst regs2; gr; cbn [branch_taken]; apply eqb_w_false; lia).
stepiv' FM_03c DM_03c (Z_to_bv 64 (bv_unsigned p + Z.of_nat j + 2))
ltac:(subst regs2 regs1; gr; rewrite H15; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepbf FM_040 DM_040
ltac:(subst regs2 regs1; gr; rewrite H16; cbn [branch_taken]; apply negb_false_iff; apply eqb_w_true; lia).
stepbt FM_044 DM_044 ltac:(subst regs2; gr; rewrite Ha4; vm_compute; reflexivity).
stepiv' FM_0b4 DM_0b4 (Z_to_bv 64 0) ltac:(gr; reflexivity).
replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity).
stepret FM_0b8 DM_0b8. msteps_done.
* split; [gr; reflexivity|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. subst regs2 regs1.
rewrite !getr_other by assumption. reflexivity.
-
assert (Ha4 : a4 = Z_to_bv 64 1)
by (subst a4; destruct (Z.ltb_spec 0 (bv_unsigned n - Z.of_nat j - 1)); [reflexivity|lia]).
destruct (Z.eq_dec ((bv_unsigned p + Z.of_nat j + 1) mod 8) 0) as [Hal|Hal].
+
destruct (mnf_aligned regs2 (bv_unsigned p + Z.of_nat j + 1) (bv_unsigned n - Z.of_nat j - 1))
as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs2 regs1; gr; first [reflexivity | assumption]).
exists regs'. split.
* eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_038 DM_038 ltac:(subst regs2; gr; rewrite Hal; vm_compute; reflexivity).
msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption.
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
+
assert (Hm' : (0 < m)%nat).
{ destruct m; [|lia]. exfalso. apply Hal.
replace (bv_unsigned p + Z.of_nat j + 1) with (8 * (bv_unsigned p / 8 + 1)) by lia.
rewrite Z.mul_comm. apply Z_mod_mult. }
set (regs3 := regupd regs2 15 (Z_to_bv 64 (bv_unsigned p + Z.of_nat (S j) + 1))).
destruct (IH regs3 (S j)) as (regs' & Hms & H10' & Hfr); try lia.
all: try (subst regs3 regs2 regs1; gr; first [reflexivity | assumption | f_equal; lia]).
exists regs'. split.
* eapply msteps_trans; [exact Hmid|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs3 1) by (subst regs3 regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_038 DM_038 ltac:(subst regs2; gr; cbn [branch_taken]; apply eqb_w_false; lia).
stepiv' FM_03c DM_03c (Z_to_bv 64 (bv_unsigned p + Z.of_nat (S j) + 1))
ltac:(subst regs2 regs1; gr; rewrite H15; imm_norm; unfold v_addi; rewrite u_Z2bv by lia; f_equal; lia).
stepbt FM_040 DM_040
ltac:(subst regs2 regs1; gr; rewrite H16; cbn [branch_taken]; apply negb_true_iff; apply eqb_w_false; lia).
subst regs3 regs2 regs1. msteps_done.
* split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption.
subst regs3 regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma mnf_sec : forall regs,
getr regs 10 = p ->
getr regs 11 = Z_to_bv 64 0 ->
getr regs 12 = n ->
exists regs',
msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x0)) mem rom)
(mkst regs' (v_jalr (getr regs 1) 0) mem rom)
/\ getr regs' 10 = Z_to_bv 64 0
/\ (forall r : reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros regs H10 H11 H12.
pose proof (u64_range p) as Hp. pose proof (u64_range n) as Hn.
assert (HA8 : 0 <= bv_unsigned p mod 8 < 8) by (apply Z.mod_pos_bound; lia).
set (regs1 := regupd (regupd (regupd regs 11 (Z_to_bv 64 0)) 13 (Z_to_bv 64 (bv_unsigned p mod 8))) 14 (Z_to_bv 64 1)).
assert (Hpre : msteps tfibsegs (mkst regs (Z_to_bv 64 (tfib_A_musl_memchr + 0x0)) mem rom)
(mkst regs1 (Z_to_bv 64 (tfib_A_musl_memchr + 0xc)) mem rom)).
{ norm_pc.
stepiv' FM_000 DM_000 (Z_to_bv 64 0) ltac:(gr; rewrite H11; bveq).
stepiv' FM_004 DM_004 (Z_to_bv 64 (bv_unsigned p mod 8))
ltac:(gr; rewrite H10; imm_norm; unfold v_andi;
change (bv_wrap 64 7) with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
stepov FM_008 DM_008 (Z_to_bv 64 1)
ltac:(rewrite alu_sltu; gr; rewrite H12; unfold v_sltu, c_ltu, bv_ltu; rewrite u_lit0;
replace (0 <? bv_unsigned n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
subst regs1. msteps_done. }
destruct (Z.eq_dec (bv_unsigned p mod 8) 0) as [HA|HA].
-
destruct (mnf_aligned regs1 (bv_unsigned p) (bv_unsigned n)) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs1. gr. rewrite H10. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs1. gr. reflexivity. }
{ subst regs1. gr. rewrite H12. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs1 1) by (subst regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbt FM_00c DM_00c ltac:(subst regs1; gr; rewrite HA; vm_compute; reflexivity).
msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption.
subst regs1. rewrite !getr_other by assumption. reflexivity.
-
set (regs2 := regupd (regupd regs1 15 (Z_to_bv 64 (bv_unsigned p + Z.of_nat 0 + 1))) 16 (Z_to_bv 64 1)).
destruct (mnf_prologue (Z.to_nat (8 - bv_unsigned p mod 8)) regs2 0) as (regs' & Hms & H10' & Hfr); try lia.
{ subst regs2 regs1. gr. rewrite H10, Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs2 regs1. gr. reflexivity. }
{ subst regs2 regs1. gr. rewrite H12, Z.sub_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
{ subst regs2 regs1. gr. reflexivity. }
{ subst regs2 regs1. gr. reflexivity. }
exists regs'. split.
+ eapply msteps_trans; [exact Hpre|].
eapply msteps_trans; [|replace (getr regs 1) with (getr regs2 1) by (subst regs2 regs1; gr; reflexivity); exact Hms].
norm_pc.
stepbf FM_00c DM_00c ltac:(subst regs1; gr; cbn [branch_taken]; apply eqb_w_false; lia).
stepbf FM_010 DM_010
ltac:(subst regs1; gr; rewrite H12; cbn [branch_taken]; unfold bv_eqb; rewrite u_lit0; apply Z.eqb_neq; lia).
stepiv' FM_014 DM_014 (Z_to_bv 64 (bv_unsigned p + Z.of_nat 0 + 1))
ltac:(subst regs1; gr; rewrite H10; imm_norm; unfold v_addi; f_equal; lia).
stepiv' FM_018 DM_018 (Z_to_bv 64 1) ltac:(gr; reflexivity).
subst regs2 regs1. msteps_done.
+ split; [exact H10'|].
intros r Hr5 Hr10 Hr11 Hr12 Hr13 Hr14 Hr15 Hr16 Hr17. rewrite (Hfr r) by assumption.
subst regs2 regs1. rewrite !getr_other by assumption. reflexivity.
Qed.
End nf.
Theorem tfib_memchrN :
forall (s : list byte) (p n : word) (mem rom : word -> option byte) (regs : bvmap 5 word),
~ In NUL s ->
Z.of_nat (length s) = bv_unsigned n ->
1 <= bv_unsigned n ->
bv_unsigned p + bv_unsigned n <= 2 ^ 63 ->
(forall j, (j < length s)%nat -> rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j s NUL]) ->
(forall a, tfib_D_const_HIGHS_0x8080808080808080 <= a < tfib_D_const_ONES_0x0101010101010100 + 8 ->
   rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
getr regs 10 = p -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = n ->
exists regs' : bvmap 5 word,
  msteps tfibsegs (mkst regs (Z_to_bv 64 tfib_A_musl_memchr) mem rom) (mkst regs' (v_jalr (getr regs 1) 0) mem rom) /\
  getr regs' 10 = Z_to_bv 64 0 /\
  (forall r : Prelude.reg, r <> 5%bv -> r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv ->
     r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv -> getr regs' r = getr regs r).
Proof.
intros. change (Z_to_bv 64 tfib_A_musl_memchr) with (Z_to_bv 64 (tfib_A_musl_memchr + 0x0)).
eapply mnf_sec; eassumption.
Qed.
End g.
