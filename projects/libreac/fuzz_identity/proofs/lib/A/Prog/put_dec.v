(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:267-269, 285-290; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACac.v:54-58;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACb8.v:237-239; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChf.v:266-269, 276-279;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACjs.v:119-123, for libreac/fuzz_identity's ASan build (lib/A). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI16 YI00 YO0a YO0c YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
IdentSyms IdentList IdentAddr IdentPa IdentPaLib IdentBase IdentFrame IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC1g YC1h YC45 YC4b YC81 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import put_dec_pad put_dec_rev.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import put_dec_src put_dec_kept put_dec_epi.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require put_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require put_dec.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.IdentSpec(DEC, dg, dec_digits).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec(
  ds_lsb, q_word, digit_word, a0_word, ltu9_word, ds_lsb_length, dec_ds, rev_ds_lsb, div10_magic).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Definition PUT_DEC_STK : Z := 128 + ESTACK.
Definition EV_PUT_DEC : Z := 0.
Definition pd_qsv (n : nat) : sv :=
SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 14757395259826634752)) (SLit 35).
Definition pd_dsv (n : nat) : sv :=
SAlu ALU_OR (SAluw ALU_SUB (SOff n 0) (SMd M_MUL (pd_qsv n) (SLit 10))) (SLit 48).
Definition pd_denot_atom : forall (E : env) n a, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
sv_denot E (SOff n 0) = Z_to_bv 64 a.
Proof.
intros E n a H Ha. cbn [sv_denot]. rewrite H, (unsigned_lit_small a) by lia. f_equal. lia.
Qed.
Lemma pd_denot_add : forall (E : env) n1 n2 a b, ew E n1 = Z_to_bv 64 a -> ew E n2 = Z_to_bv 64 b ->
0 <= a -> 0 <= b -> a + b < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff n1 0) (SOff n2 0)) = Z_to_bv 64 (a + b).
Proof.
intros E n1 n2 a b H1 H2 Ha Hb Hab. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H1, H2.
rewrite (unsigned_lit_small a) by lia. rewrite (unsigned_lit_small b) by lia.
rewrite !Z.add_0_r. rewrite (zcanon_id a) by (unfold M64; lia).
rewrite (zcanon_id b) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.
Definition PD_DCLOB : list (bv 5) := [10; 11; 15; 16; 17; 22]%bv.
Definition PD_DPIN : list (bv 5) := [12; 13; 14]%bv.
Definition PD_DKEPT : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pd_dclob_kept : forall r : bv 5, reg_in r PD_DCLOB = false -> r = 0%bv \/ In r PD_DKEPT \/ In r PD_DPIN.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin];
[first [left; reflexivity | vm_compute in Hr; discriminate | right; left; cbv; tauto | right; right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition pd_dsr : list sv :=
sr_set (sr_set (sr_set sr_atoms
 (12%bv : bv 5) (SLit 10))
 (13%bv : bv 5) (SLit 14757395259826634752))
 (14%bv : bv 5) (SLit 9).
Definition pd_dmem : smem := [YP09.mkRegion (Some 32%nat) 0 1 0 1 []].
Definition pd_dfacts : facts :=
mkFacts [(11%nat, mkAF 0 9 0); (26%nat, mkAF 4096 140737479966720 0);
         (32%nat, mkAF 4096 140737479966720 0); (22%nat, mkAF 0 18446744073709551615 0);
         (23%nat, mkAF 2147450880 2147450880 0)] []
        [(SAlu ALU_ADD (SOff 26 0) (SOff 11 0), SOff 32 0)].
Definition pd_dsh : list shent := [mkSHE 32%nat 0 1].
Lemma pd_sll32 : forall a : word, alu64 ALU_SLL a (Z_to_bv 64 32) = Z_to_bv 64 (Z.shiftl (bv_unsigned a) 32).
Proof.
intros a. apply bv_eq. rewrite alu64_sll.
replace (bv_unsigned (Z_to_bv 64 32) mod 64) with 32 by (vm_compute; reflexivity).
rewrite Z_to_bv_unsigned. unfold sll64, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). reflexivity.
Qed.
Lemma pd_srl35 : forall a : word, alu64 ALU_SRL a (Z_to_bv 64 35) = Z_to_bv 64 (Z.shiftr (bv_unsigned a) 35).
Proof.
intros a. apply bv_eq. rewrite alu64_srl.
replace (bv_unsigned (Z_to_bv 64 35) mod 64) with 35 by (vm_compute; reflexivity).
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small.
split; [apply Z.div_pos; lia |].
apply Z.le_lt_trans with (m := bv_unsigned a); [apply Z.div_le_upper_bound; lia | lia].
Qed.
Lemma pd_mulhu : forall a b : word, mul_div M_MULHU a b = Z_to_bv 64 (Z.shiftr (bv_unsigned a * bv_unsigned b) 64).
Proof.
intros a b. apply bv_eq. rewrite mulhu_unsigned.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 b) as Hb.
change (bv_modulus 64) with (2 ^ 64) in Ha, Hb.
rewrite Z.shiftr_div_pow2 by lia. symmetry. apply Z.mod_small.
split; [apply Z.div_pos; [apply Z.mul_nonneg_nonneg; lia | lia] |].
apply Z.div_lt_upper_bound; [lia |]. nia.
Qed.
Lemma pd_q_sv : forall (E : env) n R x, ew E n = Z_to_bv 64 R -> 0 <= R < 2 ^ 64 -> R mod 2 ^ 32 = x ->
sv_denot E (pd_qsv n) = Z_to_bv 64 (x / 10).
Proof.
intros E n R x H HR Hx. cbn [sv_denot pd_qsv]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite pd_sll32, pd_mulhu, pd_srl35.
rewrite (unsigned_lit_small 14757395259826634752) by lia.
rewrite (q_word (Z_to_bv 64 R)).
rewrite (unsigned_lit_small R) by lia. rewrite Hx. reflexivity.
Qed.
Lemma pd_lor48 : forall r, 0 <= r < 10 -> Z.lor r 48 = 48 + r.
Proof.
intros r Hr.
assert (C : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) by lia.
repeat (destruct C as [-> | C]; [vm_compute; reflexivity |]). subst r. vm_compute. reflexivity.
Qed.
Lemma pd_digit_val : forall (E : env) n R x, ew E n = Z_to_bv 64 R -> 0 <= R < 2 ^ 64 -> R mod 2 ^ 32 = x ->
bv_unsigned (sv_denot E (pd_dsv n)) mod 256 = 48 + x mod 10.
Proof.
intros E n R x H HR Hxm.
assert (Hx : 0 <= x < 2 ^ 32) by (rewrite <- Hxm; apply Z.mod_pos_bound; lia).
pose proof (pd_q_sv E n R x H HR Hxm) as Hq.
assert (Hd10 : 0 <= x / 10 < 2 ^ 32) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Hr10 : 0 <= x mod 10 < 10) by (apply Z.mod_pos_bound; lia).
assert (Hxr : x - x / 10 * 10 = x mod 10) by (pose proof (Z.div_mod x 10 ltac:(lia)); lia).
cbn [sv_denot pd_dsv]. rewrite Hq, H, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite alu64_or, subw_rr_unsigned, mul64_unsigned.
rewrite (unsigned_lit_small R) by lia. rewrite (unsigned_lit_small (x / 10)) by lia.
rewrite (unsigned_lit_small 10) by lia. rewrite (unsigned_lit_small 48) by lia.
unfold mul64. rewrite (Z.mod_small (x / 10 * 10) (2 ^ 64)) by lia.
unfold subw, sx32.
replace ((R - x / 10 * 10) mod 2 ^ 32) with (x mod 10)
by (rewrite <- Zminus_mod_idemp_l, Hxm, Hxr; symmetry; apply Z.mod_small; lia).
replace (x mod 10 <? 2 ^ 31) with true by (symmetry; apply Z.ltb_lt; lia).
rewrite pd_lor48 by lia. apply Z.mod_small. lia.
Qed.
Lemma pd_dg_val : forall r, 0 <= r < 10 -> bv_unsigned (dg r) = 48 + r.
Proof.
intros r Hr. unfold dg. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia.
Qed.
Ltac pd_after_step HSx KEPT2 PRES2 HVAL2 F11b F22b F32b E11v E22v E32v V32v KEPTv lo hi iv Rv xv tiv HRb Hxmb :=
lazymatch goal with |- SRr ?sg ?Wv (mkCfg ?ms2 _) _ =>
lazymatch type of HSx with st_ok_pi _ _ ?Ev ?ssx _ =>
assert (F11b : ew Ev 11 = Z_to_bv 64 iv) by (rewrite ?ew_ewset_other by lia; exact E11v);
assert (F22b : ew Ev 22 = Z_to_bv 64 Rv) by (rewrite ?ew_ewset_other by lia; exact E22v);
assert (F32b : ew Ev 32 = Z_to_bv 64 tiv) by (rewrite ?ew_ewset_other by lia; exact E32v);
lazymatch type of KEPTv with
| forall a, _ -> _ -> aview _ ?Hh ?m1 a = aview _ _ ?m0 a =>
assert (KEPT2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
aview sg Hh (ms_mem ms2) a = aview sg Hh m0 a);
[ intros a Ha Hna; rewrite <- (KEPTv a Ha Hna);
  eapply (kept_of_frame _ _ Hh m1 (ms_mem ms2) (fun z => lo <= z < hi));
  [ lazymatch goal with Hfx : frame_of _ _ _ _ |- _ => exact Hfx end | | exact Ha | exact Hna ];
  intros bb wlo whi aa Hin Hrr;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end;
  cbn [In] in Hin; destruct Hin as [Heq | []]; injection Heq as <- <- <-;
  cbn [base_val] in Hrr; rewrite (V32v _ F32b) in Hrr; lia
| ];
assert (PRES2 : forall a, apresent Hh m0 a -> apresent Hh (ms_mem ms2) a)
by (intros a Ha; eapply apresent_grows; [eassumption |]; eapply apresent_grows; [eassumption |]; exact Ha)
end;
let HRO := fresh "HRO" in
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H Wv) ms2) 0%nat _ HSx eq_refl) as HRO;
cbn [ms_mem restrict] in HRO;
pose proof (field_of_region_any Ev (mrestrict (w_H Wv) (ms_mem ms2)) 32%nat tiv _ 0 1 0 1 0 1%N (pd_dsv 22)
  HRO (V32v Ev F32b) ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HVAL2;
replace (2 ^ (8 * Z.of_N 1)) with 256 in HVAL2 by (vm_compute; reflexivity);
change (N.to_nat 1) with 1%nat in HVAL2;
rewrite (pd_digit_val Ev 22 Rv xv F22b HRb Hxmb) in HVAL2;
rewrite Z.add_0_r in HVAL2
end end.
Ltac pd_regs_kept HK HSx HAEv KEPTL :=
lazymatch type of HSx with st_ok_pi _ _ ?Ev _ _ =>
lazymatch type of HAEv with env_agree 32 (Ereg ?regs0 ?extra) _ =>
let HAE2 := fresh "HAE2" in
assert (HAE2 : env_agree 32 (Ereg regs0 extra) Ev)
by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAEv nn Hnn)
           | cbn [ewset ed]; exact (proj2 HAEv)]);
pose proof (regs_kept_of_st_ok_pi Ev _ _ regs0 extra KEPTL HSx HAE2 ltac:(vm_compute; reflexivity)) as HK;
cbn [ms_regs restrict] in HK
end end.
Definition PD_RCLOB : list (bv 5) := [10; 11; 12; 13; 15; 16; 17]%bv.
Definition PD_RKEPT : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 14; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma pd_rclob_kept : forall r : bv 5, reg_in r PD_RCLOB = false -> r = 0%bv \/ In r PD_RKEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Definition pd_rsr : list sv := sr_set sr_atoms (10%bv : bv 5) (SOff 13 0).
Definition pd_rmem : smem :=
[YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))];
 YP09.mkRegion (Some 14%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
 YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
 YP09.mkRegion (Some 32%nat) 0 1 0 1 []].
Definition pd_rfacts : facts :=
mkFacts [(13%nat, mkAF 4096 140737479966720 0); (19%nat, mkAF 4096 140737488355320 3);
         (32%nat, mkAF 4096 140737488355327 0); (33%nat, mkAF 0 140737488355328 0);
         (20%nat, mkAF 0 140737488355327 0); (34%nat, mkAF 0 255 0);
         (14%nat, mkAF 2147450880 19739720941568 0);
         (23%nat, mkAF 2147450880 2147450880 0)] []
        [(SAlu ALU_ADD (SOff 20 0) (SOff 33 0), SOff 32 0)].
Definition pd_rsh : list shent := [mkSHE 13%nat 0 1; mkSHE 19%nat 0 8; mkSHE 32%nat 0 1].
Lemma pd_vm1 : forall segs H (m : word -> option byte) a v,
aview segs H m a = Some v -> 0 <= v < 256 -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros segs H m a v Hv Hr kk Hk.
assert (kk = 0)%nat by lia. subst kk. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [bb|] eqn:Hb; cbn in Hv; [| discriminate].
injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte, bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, <- Hv, !Z.mod_mod by lia.
pose proof (bv_unsigned_in_range 8 bb) as Hbr. change (bv_modulus 8) with 256 in Hbr.
rewrite (Z.mod_small (bv_unsigned bb) 256) by lia. reflexivity.
Qed.
Lemma pd_denot_off : forall (E : env) n a z, ew E n = Z_to_bv 64 a -> 0 <= a < 2 ^ 64 ->
sv_denot E (SOff n z) = Z_to_bv 64 (a + z).
Proof. intros E n a z H Ha. cbn [sv_denot]. rewrite H, (unsigned_lit_small a) by lia. reflexivity. Qed.
Lemma pd_bv_eqm : forall z1 z2, z1 mod 2 ^ 64 = z2 mod 2 ^ 64 -> Z_to_bv 64 z1 = Z_to_bv 64 z2.
Proof.
intros z1 z2 H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). exact H.
Qed.
Lemma pd_ltu9 : forall R x, R mod 2 ^ 32 = x -> (R < 2 ^ 32 \/ 10 <= x) -> 0 <= R ->
(9 <? R) = (10 <=? x).
Proof.
intros R x Hm Hd HR.
assert (Hx : 0 <= x < 2 ^ 32) by (rewrite <- Hm; apply Z.mod_pos_bound; lia).
assert (Hkey : (9 < R) <-> (10 <= x)).
{ destruct Hd as [Hlt | Hge].
- rewrite (Z.mod_small R (2 ^ 32)) in Hm by lia. subst x. split; lia.
- assert (Hle : x <= R) by (rewrite <- Hm; apply Z.mod_le; lia). split; intros _; lia. }
destruct (Z.ltb_spec 9 R) as [H1 | H1]; destruct (Z.leb_spec 10 x) as [H2 | H2];
[reflexivity | exfalso; pose proof (proj1 Hkey H1); lia | exfalso; pose proof (proj2 Hkey H2); lia | reflexivity].
Qed.
Lemma pd_shadow_out {rc : YM05.RunCeil} : forall T n xx, in_app T n -> T <= xx < T + n ->
0 <= shadow_of_addr SHADOW_OFF xx < 2 ^ 64 /\ ~ (T <= shadow_of_addr SHADOW_OFF xx < T + n).
Proof.
intros T n xx Happ Hx. pose proof alloc_ceiling_lt as Hac.
assert (H8 : 8 * (xx / 8) <= xx) by (apply Z.mul_div_le; lia).
assert (H8b : 0 <= xx / 8) by (apply Z.div_pos; unfold in_app in Happ; lia).
assert (H8c : xx / 8 <= xx) by (apply Z.div_le_upper_bound; lia).
unfold shadow_of_addr, SHADOW_OFF, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
Lemma pd_zs_byte : forall (rd : Z -> option Z) lo len x, zero_shadow rd SHADOW_OFF lo len ->
lo mod 8 = 0 -> len mod 8 = 0 -> lo <= x < lo + len -> rd (shadow_of_addr SHADOW_OFF x) = Some 0.
Proof.
intros rd lo len x Hz Hlo Hlen Hx. unfold zero_shadow in Hz.
pose proof (Z.div_mod lo 8 ltac:(lia)) as D1. rewrite Hlo, Z.add_0_r in D1.
pose proof (Z.div_mod len 8 ltac:(lia)) as D2. rewrite Hlen, Z.add_0_r in D2.
assert (Hq1 : lo / 8 <= x / 8) by (apply Z.div_le_lower_bound; lia).
assert (Hq2 : x / 8 < lo / 8 + len / 8) by (apply Z.div_lt_upper_bound; lia).
replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF lo + (x / 8 - lo / 8))
by (unfold shadow_of_addr; lia).
apply Hz. lia.
Qed.
Lemma pd_mod4096_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D.
replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma pd_awr_mono : forall STK sp0 FP bl0 blc ly own f a,
awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc ly (f :: own) a.
Proof.
intros STK sp0 FP bl0 blc ly own f a [H | [H | [H | (cid & ps & Hin & Hr)]]];
[left | right; left | right; right; left | right; right; right]; try exact H.
exists cid, ps. split; [right; exact Hin | exact Hr].
Qed.
Lemma pd_shadow_lt_ceil {rc : YM05.RunCeil} : forall y, 0 <= y -> y <= alloc_ceiling ->
0 <= shadow_of_addr SHADOW_OFF y < alloc_ceiling.
Proof.
intros y Hy1 Hy2. pose proof asan_consts as (Hc & _).
assert (H1 : 8 * (y / 8) <= y) by (apply Z.mul_div_le; lia).
assert (H2 : 0 <= y / 8) by (apply Z.div_pos; lia).
unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.
Lemma pd_sv_val : forall (w : word), bv_unsigned (Z_to_bv 64 (bv_unsigned w + 0)) mod 2 ^ (8 * Z.of_N 8) = bv_unsigned w.
Proof.
intros w. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64).
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. lia.
Qed.
Lemma pd_nth_tl : forall (l : list byte) (j : nat), nth j (tl l) (Z_to_bv 8 0) = nth (S j) l (Z_to_bv 8 0).
Proof. intros l j. destruct l as [|c l']; [destruct j; reflexivity | reflexivity]. Qed.
Lemma pd_length_tl : forall (l : list byte), (length (tl l) = length l - 1)%nat.
Proof. intros l. destruct l as [|c l']; cbn; lia. Qed.
Lemma pd_u12 : forall (E : env) (z : Z), ew E 12 = Z_to_bv 64 z -> U E (SOff 12 1) = (z + 1) mod 2 ^ 64.
Proof.
intros E z H. rewrite U_SOff, H, unsigned_lit. unfold zcanon, M64.
rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Ltac pd_band_app :=
repeat match goal with H : forall _ : _, _ |- _ => clear H end;
try unfold shadow_of_addr in *;
try (match goal with
| |- context [?z / 8] =>
    assert (8 * (z / 8) <= z) by (apply Z.mul_div_le; lia);
    assert (0 <= z / 8) by (apply Z.div_pos; lia)
end);
try unfold SHADOW_OFF in *; try unfold in_app in *; try unfold app_addr in *;
try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *; lia.
Ltac pd_rawr HWRpv HWRdv U19v U32v :=
unfold pd_rmem;
lazymatch goal with |- awr_ok ?Ev _ _ _ _ _ _ _ _ =>
apply (awr_ok_cons_ro Ev); [cbn; lia |];
apply (awr_ok_cons_ro Ev); [cbn; lia |];
eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 19%nat _);
[reflexivity | rewrite ?ew_ewset_other by lia; exact U19v
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWRpv; lia |];
eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 32%nat _);
[reflexivity | rewrite ?ew_ewset_other by lia; exact U32v
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; apply HWRdv; lia | apply awr_ok_nil] end.
Definition pd_emem : smem :=
[YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0 [];
 got_regionP;
 bcell_regionP 32;
 uar_got_regionP 33;
 uar_cell_regionP 33].
Definition pd_efacts : facts :=
mkFacts [(2%nat, mkAF 70368744177664 140737488355328 5);
         (32%nat, mkAF 2147450880 2147450880 0);
         (33%nat, mkAF 4096 140737479966720 2)] [] [].
Ltac pd_chain HKR HKP HKD r :=
rewrite (HKR (Z_to_bv 5 r) ltac:(vm_compute; reflexivity));
rewrite (HKP r ltac:(unfold acallee_saved; clear; lia) ltac:(clear; lia) ltac:(clear; lia));
rewrite (HKD (Z_to_bv 5 r) ltac:(vm_compute; reflexivity)).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
Section e.
Variable B : asyms.
Definition tput_dec_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (b p n v mn : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_PUT_DEC) /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
tcj_kept B PUT_DEC_STK lyc Sc W memc W2 mem2 (spZ regs)
(fun a => p <= a < p + 8 \/ b + n <= a < b + n + dec_len v mn) /\
garr8 SEGS (mrestrict (w_H W2) mem2) (b + n) (map bv_unsigned (DEC v mn)) /\
val_mem SEGS (mrestrict (w_H W2) mem2) p 8 (n + dec_len v mn).
Definition tput_dec_spec : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b p n v mn : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 b -> getr regs 11 = w64 p ->
bv_unsigned (getr regs 12) mod 2 ^ 32 = v -> (bv_unsigned (getr regs 12) < 2 ^ 32 \/ 10 <= v) ->
getr regs 13 = w64 mn -> 0 <= mn <= 10 ->
spZ regs mod 32 = 0 -> sp0 - STK <= spZ regs - PUT_DEC_STK -> spZ regs <= sp0 ->
Z.of_nat (length (frames Sc)) <= 8 ->
p mod 8 = 0 -> 0 <= b -> 0 <= n ->
val_mem SEGS (mrestrict (w_H W) memc) p 8 n ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 8 ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + n) (dec_len v mn) ->
tsrc_ok W memc (spZ regs) p 8 ->
tsrc_ok W memc (spZ regs) (b + n) (dec_len v mn) ->
(p + 8 <= b + n \/ b + n + dec_len v mn <= p) ->
(spZ regs <= p \/ p + 8 <= spZ regs - PUT_DEC_STK) ->
(spZ regs <= b + n \/ b + n + dec_len v mn <= spZ regs - PUT_DEC_STK) ->
st_nev Sc + EV_PUT_DEC <= EV_MAX ->
SRr SEGS W (cfg_at SEGS (BASE + AF_put_dec) regs memc mdc)
(tput_dec_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b p n v mn).
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let HBfree := pal_free B TL. Let HBmalloc := pal_malloc B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_ident) (PI := PI).
Let PBASE := @pa_B_ok _ _ PI. Let PBLO := @pa_base_lo _ _ PL_ident PI.
Lemma pd_dloop : forall (f : nat) (R x i T : Z) (P : list byte)
W (regs : bvmap 5 word) memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k,
(1 <= f)%nat -> 0 <= R < 2 ^ 64 -> R mod 2 ^ 32 = x -> (R < 2 ^ 32 \/ 10 <= x) ->
x < 10 ^ Z.of_nat f ->
i = Z.of_nat (length P) -> (length P + length (ds_lsb f x) <= 10)%nat ->
4096 <= T -> T + 10 <= alloc_ceiling -> in_app T 10 ->
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall a, T <= a < T + 10 -> awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF T 10 ->
getr regs 11 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 10 ->
getr regs 13 = Z_to_bv 64 14757395259826634752 -> getr regs 14 = Z_to_bv 64 9 ->
getr regs 22 = Z_to_bv 64 R -> getr regs 23 = Z_to_bv 64 SHADOW_OFF ->
getr regs 26 = Z_to_bv 64 T ->
garr8 SEGS (mrestrict (w_H W) memc) T (map bv_unsigned P) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 288))) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (AF_put_dec + 356))) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem' md' k /\
getr regs' 11 = Z_to_bv 64 (i + Z.of_nat (length (ds_lsb f x))) /\
(forall q : bv 5, reg_in q PD_DCLOB = false -> getr regs' q = getr regs q) /\
garr8 SEGS (mrestrict (w_H W) mem') T (map bv_unsigned (P ++ ds_lsb f x)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (T <= a < T + 10) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction f as [|f IH]; intros R x i T P W regs memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k
Hf HR Hxm Hdisj Hxf Hi Hlen HT0 HT1 HTapp HJ HWR HRA G11 G12 G13 G14 G22 G23 G26 HGA; [lia|].
assert (Hx : 0 <= x < 2 ^ 32) by (rewrite <- Hxm; apply Z.mod_pos_bound; lia).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hds : ds_lsb (S f) x = dg (x mod 10) :: (if x <? 10 then [] else ds_lsb f (x / 10))) by reflexivity.
assert (Hlen1 : (length P <= 9)%nat) by (rewrite Hds in Hlen; cbn [length] in Hlen; lia).
assert (Hi9 : 0 <= i <= 9) by lia.
assert (Hmod : 0 <= x mod 10 < 10) by (apply Z.mod_pos_bound; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 (T + i)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E32 : ew E 32 = Z_to_bv 64 (T + i))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs [Z_to_bv 64 (T + i)] 0%nat)).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (T + i)]) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
by (intros nn q Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E11 : ew E 11 = Z_to_bv 64 i) by (rewrite (EE 11%nat (11%bv : bv 5) eq_refl); exact G11).
assert (E22 : ew E 22 = Z_to_bv 64 R) by (rewrite (EE 22%nat (22%bv : bv 5) eq_refl); exact G22).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 23%nat (23%bv : bv 5) eq_refl); exact G23).
assert (E26 : ew E 26 = Z_to_bv 64 T) by (rewrite (EE 26%nat (26%bv : bv 5) eq_refl); exact G26).
assert (U11 : bv_unsigned (ew E 11) = i) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = R) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U26 : bv_unsigned (ew E 26) = T) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = T + i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (V32 : forall Ev, ew Ev 32 = Z_to_bv 64 (T + i) -> bv_unsigned (ew Ev 32) = T + i)
by (intros Ev HEv; rewrite HEv; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_put_dec + 288) pd_dsr pd_dmem None pd_dfacts)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 288))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full E (AF_put_dec + 288) pd_dsr regs pd_dmem pd_dfacts (mrestrict (w_H W) memc)).
- unfold pd_dsr.
apply regs_ok_pin; [| intros Hq; discriminate Hq | rewrite G14; reflexivity].
apply regs_ok_pin; [| intros Hq; discriminate Hq | rewrite G13; reflexivity].
apply regs_ok_pin; [| intros Hq; discriminate Hq | rewrite G12; reflexivity].
rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- apply Forall_cons; [| apply Forall_nil].
unfold pd_dmem, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U32. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS).
exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T + i + o) HJ (HWR (T + i + o) ltac:(lia)))).
- cbn. tauto.
- split; [| split; [exact I |]].
+ unfold pd_dfacts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite U11, U22, U23, U26, U32.
repeat split; unfold SHADOW_OFF; try lia; try (rewrite Z.pow_0_r; apply Z.mod_1_r).
+ unfold pd_dfacts. cbn [f_alias alias_ok]. split; [| exact I].
rewrite (pd_denot_add E 26 11 T i E26 E11 ltac:(lia) ltac:(lia) ltac:(lia)).
symmetry. apply (pd_denot_atom E 32 (T + i) E32). lia. }
clear HE.
pose proof HS as HS0.
assert (SHOK : sh_ok SEGS (SOff 23 0) pd_dsh E (mrestrict (w_H W) memc)).
{ unfold pd_dsh, sh_ok. apply Forall_cons; [| apply Forall_nil]. split.
- cbn [she_m she_lo she_hi].
rewrite (U_atom E 32 (T + i) E32 ltac:(lia)).
replace (T + i + 0) with (T + i) by lia. change (1 - 0) with 1.
eapply obl_of_range;
[exact HRA | rewrite (U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)); reflexivity | lia | lia].
- intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha.
rewrite (U_atom E 32 (T + i) E32 ltac:(lia)) in Ha.
rewrite (U_atom E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia)).
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32%nat (T + i)); [reflexivity | exact U32 | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWR. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ =>
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (T + i <= a < T + i + 1) ->
aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna;
  eapply (kept_of_frame E _ (w_H W) memc (ms_mem msX) (fun z => T + i <= z < T + i + 1));
  [ lazymatch goal with Hfx : frame_of _ _ _ _ |- _ => exact Hfx end | | exact Ha | exact Hna ];
  intros bb wlo whi aa Hin Hrr;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end;
  cbn [In] in Hin; destruct Hin as [Heq | []]; injection Heq as <- <- <-;
  cbn [base_val] in Hrr; rewrite U32 in Hrr; lia
| ] end.
assert (PRES : forall (m2 : word -> option byte),
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m2) ->
forall a, apresent (w_H W) memc a -> apresent (w_H W) m2 a)
by (intros m2 Hg a Ha; eapply apresent_grows; [exact Hg | exact Ha]).
assert (HRA2 : forall (m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ (T + i <= a < T + i + 1) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF T 10).
{ intros m2 Hk xx Hxx. destruct (HRA xx Hxx) as (ss & Hs & Hok). exists ss. split; [| exact Hok].
rewrite <- Hs. unfold shadow_of_addr in *.
assert (H8 : 8 * (xx / 8) <= xx) by (apply Z.mul_div_le; lia).
assert (H8b : 0 <= xx / 8) by (apply Z.div_pos; lia).
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in HTapp |- *.
apply Hk; lia. }
assert (HGA2 : forall (m2 : word -> option byte),
(forall a, 0 <= a < 2 ^ 64 -> ~ (T + i <= a < T + i + 1) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) memc a) ->
val_mem SEGS (mrestrict (w_H W) m2) (T + i) 1 (48 + x mod 10) ->
garr8 SEGS (mrestrict (w_H W) m2) T (map bv_unsigned (P ++ [dg (x mod 10)]))).
{ intros m2 Hk Hv j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
rewrite map_app. cbn [map].
destruct (Nat.eq_dec j (length P)) as [Hje | Hne].
- rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map, Hje.
replace (length P - length P)%nat with 0%nat by lia. cbn [nth].
rewrite (pd_dg_val (x mod 10)) by lia.
split; [| lia]. rewrite <- Hi. exact Hv.
- rewrite app_nth1 by (rewrite length_map; lia).
destruct (HGA j ltac:(rewrite length_map; lia)) as [Hvj Hbj]. split; [| exact Hbj].
eapply (val_mem_kept SEGS (w_H W) (w_H W) memc m2 (T + Z.of_nat j) 1); [| exact Hvj].
intros kk Hkk. apply Hk; lia. }
clear HF HFr.
psrr_branch_tok RUN BR HS SHOK Bspan.
- lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F22a : ew Ev 22 = Z_to_bv 64 R) by (rewrite ?ew_ewset_other by lia; exact E22);
rewrite branch_ltu_U, U_SLit, (U_atom Ev 22 R F22a ltac:(lia)) in Hc end.
change (zcanon 9) with 9 in Hc.
rewrite (pd_ltu9 R x Hxm Hdisj ltac:(lia)) in Hc. apply (proj1 (Z.leb_le _ _)) in Hc.
assert (Hf1 : (1 <= f)%nat).
{ destruct f as [|f0]; [| lia]. exfalso. change (10 ^ Z.of_nat 1) with 10 in Hxf. lia. }
assert (Hq : 0 <= x / 10 < 2 ^ 32) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (Hqf : x / 10 < 10 ^ Z.of_nat f)
by (apply Z.div_lt_upper_bound; [lia |]; rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hxf by lia; lia).
assert (Hds10 : ds_lsb (S f) x = dg (x mod 10) :: ds_lsb f (x / 10))
by (rewrite Hds, (proj2 (Z.ltb_ge x 10) ltac:(lia)); reflexivity).
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_put_dec + 288).
{ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 32%nat (T + i));
[reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | | apply awr_ok_nil] end.
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWR. lia. }
pd_after_step HS KEPT2 PRES2 HVAL2 F11b F22b F32b E11 E22 E32 V32 KEPT (T + i) (T + i + 1) i R x (T + i) HR Hxm.
pose proof HS as HSf.
pmkst HS.
prreg HS (11%bv : bv 5) QQ11. prreg HS (22%bv : bv 5) QQ22.
prreg HS (12%bv : bv 5) QQ12. prreg HS (13%bv : bv 5) QQ13. prreg HS (14%bv : bv 5) QQ14.
pd_regs_kept HK HSf HAE PD_DKEPT.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?ms2) _ (ms_mem ?ms3) _) ?md2) _ =>
eapply (IH (x / 10) (x / 10) (i + 1) T (P ++ [dg (x mod 10)]) W (ms_regs ms2) (ms_mem ms3) md2
STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k) end.
- exact Hf1.
- lia.
- apply Z.mod_small; lia.
- left; lia.
- exact Hqf.
- rewrite length_app. cbn [length]. lia.
- rewrite length_app. cbn [length]. rewrite Hds10 in Hlen. cbn [length] in Hlen. lia.
- exact HT0.
- exact HT1.
- exact HTapp.
- exact HJ.
- exact HWR.
- exact (HRA2 _ KEPT2).
- rewrite QQ11, E11, (unsigned_lit_small i) by lia; f_equal; lia.
- rewrite QQ12. reflexivity.
- rewrite QQ13. reflexivity.
- rewrite QQ14. reflexivity.
- rewrite QQ22, E22, pd_sll32, pd_mulhu, pd_srl35.
rewrite (unsigned_lit_small 14757395259826634752) by lia.
rewrite (q_word (Z_to_bv 64 R)). rewrite (unsigned_lit_small R) by lia.
rewrite Hxm. reflexivity.
- rewrite (HK (23%bv : bv 5) ltac:(cbv; tauto)). exact G23.
- rewrite (HK (26%bv : bv 5) ltac:(cbv; tauto)). exact G26.
- exact (HGA2 _ KEPT2 HVAL2). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & Hc3 & HJ3 & QQ11' & HK3 & HGA3 & HKEPT3 & HPRES3).
split; [reflexivity|]. exists regs3, mem3, md3.
split; [exact Hc3|]. split; [exact HJ3|].
split; [rewrite QQ11', Hds10; cbn [length]; f_equal; lia|].
split.
{ intros q Hq'. rewrite (HK3 q Hq').
destruct (pd_dclob_kept q Hq') as [-> | [Hin | Hin]].
- rewrite (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HSf), (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HS0).
reflexivity.
- exact (HK q Hin).
- cbv [PD_DPIN In] in Hin.
destruct Hin as [Hq12 | [Hq13 | [Hq14 | []]]]; subst q;
[rewrite QQ12, G12 | rewrite QQ13, G13 | rewrite QQ14, G14]; reflexivity. }
split; [rewrite Hds10; cbn [app]; rewrite <- app_assoc in HGA3; cbn [app] in HGA3; exact HGA3|].
split.
{ intros a Ha Hna. rewrite (HKEPT3 a Ha Hna). apply KEPT2; [exact Ha | lia]. }
{ intros a Ha. apply HPRES3. apply PRES2. exact Ha. }
- lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F22a : ew Ev 22 = Z_to_bv 64 R) by (rewrite ?ew_ewset_other by lia; exact E22);
rewrite branch_ltu_U, U_SLit, (U_atom Ev 22 R F22a ltac:(lia)) in Hc end.
change (zcanon 9) with 9 in Hc.
rewrite (pd_ltu9 R x Hxm Hdisj ltac:(lia)) in Hc. apply (proj1 (Z.leb_gt _ _)) in Hc.
assert (Hds0 : ds_lsb (S f) x = [dg (x mod 10)])
by (rewrite Hds, (proj2 (Z.ltb_lt x 10) ltac:(lia)); reflexivity).
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_put_dec + 356).
{ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 32%nat (T + i));
[reflexivity | rewrite ?ew_ewset_other by lia; exact U32 | | apply awr_ok_nil] end.
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWR. lia. }
pd_after_step HS KEPT2 PRES2 HVAL2 F11b F22b F32b E11 E22 E32 V32 KEPT (T + i) (T + i + 1) i R x (T + i) HR Hxm.
pose proof HS as HSf.
pmkst HS.
prreg HS (11%bv : bv 5) QQ11.
prreg HS (12%bv : bv 5) QQ12. prreg HS (13%bv : bv 5) QQ13. prreg HS (14%bv : bv 5) QQ14.
pd_regs_kept HK HSf HAE PD_DKEPT.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?ms2) _ (ms_mem ?ms3) _) ?md2] =>
exists (ms_regs ms2), (ms_mem ms3), md2 end.
split; [reflexivity|]. split; [exact HJ|].
split; [rewrite QQ11, Hds0; cbn [length]; rewrite E11, (unsigned_lit_small i) by lia; f_equal; lia|].
split.
{ intros q Hq'. destruct (pd_dclob_kept q Hq') as [-> | [Hin | Hin]].
- rewrite (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HSf), (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HS0).
reflexivity.
- exact (HK q Hin).
- cbv [PD_DPIN In] in Hin.
destruct Hin as [Hq12 | [Hq13 | [Hq14 | []]]]; subst q;
[rewrite QQ12, G12 | rewrite QQ13, G13 | rewrite QQ14, G14]; reflexivity. }
split; [rewrite Hds0; exact (HGA2 _ KEPT2 HVAL2)|].
split.
{ intros a Ha Hna. apply KEPT2; [exact Ha | lia]. }
{ intros a Ha. apply PRES2. exact Ha. }
Qed.

Lemma pd_rloop : forall (rem : nat) (src n b p : Z) (Dl : list byte)
W (regs : bvmap 5 word) memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k,
(1 <= rem)%nat -> length Dl = rem ->
0 <= n -> n + Z.of_nat rem <= 2 ^ 47 ->
4096 <= b + n -> b + n + Z.of_nat rem <= 2 ^ 47 -> (forall a, b + n <= a < b + n + Z.of_nat rem -> in_app a 1 \/ alloc_ceiling <= a) -> 0 <= b ->
4096 <= p -> p + 8 <= 2 ^ 47 -> p mod 8 = 0 -> (in_app p 8 \/ alloc_ceiling <= p) ->
4096 <= src - Z.of_nat rem + 1 -> src + 1 <= alloc_ceiling -> in_app (src - Z.of_nat rem + 1) (Z.of_nat rem) ->
(p + 8 <= b + n \/ b + n + Z.of_nat rem <= p) ->
(src + 1 <= b + n \/ b + n + Z.of_nat rem <= src - Z.of_nat rem + 1) ->
(src + 1 <= p \/ p + 8 <= src - Z.of_nat rem + 1) ->
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k ->
(forall a, p <= a < p + 8 -> awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a) ->
(forall a, b + n <= a < b + n + Z.of_nat rem -> awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 8 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (b + n) (Z.of_nat rem) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (src - Z.of_nat rem + 1) (Z.of_nat rem) ->
aview SEGS (w_H W) memc (SHADOW_OFF + p / 8) = Some 0 ->
val_mem SEGS (mrestrict (w_H W) memc) p 8 n ->
(forall j, (j < rem)%nat -> val_mem SEGS (mrestrict (w_H W) memc) (src - Z.of_nat j) 1 (bv_unsigned (nth j Dl (Z_to_bv 8 0)))) ->
getr regs 10 = Z_to_bv 64 src -> getr regs 12 = Z_to_bv 64 (- Z.of_nat rem) ->
getr regs 13 = Z_to_bv 64 src -> getr regs 14 = Z_to_bv 64 (SHADOW_OFF + p / 8) ->
getr regs 19 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 b -> getr regs 23 = Z_to_bv 64 SHADOW_OFF ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 452))) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (AF_put_dec + 532))) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W mem' md' k /\
(forall q : bv 5, reg_in q PD_RCLOB = false -> getr regs' q = getr regs q) /\
val_mem SEGS (mrestrict (w_H W) mem') p 8 (n + Z.of_nat rem) /\
garr8 SEGS (mrestrict (w_H W) mem') (b + n) (map bv_unsigned Dl) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 8) -> ~ (b + n <= a < b + n + Z.of_nat rem) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction rem as [|rem IH]; intros src n b p Dl W regs memc mdc STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k
Hrem HDl Hn0 Hn1 Hb0 Hb1 Hbapp Hb2 Hp0 Hp1 Hp8 Hpapp Hs0 Hs1 Hsapp Hsep1 Hsep2 Hsep3
HJ HWRp HWRd HRAp HRAd HRAs HSHp Hvp HSRC G10 G12 G13 G14 G19 G20 G23; [lia|].
pose proof (Hbapp (b + n) ltac:(clear - Hrem; lia)) as Hbapp1.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (d0 := nth 0 Dl (Z_to_bv 8 0)).
assert (Hd0 : 0 <= bv_unsigned d0 < 256)
by (pose proof (bv_unsigned_in_range 8 d0) as Hq; change (bv_modulus 8) with 256 in Hq; lia).
assert (Hsrcv : val_mem SEGS (mrestrict (w_H W) memc) src 1 (bv_unsigned d0))
by (pose proof (HSRC 0%nat ltac:(lia)) as Hq; cbn [Z.of_nat] in Hq; rewrite Z.sub_0_r in Hq; exact Hq).
assert (H8p : 8 * (p / 8) = p) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
assert (HshpL : 2147450880 <= SHADOW_OFF + p / 8 <= 19739720941568)
by (unfold SHADOW_OFF; unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg in Hpapp; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 (b + n); Z_to_bv 64 n; Z_to_bv 64 (bv_unsigned d0)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EXx : forall j, (j < 3)%nat -> ew E (32 + j) =
nth j [Z_to_bv 64 (b + n); Z_to_bv 64 n; Z_to_bv 64 (bv_unsigned d0)] (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXx 0%nat ltac:(lia)) as E32. pose proof (EXx 1%nat ltac:(lia)) as E33.
pose proof (EXx 2%nat ltac:(lia)) as E34.
cbn [Nat.add nth] in E32, E33, E34. clear EXx.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (b + n); Z_to_bv 64 n; Z_to_bv 64 (bv_unsigned d0)]) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
by (intros nn q Hq; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hq).
assert (E13 : ew E 13 = Z_to_bv 64 src) by (rewrite (EE 13%nat (13%bv : bv 5) eq_refl); exact G13).
assert (E14 : ew E 14 = Z_to_bv 64 (SHADOW_OFF + p / 8)) by (rewrite (EE 14%nat (14%bv : bv 5) eq_refl); exact G14).
assert (E19 : ew E 19 = Z_to_bv 64 p) by (rewrite (EE 19%nat (19%bv : bv 5) eq_refl); exact G19).
assert (E20 : ew E 20 = Z_to_bv 64 b) by (rewrite (EE 20%nat (20%bv : bv 5) eq_refl); exact G20).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 23%nat (23%bv : bv 5) eq_refl); exact G23).
assert (E10 : ew E 10 = Z_to_bv 64 src) by (rewrite (EE 10%nat (10%bv : bv 5) eq_refl); exact G10).
assert (E12 : ew E 12 = Z_to_bv 64 (- Z.of_nat (S rem))) by (rewrite (EE 12%nat (12%bv : bv 5) eq_refl); exact G12).
assert (U13 : bv_unsigned (ew E 13) = src) by (rewrite E13; apply unsigned_lit_small; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF + p / 8) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U19 : bv_unsigned (ew E 19) = p) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = b) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF) by (rewrite E23; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = b + n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = bv_unsigned d0) by (rewrite E34; apply unsigned_lit_small; lia).
assert (V32 : forall Ev, ew Ev 32 = Z_to_bv 64 (b + n) -> bv_unsigned (ew Ev 32) = b + n)
by (intros Ev HEv; rewrite HEv; apply unsigned_lit_small; lia).
assert (V19 : forall Ev, ew Ev 19 = Z_to_bv 64 p -> bv_unsigned (ew Ev 19) = p)
by (intros Ev HEv; rewrite HEv; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_put_dec + 452) pd_rsr pd_rmem None pd_rfacts)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_put_dec + 452))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full E (AF_put_dec + 452) pd_rsr regs pd_rmem pd_rfacts (mrestrict (w_H W) memc)).
- unfold pd_rsr.
apply regs_ok_pin; [| intros Hq; discriminate Hq | rewrite G10; symmetry; apply (pd_denot_atom E 13 src E13); lia].
rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- unfold pd_rmem. apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) src 0 1%N (SOff 34 0) (bv_unsigned d0));
[apply (pd_denot_atom E 34 (bv_unsigned d0) E34); lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hsrcv].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U14. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) (SHADOW_OFF + p / 8) 0 1%N (SLit 0) 0);
[reflexivity | cbn; lia | cbn; lia | rewrite Z.add_0_r; apply pd_vm1; [exact HSHp | lia]].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U19. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable SEGS).
exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + o) HJ (HWRp (p + o) ltac:(lia)))). }
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) p 0 8%N (SOff 33 0) n);
[apply (pd_denot_atom E 33 n E33); lia | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Hvp].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U32. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS).
exact (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (b + n + o) HJ (HWRd (b + n + o) ltac:(lia)))).
- unfold pd_rmem. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U13, U14, U19, U32.
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hpapp, Hbapp1, Hsapp |- *.
repeat split; lia.
- split; [| split; [exact I |]].
+ unfold pd_rfacts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite U13, U19, U32, U33, U20, U34, U14, U23.
repeat split; unfold SHADOW_OFF in *; try lia;
try (rewrite Z.pow_0_r; apply Z.mod_1_r);
try (change (2 ^ 3) with 8; rewrite <- H8p; replace (8 * (p / 8)) with (p / 8 * 8) by lia; apply Z_mod_mult).
+ unfold pd_rfacts. cbn [f_alias alias_ok]. split; [| exact I].
rewrite (pd_denot_add E 20 33 b n E20 E33 ltac:(lia) ltac:(lia) ltac:(lia)).
symmetry. apply (pd_denot_atom E 32 (b + n) E32). lia. }
clear HE.
pose proof HS as HS0.
assert (SHOK : sh_ok SEGS (SOff 23 0) pd_rsh E (mrestrict (w_H W) memc)).
{ unfold pd_rsh, sh_ok.
assert (HBx : U E (SOff 23 0) = SHADOW_OFF) by (apply (U_atom E 23 SHADOW_OFF E23); unfold SHADOW_OFF; lia).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]].
- split.
+ cbn [she_m she_lo she_hi]. rewrite (U_atom E 13 src E13 ltac:(lia)).
replace (src + 0) with src by lia. change (1 - 0) with 1.
eapply obl_of_range; [exact HRAs | exact HBx | lia | lia].
+ intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha.
rewrite (U_atom E 13 src E13 ltac:(lia)) in Ha. rewrite HBx.
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hsapp |- *. lia.
- split.
+ cbn [she_m she_lo she_hi]. rewrite (U_atom E 19 p E19 ltac:(lia)).
replace (p + 0) with p by lia. change (8 - 0) with 8.
eapply obl_of_range; [exact HRAp | exact HBx | lia | lia].
+ intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha.
rewrite (U_atom E 19 p E19 ltac:(lia)) in Ha. rewrite HBx.
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hpapp |- *. lia.
- split.
+ cbn [she_m she_lo she_hi]. rewrite (U_atom E 32 (b + n) E32 ltac:(lia)).
replace (b + n + 0) with (b + n) by lia. change (1 - 0) with 1.
eapply obl_of_range; [exact HRAd | exact HBx | lia | lia].
+ intros a Ha. cbn [she_m she_lo she_hi Z.min Z.max] in Ha.
rewrite (U_atom E 32 (b + n) E32 ltac:(lia)) in Ha. rewrite HBx.
unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in Hbapp1 |- *. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold pd_rmem.
eapply (awr_ok_cons_ro E); [cbn; lia |].
eapply (awr_ok_cons_ro E); [cbn; lia |].
eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 19%nat p); [reflexivity | exact U19 | | ].
{ cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWRp. lia. }
eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 32%nat (b + n)); [reflexivity | exact U32 | | apply awr_ok_nil].
cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HWRd. lia. }
lazymatch goal with |- SRr _ _ (mkCfg ?msX _) _ =>
assert (KEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 8) -> ~ (b + n <= a < b + n + 1) ->
aview SEGS (w_H W) (ms_mem msX) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb;
  eapply (kept_of_frame E _ (w_H W) memc (ms_mem msX)
    (fun z => (p <= z < p + 8) \/ (b + n <= z < b + n + 1)));
  [ exact HFr | | exact Ha | intros [Hq | Hq]; [exact (Hna Hq) | exact (Hnb Hq)] ];
  intros bb wlo whi aa Hin Hrr;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end;
  cbn [In] in Hin;
  destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]]; injection Heq as <- <- <-;
  cbn [base_val] in Hrr; first [rewrite U13 in Hrr | rewrite U14 in Hrr | rewrite U19 in Hrr | rewrite U32 in Hrr];
  first [left; lia | right; lia | lia]
| ] end.
assert (PRES : forall (m2 : word -> option byte),
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) m2) ->
forall a, apresent (w_H W) memc a -> apresent (w_H W) m2 a)
by (intros m2 Hg a Ha; eapply apresent_grows; [exact Hg | exact Ha]).
clear HF HFr.
psrr_branch_tok RUN BR HS SHOK Bspan.
- assert (Hrem1 : (1 <= rem)%nat).
{ destruct rem as [|r0]; [| lia]. exfalso.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F12 : ew Ev 12 = Z_to_bv 64 (- Z.of_nat 1))
by (rewrite ?ew_ewset_other by lia; rewrite (EE 12%nat (12%bv : bv 5) eq_refl); exact G12);
rewrite branch_ne_U, U_SLit, (pd_u12 Ev (- Z.of_nat 1) F12) in Hc end.
cbn [Z.of_nat] in Hc. change (- 1 + 1) with 0 in Hc. rewrite Zmod_0_l in Hc.
change (zcanon 0) with 0 in Hc. cbn in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_put_dec + 452).
{ pd_rawr HWRp HWRd U19 U32. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F19b : ew Ev 19 = Z_to_bv 64 p) by (rewrite ?ew_ewset_other by lia; exact E19);
assert (F32b : ew Ev 32 = Z_to_bv 64 (b + n)) by (rewrite ?ew_ewset_other by lia; exact E32);
assert (F33b : ew Ev 33 = Z_to_bv 64 n) by (rewrite ?ew_ewset_other by lia; exact E33);
assert (F34b : ew Ev 34 = Z_to_bv 64 (bv_unsigned d0)) by (rewrite ?ew_ewset_other by lia; exact E34) end.
lazymatch goal with |- SRr _ _ (mkCfg ?ms2 _) _ =>
assert (KEPT2 : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 8) -> ~ (b + n <= a < b + n + 1) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb; rewrite <- (KEPT a Ha Hna Hnb);
  eapply (kept_of_frame _ _ (w_H W) _ (ms_mem ms2) (fun z => (p <= z < p + 8) \/ (b + n <= z < b + n + 1)));
  [ lazymatch goal with Hfx : frame_of _ _ _ _ |- _ => exact Hfx end | | exact Ha
  | intros [Hq | Hq]; [exact (Hna Hq) | exact (Hnb Hq)] ];
  intros bb wlo whi aa Hin Hrr;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end;
  cbn [In] in Hin; destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]]; injection Heq as <- <- <-;
  cbn [base_val] in Hrr;
  first [rewrite (V19 _ F19b) in Hrr; left; lia | rewrite (V32 _ F32b) in Hrr; right; lia | lia]
| ];
assert (PRES2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
by (intros a Ha; eapply apresent_grows; [eassumption |]; eapply apresent_grows; [eassumption |]; exact Ha)
end.
lazymatch goal with |- SRr _ _ (mkCfg ?ms2 _) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) ms2) 2%nat _ HS eq_refl) as HROp;
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) ms2) 3%nat _ HS eq_refl) as HROd;
cbn [ms_mem restrict] in HROp, HROd;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem ms2)) 19%nat p _ 0 8 0 8 0 8%N (SOff 33 1)
  HROp (V19 Ev F19b) ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HVALP;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem ms2)) 32%nat (b + n) _ 0 1 0 1 0 1%N (SOff 34 0)
  HROd (V32 Ev F32b) ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HVALD;
rewrite (pd_denot_off Ev 33 n 1 F33b ltac:(lia)) in HVALP;
rewrite (pd_denot_off Ev 34 (bv_unsigned d0) 0 F34b ltac:(lia)) in HVALD
end end.
replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HVALP by (vm_compute; reflexivity).
replace (2 ^ (8 * Z.of_N 1)) with 256 in HVALD by (vm_compute; reflexivity).
change (N.to_nat 8) with 8%nat in HVALP. change (N.to_nat 1) with 1%nat in HVALD.
rewrite (unsigned_lit_small (n + 1)) in HVALP by lia.
rewrite (Z.mod_small (n + 1) (2 ^ 64)) in HVALP by lia.
rewrite Z.add_0_r in HVALP, HVALD.
rewrite (unsigned_lit_small (bv_unsigned d0 + 0)) in HVALD by lia.
rewrite Z.add_0_r in HVALD. rewrite (Z.mod_small (bv_unsigned d0) 256) in HVALD by lia.
pose proof HS as HSf.
pmkst HS.
prreg HS (10%bv : bv 5) QQr10. prreg HS (12%bv : bv 5) QQr12. prreg HS (13%bv : bv 5) QQr13.
pd_regs_kept HK HSf HAE PD_RKEPT.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?ms2) _ (ms_mem ?ms3) _) ?md2) _ =>
eapply (IH (src - 1) (n + 1) b p (tl Dl) W (ms_regs ms2) (ms_mem ms3) md2
STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc k) end.
- exact Hrem1.
- rewrite pd_length_tl, HDl. cbn [length]. lia.
- lia.
- lia.
- lia.
- lia.
- intros a Ha. apply Hbapp. clear - Ha; lia.
- lia.
- lia.
- lia.
- exact Hp8.
- exact Hpapp.
- lia.
- lia.
- unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg in Hsapp |- *. lia.
- lia.
- lia.
- lia.
- exact HJ.
- exact HWRp.
- intros a Ha. apply HWRd. lia.
- intros xx Hxx. destruct (HRAp xx Hxx) as (ss & Hs & Hok). exists ss. split; [| exact Hok].
rewrite <- Hs. apply KEPT2; pd_band_app.
- intros xx Hxx. destruct (HRAd xx ltac:(lia)) as (ss & Hs & Hok). exists ss. split; [| exact Hok].
rewrite <- Hs. apply KEPT2; pd_band_app.
- intros xx Hxx. destruct (HRAs xx ltac:(lia)) as (ss & Hs & Hok). exists ss. split; [| exact Hok].
rewrite <- Hs. apply KEPT2; pd_band_app.
- rewrite <- HSHp. apply KEPT2; pd_band_app.
- exact HVALP.
- intros j Hj. eapply (val_mem_kept SEGS (w_H W) (w_H W) memc _ (src - 1 - Z.of_nat j) 1);
[ intros kk Hkk; apply KEPT2; lia
| rewrite (pd_nth_tl Dl j); pose proof (HSRC (S j) ltac:(lia)) as Hq; rewrite Nat2Z.inj_succ in Hq;
  replace (src - Z.succ (Z.of_nat j)) with (src - 1 - Z.of_nat j) in Hq by lia; exact Hq ].
- rewrite QQr10. cbn [sv_denot]. rewrite E13, (unsigned_lit_small src) by lia; f_equal; lia.
- rewrite QQr12, E12, unsigned_lit. unfold zcanon, M64. apply pd_bv_eqm.
rewrite Zplus_mod_idemp_l. f_equal. lia.
- rewrite QQr13. cbn [sv_denot]. rewrite E13, (unsigned_lit_small src) by lia; f_equal; lia.
- rewrite (HK (14%bv : bv 5) ltac:(cbv; tauto)). exact G14.
- rewrite (HK (19%bv : bv 5) ltac:(cbv; tauto)). exact G19.
- rewrite (HK (20%bv : bv 5) ltac:(cbv; tauto)). exact G20.
- rewrite (HK (23%bv : bv 5) ltac:(cbv; tauto)). exact G23. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & Hc3 & HJ3 & HK3 & HVP3 & HGD3 & HKEPT3 & HPRES3).
split; [reflexivity|]. exists regs3, mem3, md3.
split; [exact Hc3|]. split; [exact HJ3|].
split.
{ intros q Hq'. rewrite (HK3 q Hq').
destruct (pd_rclob_kept q Hq') as [-> | Hin].
- rewrite (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HSf), (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HS0).
reflexivity.
- exact (HK q Hin). }
split; [replace (n + Z.of_nat (S rem)) with (n + 1 + Z.of_nat rem) by lia; exact HVP3|].
split.
{ intros j Hj. rewrite length_map, HDl in Hj.
destruct (Nat.eq_dec j 0) as [-> | Hne].
- cbn [Z.of_nat]. rewrite Z.add_0_r.
assert (Hnth : nth 0 (map bv_unsigned Dl) 0 = bv_unsigned d0)
by (destruct Dl as [|c Dl']; [cbn in HDl; lia | reflexivity]).
rewrite Hnth. split; [| exact Hd0].
eapply (val_mem_kept SEGS (w_H W) (w_H W) _ mem3 (b + n) 1); [| exact HVALD].
intros kk Hkk. apply HKEPT3; lia.
- assert (Hnth : nth j (map bv_unsigned Dl) 0 = nth (j - 1) (map bv_unsigned (tl Dl)) 0).
{ destruct Dl as [|c Dl']; [cbn in HDl; lia |]. cbn [map tl nth].
destruct j as [|j0]; [lia |]. cbn [nth]. replace (S j0 - 1)%nat with j0 by lia. reflexivity. }
rewrite Hnth.
destruct (HGD3 (j - 1)%nat ltac:(rewrite length_map, pd_length_tl, HDl; cbn [length]; lia)) as [Hv3 Hb3].
split; [| exact Hb3].
replace (b + n + Z.of_nat j) with (b + (n + 1) + Z.of_nat (j - 1)) by lia. exact Hv3. }
split.
{ intros a Ha Hna Hnb. rewrite (HKEPT3 a Ha Hna ltac:(lia)). apply KEPT2; [exact Ha | lia | lia]. }
{ intros a Ha. apply HPRES3. apply PRES2. exact Ha. }
- assert (Hrem0 : rem = 0%nat).
{ destruct rem as [|r0]; [reflexivity | exfalso].
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F12 : ew Ev 12 = Z_to_bv 64 (- Z.of_nat (S (S r0))))
by (rewrite ?ew_ewset_other by lia; rewrite (EE 12%nat (12%bv : bv 5) eq_refl); exact G12);
rewrite branch_ne_U, U_SLit, (pd_u12 Ev (- Z.of_nat (S (S r0))) F12) in Hc end.
change (zcanon 0) with 0 in Hc.
replace (- Z.of_nat (S (S r0)) + 1) with (- (Z.of_nat (S (S r0)) - 1)) in Hc by lia.
rewrite Z.mod_opp_l_nz in Hc;
[| lia | rewrite (Z.mod_small (Z.of_nat (S (S r0)) - 1) (2 ^ 64)) by lia; lia].
rewrite (Z.mod_small (Z.of_nat (S (S r0)) - 1) (2 ^ 64)) in Hc by lia.
apply (proj1 (negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc. lia. }
subst rem.
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_put_dec + 532).
{ pd_rawr HWRp HWRd U19 U32. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F19b : ew Ev 19 = Z_to_bv 64 p) by (rewrite ?ew_ewset_other by lia; exact E19);
assert (F32b : ew Ev 32 = Z_to_bv 64 (b + n)) by (rewrite ?ew_ewset_other by lia; exact E32);
assert (F33b : ew Ev 33 = Z_to_bv 64 n) by (rewrite ?ew_ewset_other by lia; exact E33);
assert (F34b : ew Ev 34 = Z_to_bv 64 (bv_unsigned d0)) by (rewrite ?ew_ewset_other by lia; exact E34) end.
lazymatch goal with |- SRr _ _ (mkCfg ?ms2 _) _ =>
assert (KEPT2 : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 8) -> ~ (b + n <= a < b + n + 1) ->
aview SEGS (w_H W) (ms_mem ms2) a = aview SEGS (w_H W) memc a);
[ intros a Ha Hna Hnb; rewrite <- (KEPT a Ha Hna Hnb);
  eapply (kept_of_frame _ _ (w_H W) _ (ms_mem ms2) (fun z => (p <= z < p + 8) \/ (b + n <= z < b + n + 1)));
  [ lazymatch goal with Hfx : frame_of _ _ _ _ |- _ => exact Hfx end | | exact Ha
  | intros [Hq | Hq]; [exact (Hna Hq) | exact (Hnb Hq)] ];
  intros bb wlo whi aa Hin Hrr;
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end;
  cbn [In] in Hin; destruct Hin as [Heq | [Heq | [Heq | [Heq | []]]]]; injection Heq as <- <- <-;
  cbn [base_val] in Hrr;
  first [rewrite (V19 _ F19b) in Hrr; left; lia | rewrite (V32 _ F32b) in Hrr; right; lia | lia]
| ];
assert (PRES2 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms2) a)
by (intros a Ha; eapply apresent_grows; [eassumption |]; eapply apresent_grows; [eassumption |]; exact Ha)
end.
lazymatch goal with |- SRr _ _ (mkCfg ?ms2 _) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx _ =>
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) ms2) 2%nat _ HS eq_refl) as HROp;
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) ms2) 3%nat _ HS eq_refl) as HROd;
cbn [ms_mem restrict] in HROp, HROd;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem ms2)) 19%nat p _ 0 8 0 8 0 8%N (SOff 33 1)
  HROp (V19 Ev F19b) ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HVALP;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem ms2)) 32%nat (b + n) _ 0 1 0 1 0 1%N (SOff 34 0)
  HROd (V32 Ev F32b) ltac:(cbn [In]; left; reflexivity) ltac:(cbn; lia)) as HVALD;
rewrite (pd_denot_off Ev 33 n 1 F33b ltac:(lia)) in HVALP;
rewrite (pd_denot_off Ev 34 (bv_unsigned d0) 0 F34b ltac:(lia)) in HVALD
end end.
replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HVALP by (vm_compute; reflexivity).
replace (2 ^ (8 * Z.of_N 1)) with 256 in HVALD by (vm_compute; reflexivity).
change (N.to_nat 8) with 8%nat in HVALP. change (N.to_nat 1) with 1%nat in HVALD.
rewrite (unsigned_lit_small (n + 1)) in HVALP by lia.
rewrite (Z.mod_small (n + 1) (2 ^ 64)) in HVALP by lia.
rewrite Z.add_0_r in HVALP, HVALD.
rewrite (unsigned_lit_small (bv_unsigned d0 + 0)) in HVALD by lia.
rewrite Z.add_0_r in HVALD. rewrite (Z.mod_small (bv_unsigned d0) 256) in HVALD by lia.
pose proof HS as HSf.
pmkst HS.
pd_regs_kept HK HSf HAE PD_RKEPT.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?ms2) _ (ms_mem ?ms3) _) ?md2] =>
exists (ms_regs ms2), (ms_mem ms3), md2 end.
split; [reflexivity|]. split; [exact HJ|].
split.
{ intros q Hq'. destruct (pd_rclob_kept q Hq') as [-> | Hin].
- rewrite (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HSf), (st_ok_pi_restrict_reg (w_H W) _ _ _ 0%bv HS0).
reflexivity.
- exact (HK q Hin). }
split; [cbn [Z.of_nat]; replace (n + 1) with (n + 1) by lia; exact HVALP|].
split.
{ intros j Hj. rewrite length_map, HDl in Hj. cbn [length] in Hj.
assert (j = 0)%nat by lia. subst j. cbn [Z.of_nat]. rewrite Z.add_0_r.
assert (Hnth : nth 0 (map bv_unsigned Dl) 0 = bv_unsigned d0)
by (destruct Dl as [|c Dl']; [cbn in HDl; lia | reflexivity]).
rewrite Hnth. split; [exact HVALD | exact Hd0]. }
split.
{ intros a Ha Hna Hnb. apply KEPT2; [exact Ha | lia | cbn [Z.of_nat] in Hnb; lia]. }
{ intros a Ha. apply PRES2. exact Ha. }
Qed.

Hypothesis ML : model_laws (as_universe B).
Hypothesis TLF : PALibF B.
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IS___asan_memset).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Theorem pb_put_dec : tput_dec_spec.
Proof.
unfold tput_dec_spec.
intros STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc W memc mdc k regs b p n v mn
HJ Hra Hra4 Hgp Htp G10 G11 Hv32 Hvx G13 Hmn Hal32 Hwlo Hwhi Hroom Hp8 Hb0 Hn0 Hvp WRp WRd SRp SRd Hsep Hpside Hdside Hev.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hstk : PUT_DEC_STK = 4224) by reflexivity.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & J1 & J2 & J3 & J4 & Hgone & Hpres & Hstatic & J5 & HQT).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kc & Ku & Kg & Kgu).
rewrite (pal_got_shadow _ TL), (pal_cell _ TL) in Kg. rewrite (pal_cell _ TL) in Kc.
rewrite (palf_got_uar _ TLF) in Kgu.
pose proof (val_mem_of_rdword _ _ _ _ _ Kg) as Kgot.
pose proof (val_mem_of_rdword _ _ _ _ _ Kc) as Kcell.
pose proof (val_mem_of_rdword _ _ _ _ _ Kgu) as Kguar.
pose proof (val_mem_of_rd32 _ _ _ _ _ Ku) as Kuar.
pose proof (palf_uar_img _ TLF) as Huar. pose proof (palf_uar_al _ TLF) as Huar4.
pose proof (palf_sep _ TLF) as Hsep4.
pose proof (pa_obj_img 0 ltac:(lia)) as Hob0. pose proof (pa_obj_img 1 ltac:(lia)) as Hob1.
pose proof (pa_obj_img 30 ltac:(lia)) as Hob30.
assert (Hspsafe : alloc_ceiling + ESTACK + 128 <= spZ regs /\ spZ regs <= 2 ^ 47) by lia.
pose proof SRp as (SRp1 & SRpRA & SRpHull & SRpAMR & SRpLo & SRpHi).
pose proof SRd as (SRd1 & SRdRA & SRdHull & SRdAMR & SRdLo & SRdHi).
assert (HPapp : 4096 <= p /\ p + 8 <= 2 ^ 47 /\ (in_app p 8 \/ alloc_ceiling <= p)).
{ destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p HJ
(proj1 (WRp p ltac:(lia)))) as (_ & Hcases).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (p + 7) HJ
(proj1 (WRp (p + 7) ltac:(lia)))) as (_ & Hcases7).
unfold amem_range in SRpAMR.
pose proof (proj2 alloc_ceiling_value) as Hacm.
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Hacd. rewrite Hacm, Z.add_0_r in Hacd.
pose proof (Z.div_mod p 8 ltac:(lia)) as Hpd. rewrite Hp8, Z.add_0_r in Hpd.
unfold in_app, app_addr in *.
destruct Hcases as [[Hc _] | [[Ha _] | (cid2 & pos2 & _ & [[Ha _] | [Hk _]])]];
destruct Hcases7 as [[Hc7 _] | [[Ha7 _] | (cid7 & pos7 & _ & [[Ha7 _] | [Hk7 _]])]];
try unfold ASAN_CEIL in *; try unfold kLowMemEnd in *;
try unfold kHighMemEnd in *; try unfold kLowShadowBeg in *; try unfold kHighMemBeg in *;
try unfold kHighShadowEnd in *; lia. }
remember (Eimg (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EXx : forall j, (j < 2)%nat -> ew E (32 + j) =
nth j [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)] (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EXx 0%nat ltac:(lia)) as E32. pose proof (EXx 1%nat ltac:(lia)) as E33.
cbn [Nat.add nth] in E32, E33. clear EXx.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (as_uar_cell B)]) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall nn (q : bv 5), Z.of_nat nn = bv_unsigned q -> ew E nn = getr regs q)
by (intros nn q Hq; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hq).
assert (EO : forall q, (A_TEXT <= q < A_LIM)%nat -> ew E q = Z_to_bv 64 (VAL q))
by (intros q Hq; apply (img_env_atomP E q HEI Hq)).
assert (U2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); reflexivity).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = as_uar_cell B) by (rewrite E33; apply unsigned_lit_small; lia).
assert (UO : forall q, (A_TEXT <= q < A_LIM)%nat -> bv_unsigned (ew E q) = VAL q)
by (intros q Hq; rewrite (EO q Hq); apply unsigned_lit_small; apply pa_val_range).
assert (HS : st_ok_pi SEGS VAL E (mkSS AF_put_dec sr_atoms pd_emem None pd_efacts)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_put_dec)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx.
apply (pa_entry_st_ok_full E AF_put_dec sr_atoms regs pd_emem pd_efacts (mrestrict (w_H W) memc)).
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute; reflexivity.
- unfold pd_emem, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U2. split; [lia|]. split; [lia|]. split; [| apply Forall_nil].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (UO (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) (VAL (A_OBJ 1)) 0 8%N (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30))).
{ apply (pd_denot_atom E (A_OBJ 30) (VAL (A_OBJ 30)) (EO (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
pose proof (pa_val_range (A_OBJ 30)) as Hvr30. lia. }
{ change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). pose proof (pa_val_range (A_OBJ 30)). lia. }
{ change (Z.of_N 8) with 8. lia. }
{ rewrite Z.add_0_r. change (N.to_nat 8) with 8%nat. exact Kgot. }
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (UO (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) (VAL (A_OBJ 30)) 0 8%N (SOff 32 0) SHADOW_OFF);
[ apply (pd_denot_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia
| cbn; unfold SHADOW_OFF; lia | cbn; lia | rewrite Z.add_0_r; change (N.to_nat 8) with 8%nat; exact Kcell ].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite (UO (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) (VAL (A_OBJ 0)) 0 8%N (SOff 33 0) (as_uar_cell B));
first
[ apply (pd_denot_atom E 33 (as_uar_cell B) E33); lia
| cbn; lia | rewrite Z.add_0_r; change (N.to_nat 8) with 8%nat; exact Kguar ].
+ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [| apply Forall_nil].
apply (chunk_ok_val SEGS E (mrestrict (w_H W) memc) (as_uar_cell B) 0 4%N (SLit 1) 1);
first
[ reflexivity | cbn; lia | rewrite Z.add_0_r; change (N.to_nat 4) with 4%nat; exact Kuar ].
- unfold pd_emem, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
rewrite U2, U33, (UO (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)),
(UO (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)),
(UO (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
cbn [zseps zseps_from fst snd] in Hsep4. repeat split; lia.
- split; [| split; exact I].
unfold pd_efacts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite U2, U32, U33. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat split; unfold SHADOW_OFF;
try (rewrite <- Hal32; change (2 ^ 5) with 32; reflexivity);
try (change (2 ^ 2) with 4; exact Huar4); try lia. }
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H W) memc))
by (apply Forall_nil).
paj_run_tok RUN HS HJ SHOK Bspan.
{ unfold pd_emem. eapply (awr_ok_cons_stack_off E _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[reflexivity | rewrite U2; lia | cbn; lia | cbn; lia |].
repeat (apply awr_ok_cons_ro; [cbn; lia |]). apply awr_ok_nil. }
rename HFr into HFrE. rename HG into HGE.
lazymatch goal with |- SRr _ _ (mkCfg ?msE _) _ =>
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem msE) a = aview SEGS (w_H W) memc a) end.
{ intros a Ha Hw.
apply (kept_of_frame E _ (w_H W) memc _ (fun x => spZ regs - 128 <= x < spZ regs) HFrE); [| exact Ha | exact Hw].
intros bb wlo whi aa Hin Hr.
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Eq | Hin];
[injection Eq as <- <- <-; cbn [base_val] in Hr; try rewrite U2 in Hr; clear - Hr; lia |]).
destruct Hin. }
prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
pmkst HS.
rewrite (palf_sm0 B TLF).
pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ (ms_mem ?msY) _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msY)
STK sp0 FP ly Sa W0 mem0 md0 own lyc Sc _ k (spZ regs - 128 - sp0) _ HJ) end.
- unfold spZ at 1. rewrite R2, U2, (unsigned_lit_small (spZ regs + -128)) by lia. lia.
- pose proof (proj1 (Z.mod_divide (spZ regs) 32 ltac:(lia)) Hal32) as D32.
pose proof (proj1 (Z.mod_divide sp0 16 ltac:(lia)) Hsp0al) as D16.
destruct D32 as [q1 Hq1]. destruct D16 as [q2 Hq2].
apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). exists (2 * q1 - 8 - q2). lia.
- lia.
- rewrite Hes. lia.
- rewrite R3, (EE 3%nat (3%bv : bv 5) eq_refl). exact Hgp.
- rewrite R4, (EE 4%nat (4%bv : bv 5) eq_refl). exact Htp.
- exact R1.
- apply ret_ok_codeptr_v; [unfold AF_put_dec; lia | reflexivity].
- change (fs_frames 0) with 16384. lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJt2 & (fS2 & ES2)).
clear R1 R2 R3 R4.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HFal & HFhi & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR2 Hfin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as HFimg.
destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (HFLpres & HFLown & HFLrng).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
assert (HFq : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
assert (HF8 : F / 8 = 4 * (F / 32))
by (rewrite HFq at 1; replace (32 * (F / 32)) with (4 * (F / 32) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof HK as (K1 & K2 & K3 & K4 & K5 & K6).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U2; intros aa Haa;
  [ apply (mbyte_of_aview SEGS); apply K1; unfold ESTACK in *; lia
  | apply writable_kept; intros Hp; apply K5; [unfold ESTACK in *; lia | unfold ESTACK in *; lia | exact Hp] ]
| specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2.
clear HEI. rename HEI2 into HEI.
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF. fold F in RF.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 528 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] HS
ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
pose proof (img_env_havoc_hi _ 528%nat [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] HEI ltac:(cbv; lia)) as HEI3.
clear HEI. rename HEI3 into HEI.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (E528 : ew Ev 528 = Z_to_bv 64 FL)
by (exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E529 : ew Ev 529 = Z_to_bv 64 (SHADOW_OFF + F / 8))
by (exact (ew_havoc_new _ 528 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)));
assert (E32b : ew Ev 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E32);
assert (E516 : ew Ev 516 = Z_to_bv 64 F) by (rewrite ew_havoc_old by lia; exact RF) end.
assert (HFLlo : 4096 <= FL < 140737479966720) by (unfold ASAN_CEIL in *; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_fact Ev _ _ 516 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E516, unsigned_lit_small by lia;
change (2 ^ 5) with 32; lia)) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 528 (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite E528, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_fact Ev _ _ 529 (mkAF (SHADOW_OFF + 512) (SHADOW_OFF + 17592186044416) 2) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E529, unsigned_lit_small by (unfold SHADOW_OFF; lia);
change (2 ^ 2) with 4; unfold SHADOW_OFF;
split; [lia|]; split; [rewrite HF8; replace (2147450880 + 4 * (F / 32)) with ((536862720 + F / 32) * 4) by lia;
apply Z_mod_mult | lia])) as HS3; clear HS; rename HS3 into HS;
pose proof (st_ok_pi_add_alias Ev _ _ _ _ HS
(shadow_decl_ok Ev 516 32 529 F SHADOW_OFF E516 ltac:(lia) E32b E529)) as HS3;
clear HS; rename HS3 into HS end.
assert (ZS : val_mem SEGS (mrestrict (w_H W) mem2) (SHADOW_OFF + F / 8) 8 0).
{ apply val_mem_zero8. intros ii Hii. unfold zero_shadow, shadow_of_addr in Hz.
apply Hz. change (64 / 8) with 8. lia. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
rewrite E516, unsigned_lit_small by lia; split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ F 56 8%N (SOff 528 0) FL);
[ apply (pd_denot_atom Ev 528 FL E528); lia
| cbn; lia | cbn; lia
| change (N.to_nat 8) with 8%nat; replace (F + 56) with (F + 64 - 8) by lia;
exact (val_mem_of_rdword SEGS _ _ _ _ Hflag) ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite E516; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite U2;
rewrite (unsigned_lit_small F) by (clear - HF4096 HFceil C1; lia);
repeat split; try (clear - HFceil HF4096 Hspsafe Hes C1; unfold ESTACK in *; lia))) as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _
(fshadow_region 529 0 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok, fshadow_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
change (fs_frame_bytes 0 / 8) with 8;
rewrite E529, unsigned_lit_small by (clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia);
split; [clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia|];
split; [clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia|];
split;
[ intros o Ho; apply (apresent_writable SEGS); unfold shadow_addr in HFSpres;
apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; clear - Ho; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ (SHADOW_OFF + F / 8) 0 8%N (SLit 0) 0);
[ reflexivity | cbn; clear; lia | cbn; clear; lia
| change (N.to_nat 8) with 8%nat; rewrite Z.add_0_r; exact ZS ] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint, fshadow_region;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
change (fs_frame_bytes 0 / 8) with 8;
rewrite E529, E516; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite U2;
rewrite (unsigned_lit_small F) by (clear - HF4096 HFceil C1; lia);
rewrite (unsigned_lit_small (SHADOW_OFF + F / 8)) by (clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia);
repeat split;
try (clear - HFceil HF4096 Hspsafe Hes C1 HF8lo HF8hi HFq HF8 HFapp;
unfold ESTACK, SHADOW_OFF, in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)))
as HS3; clear HS; rename HS3 into HS end.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (SHOK2 : sh_ok SEGS (SOff 32 0) (@nil shent) Ev (mrestrict (w_H W) mem2)) by (apply Forall_nil) end.
paj_run_to_sh RUNTOP HS HJ2 (AF_put_dec + 288).
{ lazymatch goal with |- awr_ok ?Ev _ _ _ _ _ _ _ _ =>
eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 529%nat (SHADOW_OFF + F / 8));
[ reflexivity
| rewrite E529; apply unsigned_lit_small; clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia
| cbn [fshadow_region YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
  exists 0, pos; split; [left; reflexivity|]; right;
  unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 0 / 8) with 8;
  fold F; clear - Ha; lia
| ];
eapply (awr_ok_cons_gen Ev _ _ _ _ _ _ _ _ _ 516%nat F);
[ reflexivity
| rewrite E516; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; right; right; right;
  exists 0, pos; split; [left; reflexivity|]; left;
  unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; fold F; clear - Ha; lia
| ];
eapply (awr_ok_cons_stack_off Ev _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
[ reflexivity
| try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite U2; clear; lia
| cbn; clear - Hwlo Hstk Hes; lia
| cbn; clear - Hwhi; lia
| apply awr_ok_nil ] end. }
rename HFr into HFrS. rename HG into HGS.
lazymatch goal with |- SRr _ _ (mkCfg ?msS _) _ =>
assert (KS : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 <= a < spZ regs) -> ~ (F <= a < F + 64) ->
~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) ->
aview SEGS (w_H W) (ms_mem msS) a = aview SEGS (w_H W) mem2 a) end.
{ intros a Ha Hw1 Hw2 Hw3.
apply (kept_of_frame _ _ (w_H W) mem2 _
(fun x => (spZ regs - 128 <= x < spZ regs) \/ (F <= x < F + 64) \/ (SHADOW_OFF + F / 8 <= x < SHADOW_OFF + F / 8 + 8)) HFrS);
[| exact Ha | intros [Hq | [Hq | Hq]]; [exact (Hw1 Hq) | exact (Hw2 Hq) | exact (Hw3 Hq)]].
intros bb wlo whi aa Hin Hr.
lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In (bb, wlo, whi) l') in Hin end.
cbn [In] in Hin.
repeat (destruct Hin as [Eq | Hin];
[injection Eq as <- <- <-; cbn [base_val] in Hr;
 try (rewrite E529 in Hr; rewrite unsigned_lit_small in Hr by (clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia));
 try (rewrite E516 in Hr; rewrite unsigned_lit_small in Hr by (clear - HF4096 HFceil C1; lia));
 try (rewrite ew_havoc_old in Hr by lia; rewrite ew_havoc_old in Hr by lia; rewrite U2 in Hr);
 clear - Hr; lia |]).
destruct Hin. }
lazymatch goal with |- SRr _ _ (mkCfg ?msD _) _ =>
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssD _ =>
pose proof (st_ok_pi_region_nth Ev ssD (restrict (w_H W) msD) 0%nat _ HS eq_refl) as HROs;
cbn [ms_mem restrict] in HROs;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msD)) 529%nat (SHADOW_OFF + F / 8)
  _ 0 8 0 8 4 1%N (SLit 0) HROs
  ltac:(rewrite E529; apply unsigned_lit_small; clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia)
  ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as HSH4;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msD)) 529%nat (SHADOW_OFF + F / 8)
  _ 0 8 0 8 5 1%N (SLit 2) HROs
  ltac:(rewrite E529; apply unsigned_lit_small; clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia)
  ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as HSH5
end end.
lazymatch goal with |- SRr _ _ (mkCfg ?msD _) _ =>
assert (HRAd : range_addressable (aview SEGS (w_H W) (ms_mem msD)) SHADOW_OFF (F + 32) 10) end.
{ intros xx Hxx.
assert (Hq : 8 * (F / 8) = F) by (clear - HFq HF8; lia).
destruct (Z.lt_ge_cases xx (F + 40)) as [Hlo | Hhi].
- exists 0. split; [| left; reflexivity].
unfold shadow_of_addr. replace (SHADOW_OFF + xx / 8) with (SHADOW_OFF + F / 8 + 4)
by (clear - Hxx Hlo Hq; assert (xx / 8 = F / 8 + 4) by (symmetry; apply Z.div_unique_pos with (r := xx - F - 32); lia); lia).
apply aview_of_val_mem1; [exact HSH4 | clear; lia].
- exists 2. split; [| right; split; [| lia]].
+ unfold shadow_of_addr. replace (SHADOW_OFF + xx / 8) with (SHADOW_OFF + F / 8 + 5)
by (clear - Hxx Hhi Hq; assert (xx / 8 = F / 8 + 5) by (symmetry; apply Z.div_unique_pos with (r := xx - F - 40); lia); lia).
apply aview_of_val_mem1; [exact HSH5 | clear; lia].
+ clear - Hxx Hhi Hq HFq. assert (xx = 8 * (F / 8) + 40 \/ xx = 8 * (F / 8) + 41) by lia.
assert (Hm : (8 * (F / 8) + 40) mod 8 = 0) by (replace (8 * (F / 8) + 40) with ((F / 8 + 5) * 8) by lia; apply Z_mod_mult).
assert (Hm1 : (8 * (F / 8) + 41) mod 8 = 1)
by (replace (8 * (F / 8) + 41) with ((F / 8 + 5) * 8 + 1) by lia; rewrite Z.add_comm, Z.mod_add by lia; reflexivity).
destruct H as [-> | ->]; lia. }
prreg HS (11%bv : bv 5) D11. prreg HS (12%bv : bv 5) D12. prreg HS (13%bv : bv 5) D13.
prreg HS (14%bv : bv 5) D14. prreg HS (22%bv : bv 5) D22. prreg HS (23%bv : bv 5) D23.
prreg HS (26%bv : bv 5) D26. prreg HS (2%bv : bv 5) D2. prreg HS (3%bv : bv 5) D3.
prreg HS (4%bv : bv 5) D4. prreg HS (19%bv : bv 5) D19. prreg HS (21%bv : bv 5) D21.
prreg HS (20%bv : bv 5) D20. prreg HS (8%bv : bv 5) D8. prreg HS (9%bv : bv 5) D9.
prreg HS (18%bv : bv 5) D18. prreg HS (24%bv : bv 5) D24. prreg HS (25%bv : bv 5) D25. prreg HS (27%bv : bv 5) D27.
pose proof HS as HSd. pmkst HS.
assert (HRv : 0 <= bv_unsigned (getr regs 12) < 2 ^ 64)
by (pose proof (bv_unsigned_in_range 64 (getr regs 12)) as Hq;
change (bv_modulus 64) with (2 ^ 64) in Hq; clear - Hq; lia).
assert (HTapp : in_app (F + 32) 10)
by (clear - HFapp HF4096 HFceil; unfold in_app, app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msD) _ (ms_mem ?msE) _) ?mdD) _ =>
eapply (pd_dloop 10%nat (bv_unsigned (getr regs 12)) v 0 (F + 32) (@nil byte) W (ms_regs msD) (ms_mem msE) mdD
STK sp0 FP ly Sa W0 mem0 md0 ((0, pos) :: own) lyc S2 k) end.
- clear; lia.
- exact HRv.
- exact Hv32.
- exact Hvx.
- clear - Hv32 HRv. change (10 ^ Z.of_nat 10) with 10000000000.
pose proof (Z.mod_pos_bound (bv_unsigned (getr regs 12)) (2 ^ 32) ltac:(lia)). lia.
- reflexivity.
- pose proof (ds_lsb_length 10 v) as Hdl. cbn [length]. clear - Hdl. lia.
- clear - HF4096; lia.
- clear - HFceil; lia.
- exact HTapp.
- exact HJ2.
- intros a Ha. right; right; right. exists 0, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. clear - Ha. lia.
- exact HRAd.
- rewrite D11. reflexivity.
- rewrite D12. reflexivity.
- rewrite D13. reflexivity.
- rewrite D14. reflexivity.
- rewrite D22. try (rewrite ew_havoc_old by lia). try (rewrite ew_havoc_old by lia).
rewrite (EE 12%nat (12%bv : bv 5) eq_refl). symmetry. apply Z_to_bv_bv_unsigned.
- rewrite D23. try (rewrite ew_havoc_old by lia). try (rewrite ew_havoc_old by lia). exact E32.
- rewrite D26. cbn [nth map CLOB]. rewrite Ha0. unfold w64.
rewrite (unsigned_lit_small F) by (clear - HF4096 HFceil C1; lia). reflexivity.
- intros j Hj. cbn [map length] in Hj. clear - Hj; lia. }
cbv beta.
intros W3 c3 _ (-> & regsD & memD & mdD & HcD & HJD & RD11 & HKD & HGD & HKEPTD & HPRESD).
pose proof (ds_lsb_length 10 v) as Hdl10.
assert (Hdpos : (1 <= length (ds_lsb 10 v))%nat) by (cbn [ds_lsb length]; clear; lia).
rewrite HcD.
destruct HPapp as (HP4096 & HP47 & HPor).
eapply SRr_bind.
{ eapply (pd_pad B LAWS AMEMSET (Z.of_nat (length (ds_lsb 10 v))) mn (F + 32) p (spZ regs - 128 - sp0)
(ds_lsb 10 v) W regsD memD mdD STK sp0 FP ly Sa W0 mem0 md0 ((0, pos) :: own) lyc S2 k).
- clear - Hdl10 Hdpos; lia.
- exact Hmn.
- reflexivity.
- clear - HF4096; lia.
- clear - HFceil; lia.
- exact HTapp.
- exact Hp8.
- destruct HPor as [Hpi | Hpc]; [left; exact Hpi | right; split; [exact Hpc | exact HP47]].
- unfold spZ. rewrite (HKD (2%bv : bv 5) ltac:(cbv; reflexivity)), D2.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite U2.
rewrite (unsigned_lit_small (spZ regs + -128)) by (clear - Hspsafe C1 Hes; unfold ESTACK in *; lia).
unfold spZ. clear; lia.
- pose proof (proj1 (Z.mod_divide (spZ regs) 32 ltac:(lia)) Hal32) as D32.
pose proof (proj1 (Z.mod_divide sp0 16 ltac:(lia)) Hsp0al) as D16.
destruct D32 as [q1 Hq1]. destruct D16 as [q2 Hq2].
apply (proj2 (Z.mod_divide _ 16 ltac:(lia))). exists (2 * q1 - 8 - q2). clear - Hq1 Hq2; lia.
- clear - Hwhi; lia.
- clear - Hwlo Hstk Hes; lia.
- rewrite (HKD (3%bv : bv 5) ltac:(cbv; reflexivity)), D3.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia).
rewrite (EE 3%nat (3%bv : bv 5) eq_refl). exact Hgp.
- rewrite (HKD (4%bv : bv 5) ltac:(cbv; reflexivity)), D4.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia).
rewrite (EE 4%nat (4%bv : bv 5) eq_refl). exact Htp.
- rewrite RD11. reflexivity.
- rewrite (HKD (19%bv : bv 5) ltac:(cbv; reflexivity)), D19.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia).
rewrite (EE 11%nat (11%bv : bv 5) eq_refl). exact G11.
- rewrite (HKD (21%bv : bv 5) ltac:(cbv; reflexivity)), D21.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia).
rewrite (EE 13%nat (13%bv : bv 5) eq_refl). exact G13.
- rewrite (HKD (23%bv : bv 5) ltac:(cbv; reflexivity)), D23.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia). exact E32.
- rewrite (HKD (26%bv : bv 5) ltac:(cbv; reflexivity)), D26.
cbn [nth map CLOB]. rewrite Ha0. unfold w64.
rewrite (unsigned_lit_small F) by (clear - HF4096 HFceil C1; lia). reflexivity.
- exact HJD.
- intros a Ha. right; right; right. exists 0, pos. split; [left; reflexivity|]. left.
unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. clear - Ha. lia.
- intros xx Hxx. destruct (HRAd xx Hxx) as (ss & Hs & Hok). exists ss. split; [| exact Hok].
rewrite <- Hs. destruct (pd_shadow_out (F + 32) 10 xx HTapp Hxx) as [Hs1 Hs2].
apply HKEPTD; [exact Hs1 | exact Hs2].
- eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc S2 W memD mdD 0 pos); [exact (proj1 HJD) | exact Hfin2 | | | clear; lia].
+ fold F. clear; lia.
+ change (fs_frame_bytes 0) with 64. fold F. clear; lia.
- exact HGD. }
cbv beta.
intros W4 c4 _ (-> & regsP & memP & mdP & HcP & HJP & RP10 & RP13 & RP12 & RP14 & RP21 & HKP & HGP & HKEPTP & HPRESP).
assert (HspD : spZ regsD = spZ regs - 128).
{ unfold spZ. rewrite (HKD (2%bv : bv 5) ltac:(cbv; reflexivity)), D2.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite U2.
rewrite (unsigned_lit_small (spZ regs + -128)) by (clear - Hspsafe C1 Hes; unfold ESTACK in *; lia).
unfold spZ. lia. }
assert (KPM : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 - ESTACK <= a < spZ regs) ->
~ (F <= a < F + 64) -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) ->
aview SEGS (w_H W) memP a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hw1 Hw2 Hw3.
rewrite (HKEPTP a Ha ltac:(clear - Hw2; lia) ltac:(rewrite HspD; clear - Hw1; lia)).
rewrite (HKEPTD a Ha ltac:(clear - Hw2; lia)).
exact (KS a Ha ltac:(clear - Hw1 Hes; unfold ESTACK in *; lia) Hw2 Hw3). }
pose proof HJP as (HARP & Hlyc0 & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
assert (HSTKlo : ly_stk_lo lyc + STK <= sp0 /\ sp0 <= ly_stk_hi lyc).
{ clear - Hstatic Hlyc0. destruct Hstatic as (_ & _ & _ & Hl & Hh & _).
destruct Hlyc0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & El & Eh & _). rewrite El, Eh. split; lia. }
destruct HSTKlo as (HSTKlo & HSTKhi).
assert (HOUT : forall a, awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a ->
~ (F <= a < F + 64) /\ ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8)).
{ intros a Hw.
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (_ & Hcases).
destruct Hcases as [[Hc Hsw0] | [[Happ (bb & mm & Hinb & Hrb & _)] | (cid2 & ps2 & Hinown & Hzz)]].
- split; clear - Hc HFceil HF8lo HF8hi C1; unfold SHADOW_OFF in *; lia.
- destruct (al_blocks SEGS B LAWS lyc S2 W memP mdP bb mm HARP ltac:(rewrite Eab; exact Hinb)) as (_ & Hb4096 & Hbceil & Hbapp2 & _).
pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 bb mm 0 pos HAR2
ltac:(rewrite Eab; exact Hinb) Hfin2) as Hdbf.
unfold zdisjoint in Hdbf. cbn [fst snd] in Hdbf. fold F in Hdbf.
change (fs_frame_bytes 0) with 64 in Hdbf.
split; [clear - Hdbf Hrb; lia |].
assert (Hq8 : 8 * (F / 8) = F) by (clear - HFq HF8; lia).
unfold app_addr, kLowShadowBeg, kHighMemBeg in Happ.
destruct Happ as (Ha4096 & [Hlow | (Hhigh & _)]).
+ clear - Hlow Hq8 HF4096. unfold SHADOW_OFF. lia.
+ clear - Hhigh Hq8 HFceil C1 HF4096. unfold SHADOW_OFF. lia.
- destruct (in_split (cid2, ps2) own Hinown) as (l1 & l2 & Esplit).
assert (Hfr2 : frames S2 = [] ++ (0, pos) :: l1 ++ (cid2, ps2) :: (l2 ++ frames Sa)).
{ rewrite Hfrsc, Esplit. cbn [app]. rewrite <- app_assoc. reflexivity. }
assert (Hzz2 : in_zr a (frame_rng lyc (cid2, ps2)) \/
in_zr a (shadow_addr (frame_addr lyc cid2 ps2), fs_frame_bytes cid2 / 8))
by (destruct Hzz as [[_ Hq] | [_ Hq]]; [left | right]; exact Hq).
split; intros Hin0;
[ exact (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid2, ps2) [] l1 (l2 ++ frames Sa) a
  HAR2 Hfr2 ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold F;
  change (fs_frame_bytes 0) with 64; clear - Hin0; lia) Hzz2)
| exact (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid2, ps2) [] l1 (l2 ++ frames Sa) a
  HAR2 Hfr2 ltac:(right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F;
  change (fs_frame_bytes 0 / 8) with 8; clear - Hin0; lia) Hzz2) ]. }
assert (HRAP : forall q nn, 0 <= q -> q + nn <= 2 ^ 47 ->
(forall a, q <= a < q + nn -> awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a) ->
(forall a, q <= a < q + nn -> ~ (spZ regs - 128 - ESTACK <= a < spZ regs)) ->
amem_range q nn ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q nn ->
range_addressable (aview SEGS (w_H W) memP) SHADOW_OFF q nn).
{ intros q nn Hq0 Hq1 Hwr Hside HAMRq Hrac x Hx.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HARP))) as (_ & _ & _ & _ & Hpal & Hpah & _).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x HJ (Hwr x Hx)) as (_ & Hcases).
destruct Hcases as [[Hc Hstkw] | [[Happ (bb & mm & Hinb & Hrb & _)] | (cid2 & ps2 & Hinown & Hzz)]].
- exists 0. split; [| left; reflexivity].
pose proof (al_zshadow _ _ LAWS _ _ _ _ _ (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
HARP ltac:(left; reflexivity)) as Hzst. cbn [fst snd] in Hzst.
assert (Hlo8 : ly_stk_lo lyc mod 8 = 0) by exact (pd_mod4096_mod8 _ Hpal).
assert (Hhi8 : ly_stk_hi lyc mod 8 = 0) by exact (pd_mod4096_mod8 _ Hpah).
assert (Hlen8 : (ly_stk_hi lyc - ly_stk_lo lyc) mod 8 = 0).
{ clear - Hlo8 Hhi8.
pose proof (proj1 (Z.mod_divide (ly_stk_hi lyc) 8 ltac:(lia)) Hhi8) as (q1 & Hq1).
pose proof (proj1 (Z.mod_divide (ly_stk_lo lyc) 8 ltac:(lia)) Hlo8) as (q2 & Hq2).
apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exists (q1 - q2). lia. }
exact (pd_zs_byte _ (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) x Hzst Hlo8 Hlen8
ltac:(clear - Hstkw HSTKlo HSTKhi; lia)).
- exact (range_addressable_of_block SEGS B LAWS _ _ _ _ _ bb mm x 1 HARP
ltac:(rewrite Eab; exact Hinb) ltac:(clear - Hrb; lia) ltac:(clear - Hrb; lia) x ltac:(clear; lia)).
- destruct (Hrac x Hx) as (sv0 & Hsv & Hok). exists sv0. split; [| exact Hok].
destruct (HOUT x (Hwr x Hx)) as (HO1 & HO2).
assert (Hd8 : 8 * (x / 8) <= x /\ x < 8 * (x / 8) + 8 /\ 0 <= x / 8 /\ x / 8 <= x).
{ clear - Hx Hq0. pose proof (Z.div_mod x 8 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Dr.
split; [lia | split; [lia | split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]]]. }
assert (HFd8 : 8 * (F / 8) = F /\ F / 8 = 4 * (F / 32)) by (clear - HFq HF8; lia).
rewrite <- Hsv.
rewrite (KPM (shadow_of_addr SHADOW_OFF x)
ltac:(unfold shadow_of_addr, SHADOW_OFF in *; clear - Hd8 Hq0 Hq1 Hx C1; lia)
ltac:(unfold shadow_of_addr, SHADOW_OFF in *;
clear - Hd8 Hq0 Hq1 Hx Hspsafe Hes C1; unfold ESTACK in *; lia)
ltac:(unfold shadow_of_addr, SHADOW_OFF in *; clear - Hd8 Hx Hq0 Hq1 HFapp HF4096 HFceil C1;
unfold in_app, kLowShadowBeg, kHighMemBeg in *; lia)
ltac:(unfold shadow_of_addr, SHADOW_OFF in *; clear - Hd8 HFd8 HO1; lia)).
assert (Hin2 : In (cid2, ps2) (frames S2))
by (rewrite Hfrsc; apply in_or_app; left; right; exact Hinown).
destruct (frame_al64 SEGS B lyc S2 W memP mdP cid2 ps2 HARP Hin2) as (Hfa64 & Hfs64 & Hfs0).
assert (Hfa8 : 8 * (frame_addr lyc cid2 ps2 / 8) = frame_addr lyc cid2 ps2).
{ clear - Hfa64. pose proof (proj1 (Z.mod_divide _ 64 ltac:(lia)) Hfa64) as (qq & Hqq).
pose proof (Z.div_mod (frame_addr lyc cid2 ps2) 8 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (frame_addr lyc cid2 ps2) 8 ltac:(lia)) as Dr.
assert (Hm8 : frame_addr lyc cid2 ps2 mod 8 = 0)
by (rewrite Hqq; replace (qq * 64) with ((qq * 8) * 8) by lia; apply Z_mod_mult). lia. }
assert (Hfs8 : 8 * (fs_frame_bytes cid2 / 8) = fs_frame_bytes cid2).
{ clear - Hfs64. pose proof (proj1 (Z.mod_divide _ 64 ltac:(lia)) Hfs64) as (qq & Hqq).
pose proof (Z.div_mod (fs_frame_bytes cid2) 8 ltac:(lia)) as Dq.
pose proof (Z.mod_pos_bound (fs_frame_bytes cid2) 8 ltac:(lia)) as Dr.
assert (Hm8 : fs_frame_bytes cid2 mod 8 = 0)
by (rewrite Hqq; replace (qq * 64) with ((qq * 8) * 8) by lia; apply Z_mod_mult). lia. }
rewrite (K4 cid2 ps2 (shadow_of_addr SHADOW_OFF x)
ltac:(rewrite Hfrs; apply in_or_app; left; exact Hinown)
ltac:(destruct Hzz as [[_ Hz1] | [Hz1 _]];
[ right; unfold in_zr, frame_rng, shadow_of_addr, shadow_addr in *; cbn [fst snd] in *;
  clear - Hz1 Hd8 Hfa8 Hfs8; lia
| exfalso; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, kHighShadowEnd in *;
  clear - Hz1 HAMRq Hx; lia ])
ltac:(clear; tauto)).
apply KE; [unfold shadow_of_addr, SHADOW_OFF; clear - Hd8 Hq0 Hq1 Hx C1; lia |].
unfold shadow_of_addr, SHADOW_OFF.
clear - Hd8 Hq0 Hq1 Hx Hspsafe Hes C1; unfold ESTACK in *; lia. }
assert (HBYTE : forall a, awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a ->
0 <= a < 2 ^ 64 -> ~ (spZ regs - 128 - ESTACK <= a < spZ regs) ->
aview SEGS (w_H W) memP a = aview SEGS (w_H W) memc a).
{ intros a Hw Ha Hside.
destruct (HOUT a Hw) as (HO1 & HO2).
rewrite (KPM a Ha Hside HO1 HO2).
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (_ & Hcases).
destruct Hcases as [[Hc Hstkw] | [[Happ (bb & mm & Hinb & Hrb & _)] | (cid2 & ps2 & Hinown & Hzz)]].
- rewrite (K1 a ltac:(clear - Hc Ha; lia) ltac:(clear - Hside Hes; unfold ESTACK in *; lia)).
apply KE; [exact Ha | clear - Hside Hes; unfold ESTACK in *; lia].
- replace a with (bb + (a - bb)) by (clear; lia).
rewrite (K2 bb mm (a - bb) Hinb ltac:(clear - Hrb; lia) ltac:(clear; tauto)).
replace (bb + (a - bb)) with a by (clear; lia).
apply KE; [exact Ha | clear - Hside Hes; unfold ESTACK in *; lia].
- rewrite (K4 cid2 ps2 a ltac:(rewrite Hfrs; apply in_or_app; left; exact Hinown)
ltac:(destruct Hzz as [[_ Hz1] | [_ Hz1]]; [left; exact Hz1 | right; exact Hz1]) ltac:(clear; tauto)).
apply KE; [exact Ha | clear - Hside Hes; unfold ESTACK in *; lia]. }
assert (HvpP : val_mem SEGS (mrestrict (w_H W) memP) p 8 n).
{ eapply (val_mem_kept SEGS (w_H W) (w_H W) memc memP p 8); [| exact Hvp].
intros kq Hkq. first [apply HBYTE | symmetry; apply HBYTE].
- exact (proj1 (WRp (p + kq) ltac:(clear - Hkq; lia))).
- clear - Hkq HP4096 HP47. lia.
- clear - Hkq Hpside Hstk Hes. unfold PUT_DEC_STK, ESTACK in *. lia. }
assert (Hv32b : 0 <= v < 2 ^ 32)
by (rewrite <- Hv32; apply Z.mod_pos_bound; clear; lia).
pose proof (pd_dec_rev v mn Hv32b ltac:(clear - Hmn; lia)) as (Hdecrev & Hdeclen).
set (K := Z.of_nat (length (ds_lsb 10 v))) in *.
set (Kmax := Z.max K mn) in *.
assert (HKm : 1 <= Kmax <= 10) by (clear - Hdl10 Hdpos Hmn; unfold Kmax, K; lia).
assert (HdecK : dec_len v mn = Kmax) by (rewrite Hdeclen; unfold Kmax, K; clear; lia).
assert (HTr : forall x, F + 32 <= x < F + 32 + Kmax -> F + 32 <= x < F + 32 + 10)
by (clear - HKm; lia).
assert (HDbnd : forall a, awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a ->
4096 <= a /\ a < 2 ^ 47).
{ intros a Hw.
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (_ & Hcs).
destruct Hcs as [[Hc1 Hs1] | [[Ha1 _] | (c1 & q1 & _ & [[Ha1 _] | [Hk1 _]])]].
- clear - Hc1 Hs1 Hstatic C1. destruct Hstatic as (_ & _ & _ & _ & Hh & H47 & _). lia.
- clear - Ha1 C1. unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- clear - Ha1 C1. unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
- clear - Hk1 C1. unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (HDapp : 4096 <= b + n /\ b + n + dec_len v mn <= 2 ^ 47).
{ destruct (HDbnd (b + n) (proj1 (WRd (b + n) ltac:(clear - HdecK HKm; lia)))) as (Q1 & Q2).
destruct (HDbnd (b + n + dec_len v mn - 1)
(proj1 (WRd (b + n + dec_len v mn - 1) ltac:(clear - HdecK HKm; lia)))) as (Q3 & Q4).
clear - Q1 Q2 Q3 Q4 HdecK HKm. lia. }
assert (HRAsrc : range_addressable (aview SEGS (w_H W) memP) SHADOW_OFF (F + 32) 10).
{ intros xx Hxx. destruct (HRAd xx Hxx) as (ss & Hs & Hok). exists ss. split; [| exact Hok].
rewrite <- Hs. destruct (pd_shadow_out (F + 32) 10 xx HTapp Hxx) as (Hs1 & Hs2).
assert (Hxx0 : 0 <= xx) by (clear - Hxx HF4096; lia).
assert (Hxx1 : xx <= alloc_ceiling) by (clear - Hxx HFceil; lia).
pose proof (pd_shadow_lt_ceil xx Hxx0 Hxx1) as Hslt.
rewrite (HKEPTP (shadow_of_addr SHADOW_OFF xx) Hs1 Hs2
ltac:(rewrite HspD; clear - Hslt Hspsafe Hes; unfold ESTACK in *; lia)).
apply HKEPTD; [exact Hs1 | exact Hs2]. }
assert (HRAp : range_addressable (aview SEGS (w_H W) memP) SHADOW_OFF p 8).
{ apply (HRAP p 8); [clear - HP4096; lia | clear - HP47; lia
| intros a Ha; exact (proj1 (WRp a Ha))
| intros a Ha; clear - Ha Hpside Hstk Hes; unfold PUT_DEC_STK, ESTACK in *; lia
| exact SRpAMR | exact SRpRA]. }
assert (HRAdst : range_addressable (aview SEGS (w_H W) memP) SHADOW_OFF (b + n) (dec_len v mn)).
{ apply (HRAP (b + n) (dec_len v mn)); [clear - Hb0 Hn0; lia | clear - HDapp; lia
| intros a Ha; exact (proj1 (WRd a Ha))
| intros a Ha; clear - Ha Hdside Hstk Hes; unfold PUT_DEC_STK, ESTACK in *; lia
| exact SRdAMR | exact SRdRA]. }
assert (HSHp : aview SEGS (w_H W) memP (SHADOW_OFF + p / 8) = Some 0).
{ destruct (HRAp (p + 7) ltac:(clear; lia)) as (ss & Hs & Hok).
assert (Hdiv : (p + 7) / 8 = p / 8).
{ clear - Hp8. pose proof (Z.div_mod p 8 ltac:(lia)) as Dq. rewrite Hp8, Z.add_0_r in Dq.
symmetry. apply (Z.div_unique (p + 7) 8 (p / 8) 7); lia. }
unfold shadow_of_addr in Hs. rewrite Hdiv in Hs. rewrite Hs. f_equal.
destruct Hok as [-> | (Hm & Hlt)]; [reflexivity|].
exfalso. clear - Hm Hlt Hp8.
pose proof (Z.div_mod p 8 ltac:(lia)) as Dq. rewrite Hp8, Z.add_0_r in Dq.
assert (Hmm : (p + 7) mod 8 = 7) by (rewrite Dq; replace (8 * (p / 8) + 7) with (7 + (p / 8) * 8) by lia;
rewrite Z.mod_add by lia; reflexivity). lia. }
set (PL := ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat mn - length (ds_lsb 10 v))) in *.
assert (HPLlen : Z.of_nat (length PL) = Kmax)
by (unfold PL; rewrite length_app, repeat_length; unfold Kmax, K; clear - Hdl10 Hdpos Hmn; lia).
assert (HGPL : garr8 SEGS (mrestrict (w_H W) memP) (F + 32) (map bv_unsigned PL)).
{ unfold PL. replace (Z.to_nat mn - length (ds_lsb 10 v))%nat with (Z.to_nat (Kmax - K))
by (unfold Kmax, K; clear - Hdl10 Hdpos Hmn; lia). exact HGP. }
assert (Hsrcb : forall j, (j < Z.to_nat Kmax)%nat ->
val_mem SEGS (mrestrict (w_H W) memP) (F + 32 + Kmax - 1 - Z.of_nat j) 1
(bv_unsigned (nth j (rev PL) (Z_to_bv 8 0)))).
{ intros j Hj.
replace (F + 32 + Kmax - 1 - Z.of_nat j) with (F + 32 + Z.of_nat (length PL) - 1 - Z.of_nat j)
by (rewrite HPLlen; clear; lia).
exact (pd_src_rev memP (w_H W) (F + 32) PL j HGPL ltac:(clear - Hj HPLlen HKm; lia)). }
assert (Hdisj_sd : F + 32 + Kmax <= b + n \/ b + n + Kmax <= F + 32).
{ destruct (Z.le_gt_cases (F + 32 + Kmax) (b + n)) as [H1 | H1]; [left; exact H1 |].
destruct (Z.le_gt_cases (b + n + Kmax) (F + 32)) as [H2 | H2]; [right; exact H2 |].
exfalso.
destruct (HOUT (Z.max (b + n) (F + 32))
(proj1 (WRd (Z.max (b + n) (F + 32)) ltac:(clear - H1 H2 HKm HdecK; lia)))) as (HO1 & _).
apply HO1. clear - H1 H2 HKm. lia. }
assert (Hdisj_sp : p + 8 <= F + 32 \/ F + 32 + Kmax <= p).
{ destruct (Z.le_gt_cases (p + 8) (F + 32)) as [H1 | H1]; [left; exact H1 |].
destruct (Z.le_gt_cases (F + 32 + Kmax) p) as [H2 | H2]; [right; exact H2 |].
exfalso.
destruct (HOUT (Z.max p (F + 32))
(proj1 (WRp (Z.max p (F + 32)) ltac:(clear - H1 H2 HKm; lia)))) as (HO1 & _).
apply HO1. clear - H1 H2 HKm. lia. }
rewrite HcP.
eapply SRr_bind.
{ eapply (pd_rloop (Z.to_nat Kmax) (F + 32 + Kmax - 1) n b p (rev PL) W regsP memP mdP
STK sp0 FP ly Sa W0 mem0 md0 ((0, pos) :: own) lyc S2 k).
- clear - HKm; lia.
- rewrite length_rev. clear - HPLlen HKm; lia.
- exact Hn0.
- clear - HDapp HdecK HKm Hb0 Hn0; lia.
- clear - HDapp HdecK HKm Hb0 Hn0; lia.
- clear - HDapp HdecK HKm Hb0 Hn0; lia.
- intros a Ha.
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ
(proj1 (WRd a ltac:(clear - Ha HdecK HKm; lia)))) as (_ & Hcs).
destruct Hcs as [[Hc1 _] | [[Ha1 _] | (c1 & q1 & _ & [[Ha1 _] | [Hk1 _]])]].
+ right. exact Hc1.
+ left. unfold in_app, app_addr in *. clear - Ha1. lia.
+ left. unfold in_app, app_addr in *. clear - Ha1. lia.
+ exfalso. unfold amem_range in SRdAMR.
unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg, kHighMemEnd in *.
clear - Hk1 SRdAMR Ha HdecK HKm. lia.
- exact Hb0.
- exact HP4096.
- clear - HP47; lia.
- exact Hp8.
- exact HPor.
- clear - HF4096 HKm; lia.
- clear - HFceil HKm; lia.
- eapply in_app_sub; [exact HTapp | clear - HKm; lia | clear - HKm; lia | clear - HKm; lia].
- destruct Hsep as [Hs1 | Hs2]; [left; clear - Hs1 HdecK HKm; lia | right; clear - Hs2 HdecK HKm; lia].
- destruct Hdisj_sd as [H1 | H1]; [left; clear - H1 HKm; lia | right; clear - H1 HKm; lia].
- destruct Hdisj_sp as [H1 | H1]; [right; clear - H1 HKm; lia | left; clear - H1 HKm; lia].
- exact HJP.
- intros a Ha. rewrite Eab. apply pd_awr_mono. exact (proj1 (WRp a Ha)).
- intros a Ha. rewrite Eab. apply pd_awr_mono. exact (proj1 (WRd a ltac:(clear - Ha HdecK HKm; lia))).
- exact HRAp.
- replace (Z.of_nat (Z.to_nat Kmax)) with (dec_len v mn) by (rewrite HdecK; clear - HKm; lia).
exact HRAdst.
- replace (F + 32 + Kmax - 1 - Z.of_nat (Z.to_nat Kmax) + 1) with (F + 32) by (clear - HKm; lia).
eapply range_addressable_sub; [exact HRAsrc | clear; lia | clear - HKm; lia].
- exact HSHp.
- exact HvpP.
- intros j Hj. exact (Hsrcb j Hj).
- exact RP10.
- rewrite RP12. f_equal. clear - HKm; lia.
- exact RP13.
- exact RP14.
- change (getr regsP 19) with (getr regsP (Z_to_bv 5 19)).
rewrite (HKP 19 ltac:(unfold acallee_saved; clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
change (getr regsD (Z_to_bv 5 19)) with (getr regsD 19).
rewrite (HKD (19%bv : bv 5) ltac:(cbv; reflexivity)), D19.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia).
rewrite (EE 11%nat (11%bv : bv 5) eq_refl). exact G11.
- change (getr regsP 20) with (getr regsP (Z_to_bv 5 20)).
rewrite (HKP 20 ltac:(unfold acallee_saved; clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
change (getr regsD (Z_to_bv 5 20)) with (getr regsD 20).
rewrite (HKD (20%bv : bv 5) ltac:(cbv; reflexivity)), D20.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia).
rewrite (EE 10%nat (10%bv : bv 5) eq_refl). exact G10.
- change (getr regsP 23) with (getr regsP (Z_to_bv 5 23)).
rewrite (HKP 23 ltac:(unfold acallee_saved; clear; lia) ltac:(clear; lia) ltac:(clear; lia)).
change (getr regsD (Z_to_bv 5 23)) with (getr regsD 23).
rewrite (HKD (23%bv : bv 5) ltac:(cbv; reflexivity)), D23.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia). exact E32. }
cbv beta.
intros W5 c5 _ (-> & regsR & memR & mdR & HcR & HJR & HKR & HVPR & HGDR & HKEPTR & HPRESR).
lazymatch type of HSd with st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msS) =>
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) msS) 2%nat _ HSd eq_refl) as HROstk;
cbn [ms_mem restrict] in HROstk;
pose proof (st_ok_pi_region_nth Ev ssx (restrict (w_H W) msS) 1%nat _ HSd eq_refl) as HROfr;
cbn [ms_mem restrict] in HROfr;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 516%nat F _ 0 64 0 64 56 8%N (SOff 528 0)
  HROfr ltac:(rewrite E516; apply unsigned_lit_small; clear - HF4096 HFceil C1; lia)
  ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as HFLv;
assert (HU2s : bv_unsigned (ew Ev 2) = spZ regs)
by (rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact U2);
assert (KR : forall a, spZ regs - 128 <= a < spZ regs ->
aview SEGS (w_H W) memR a = aview SEGS (w_H W) (ms_mem msS) a);
[ intros a Ha;
  rewrite (HKEPTR a ltac:(clear - Ha Hspsafe C1 Hes; unfold ESTACK in *; lia)
    ltac:(clear - Ha Hpside Hstk Hes; unfold PUT_DEC_STK, ESTACK in *; lia)
    ltac:(rewrite <- HdecK in *; clear - Ha Hdside Hstk Hes HKm; unfold PUT_DEC_STK, ESTACK in *; lia));
  rewrite (HKEPTP a ltac:(clear - Ha Hspsafe C1 Hes; unfold ESTACK in *; lia) ltac:(clear - Ha HFceil Hspsafe Hes; unfold ESTACK in *; lia)
    ltac:(rewrite HspD; clear - Ha; lia));
  exact (HKEPTD a ltac:(clear - Ha Hspsafe C1 Hes; unfold ESTACK in *; lia) ltac:(clear - Ha HFceil Hspsafe Hes; unfold ESTACK in *; lia))
| ];
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-8) 8%N (SOff 1 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr1;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-16) 8%N (SOff 8 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr8;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-24) 8%N (SOff 9 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr9;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-32) 8%N (SOff 18 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr18;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-40) 8%N (SOff 19 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr19;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-48) 8%N (SOff 20 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr20;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-56) 8%N (SOff 21 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr21;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-64) 8%N (SOff 22 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr22;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-72) 8%N (SOff 23 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr23;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-80) 8%N (SOff 24 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr24;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-88) 8%N (SOff 25 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr25;
pose proof (field_of_region_any Ev (mrestrict (w_H W) (ms_mem msS)) 2%nat (spZ regs) _ (-128) 0 (-128) 0 (-96) 8%N (SOff 26 0)
  HROstk HU2s ltac:(cbn [In]; tauto) ltac:(cbn; clear; lia)) as SVr26;
idtac end.
cbn [sv_denot] in SVr1. change (N.to_nat 8) with 8%nat in SVr1.
rewrite ew_havoc_old in SVr1 by lia. rewrite ew_havoc_old in SVr1 by lia.
rewrite (EE 1%nat (1%bv : bv 5) eq_refl) in SVr1. rewrite pd_sv_val in SVr1.
assert (SV1 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 120) 8 (bv_unsigned (getr regs 1))).
{ replace (spZ regs - 128 + 120) with (spZ regs + (-8)) by (clear; lia).
  lazymatch type of SVr1 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-8)) 8); [| exact SVr1] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr8. change (N.to_nat 8) with 8%nat in SVr8.
rewrite ew_havoc_old in SVr8 by lia. rewrite ew_havoc_old in SVr8 by lia.
rewrite (EE 8%nat (8%bv : bv 5) eq_refl) in SVr8. rewrite pd_sv_val in SVr8.
assert (SV8 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 112) 8 (bv_unsigned (getr regs 8))).
{ replace (spZ regs - 128 + 112) with (spZ regs + (-16)) by (clear; lia).
  lazymatch type of SVr8 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-16)) 8); [| exact SVr8] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr9. change (N.to_nat 8) with 8%nat in SVr9.
rewrite ew_havoc_old in SVr9 by lia. rewrite ew_havoc_old in SVr9 by lia.
rewrite (EE 9%nat (9%bv : bv 5) eq_refl) in SVr9. rewrite pd_sv_val in SVr9.
assert (SV9 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 104) 8 (bv_unsigned (getr regs 9))).
{ replace (spZ regs - 128 + 104) with (spZ regs + (-24)) by (clear; lia).
  lazymatch type of SVr9 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-24)) 8); [| exact SVr9] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr18. change (N.to_nat 8) with 8%nat in SVr18.
rewrite ew_havoc_old in SVr18 by lia. rewrite ew_havoc_old in SVr18 by lia.
rewrite (EE 18%nat (18%bv : bv 5) eq_refl) in SVr18. rewrite pd_sv_val in SVr18.
assert (SV18 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 96) 8 (bv_unsigned (getr regs 18))).
{ replace (spZ regs - 128 + 96) with (spZ regs + (-32)) by (clear; lia).
  lazymatch type of SVr18 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-32)) 8); [| exact SVr18] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr19. change (N.to_nat 8) with 8%nat in SVr19.
rewrite ew_havoc_old in SVr19 by lia. rewrite ew_havoc_old in SVr19 by lia.
rewrite (EE 19%nat (19%bv : bv 5) eq_refl) in SVr19. rewrite pd_sv_val in SVr19.
assert (SV19 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 88) 8 (bv_unsigned (getr regs 19))).
{ replace (spZ regs - 128 + 88) with (spZ regs + (-40)) by (clear; lia).
  lazymatch type of SVr19 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-40)) 8); [| exact SVr19] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr20. change (N.to_nat 8) with 8%nat in SVr20.
rewrite ew_havoc_old in SVr20 by lia. rewrite ew_havoc_old in SVr20 by lia.
rewrite (EE 20%nat (20%bv : bv 5) eq_refl) in SVr20. rewrite pd_sv_val in SVr20.
assert (SV20 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 80) 8 (bv_unsigned (getr regs 20))).
{ replace (spZ regs - 128 + 80) with (spZ regs + (-48)) by (clear; lia).
  lazymatch type of SVr20 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-48)) 8); [| exact SVr20] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr21. change (N.to_nat 8) with 8%nat in SVr21.
rewrite ew_havoc_old in SVr21 by lia. rewrite ew_havoc_old in SVr21 by lia.
rewrite (EE 21%nat (21%bv : bv 5) eq_refl) in SVr21. rewrite pd_sv_val in SVr21.
assert (SV21 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 72) 8 (bv_unsigned (getr regs 21))).
{ replace (spZ regs - 128 + 72) with (spZ regs + (-56)) by (clear; lia).
  lazymatch type of SVr21 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-56)) 8); [| exact SVr21] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr22. change (N.to_nat 8) with 8%nat in SVr22.
rewrite ew_havoc_old in SVr22 by lia. rewrite ew_havoc_old in SVr22 by lia.
rewrite (EE 22%nat (22%bv : bv 5) eq_refl) in SVr22. rewrite pd_sv_val in SVr22.
assert (SV22 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 64) 8 (bv_unsigned (getr regs 22))).
{ replace (spZ regs - 128 + 64) with (spZ regs + (-64)) by (clear; lia).
  lazymatch type of SVr22 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-64)) 8); [| exact SVr22] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr23. change (N.to_nat 8) with 8%nat in SVr23.
rewrite ew_havoc_old in SVr23 by lia. rewrite ew_havoc_old in SVr23 by lia.
rewrite (EE 23%nat (23%bv : bv 5) eq_refl) in SVr23. rewrite pd_sv_val in SVr23.
assert (SV23 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 56) 8 (bv_unsigned (getr regs 23))).
{ replace (spZ regs - 128 + 56) with (spZ regs + (-72)) by (clear; lia).
  lazymatch type of SVr23 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-72)) 8); [| exact SVr23] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr24. change (N.to_nat 8) with 8%nat in SVr24.
rewrite ew_havoc_old in SVr24 by lia. rewrite ew_havoc_old in SVr24 by lia.
rewrite (EE 24%nat (24%bv : bv 5) eq_refl) in SVr24. rewrite pd_sv_val in SVr24.
assert (SV24 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 48) 8 (bv_unsigned (getr regs 24))).
{ replace (spZ regs - 128 + 48) with (spZ regs + (-80)) by (clear; lia).
  lazymatch type of SVr24 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-80)) 8); [| exact SVr24] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr25. change (N.to_nat 8) with 8%nat in SVr25.
rewrite ew_havoc_old in SVr25 by lia. rewrite ew_havoc_old in SVr25 by lia.
rewrite (EE 25%nat (25%bv : bv 5) eq_refl) in SVr25. rewrite pd_sv_val in SVr25.
assert (SV25 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 40) 8 (bv_unsigned (getr regs 25))).
{ replace (spZ regs - 128 + 40) with (spZ regs + (-88)) by (clear; lia).
  lazymatch type of SVr25 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-88)) 8); [| exact SVr25] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in SVr26. change (N.to_nat 8) with 8%nat in SVr26.
rewrite ew_havoc_old in SVr26 by lia. rewrite ew_havoc_old in SVr26 by lia.
rewrite (EE 26%nat (26%bv : bv 5) eq_refl) in SVr26. rewrite pd_sv_val in SVr26.
assert (SV26 : val_mem SEGS (mrestrict (w_H W) memR) (spZ regs - 128 + 32) 8 (bv_unsigned (getr regs 26))).
{ replace (spZ regs - 128 + 32) with (spZ regs + (-96)) by (clear; lia).
  lazymatch type of SVr26 with val_mem _ (mrestrict _ ?mS) _ _ _ =>
  eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (spZ regs + (-96)) 8); [| exact SVr26] end.
  intros kq Hkq. first [symmetry; apply KR | apply KR]; clear - Hkq; lia. }
cbn [sv_denot] in HFLv. change (N.to_nat 8) with 8%nat in HFLv.
rewrite E528 in HFLv.
replace (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 FL) + 0)) mod 2 ^ (8 * Z.of_N 8)) with FL in HFLv
by (rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (unsigned_lit_small FL) by (clear - HFLlo; lia);
change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); symmetry; apply Z.mod_small; clear - HFLlo; lia).
assert (HFLR : rdword (aview SEGS (w_H W) memR) (F + 56) = Some FL).
{ apply rdword_of_val_mem; [| clear - HFLlo; lia].
lazymatch type of HFLv with val_mem _ (mrestrict _ ?mS) _ _ _ =>
eapply (val_mem_kept SEGS (w_H W) (w_H W) mS memR (F + 56) 8); [| exact HFLv] end.
intros kq Hkq.
assert (Hq1 : ~ (p <= F + 56 + kq < p + 8)).
{ intros Hin. destruct (HOUT (F + 56 + kq) (proj1 (WRp (F + 56 + kq) Hin))) as (HO1 & _).
apply HO1. clear - Hkq. lia. }
assert (Hq2 : ~ (b + n <= F + 56 + kq < b + n + Z.of_nat (Z.to_nat Kmax))).
{ intros Hin. destruct (HOUT (F + 56 + kq) (proj1 (WRd (F + 56 + kq) ltac:(rewrite HdecK; clear - Hin HKm; lia)))) as (HO1 & _).
apply HO1. clear - Hkq. lia. }
first [symmetry | idtac].
rewrite (HKEPTR (F + 56 + kq) ltac:(clear - Hkq HF4096 HFceil C1; lia) Hq1 Hq2).
rewrite (HKEPTP (F + 56 + kq) ltac:(clear - Hkq HF4096 HFceil C1; lia) ltac:(clear - Hkq; lia)
ltac:(rewrite HspD; clear - Hkq HFceil Hspsafe Hes; unfold ESTACK in *; lia)).
first [reflexivity | exact (HKEPTD (F + 56 + kq) ltac:(clear - Hkq HF4096 HFceil C1; lia) ltac:(clear - Hkq; lia))
| symmetry; exact (HKEPTD (F + 56 + kq) ltac:(clear - Hkq HF4096 HFceil C1; lia) ltac:(clear - Hkq; lia))]. }
idtac "FLOK".
rewrite HcR.
eapply SRr_bind.
{ eapply (pd_epi B LAWS ML ASF FFL F FL (spZ regs) pos W regsR regs memR mdR STK sp0 FP ly Sa W0 mem0 md0 own lyc S2 k).
- change (getr regsR 2) with (getr regsR (Z_to_bv 5 2)). pd_chain HKR HKP HKD 2.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 2)] => change (getr X (Z_to_bv 5 2)) with (getr X 2) end. rewrite D2.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); try rewrite U2;
first [reflexivity | (cbn [sv_denot]; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 2%nat (2%bv : bv 5) eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; f_equal; lia) | (f_equal; lia) | (unfold spZ; f_equal; lia)].
- change (getr regsR 8) with (getr regsR (Z_to_bv 5 8)). pd_chain HKR HKP HKD 8.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 8)] => change (getr X (Z_to_bv 5 8)) with (getr X 8) end. rewrite D8.
first [reflexivity | (cbn [sv_denot]; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 2%nat (2%bv : bv 5) eq_refl); unfold spZ; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) | (try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 2%nat (2%bv : bv 5) eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned)].
- change (getr regsR 9) with (getr regsR (Z_to_bv 5 9)). pd_chain HKR HKP HKD 9.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 9)] => change (getr X (Z_to_bv 5 9)) with (getr X 9) end. rewrite D9.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); try rewrite U2;
first [reflexivity | (cbn [sv_denot]; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 2%nat (2%bv : bv 5) eq_refl); unfold spZ; rewrite Z_to_bv_bv_unsigned; f_equal; lia) | (f_equal; lia) | (unfold spZ; f_equal; lia)].
- change (getr regsR 18) with (getr regsR (Z_to_bv 5 18)). pd_chain HKR HKP HKD 18.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 18)] => change (getr X (Z_to_bv 5 18)) with (getr X 18) end. rewrite D18.
first [ (cbn [nth map CLOB]; rewrite Ha0; reflexivity) | (cbn [sv_denot]; cbn [nth map CLOB]; rewrite Ha0; unfold w64; rewrite Z.add_0_r, (unsigned_lit_small F) by (clear - HF4096 HFceil C1; lia); reflexivity) ].
- change (getr regsR 24) with (getr regsR (Z_to_bv 5 24)). pd_chain HKR HKP HKD 24.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 24)] => change (getr X (Z_to_bv 5 24)) with (getr X 24) end. rewrite D24.
first [ (cbn [nth map CLOB]; rewrite Ha0; reflexivity) | (cbn [sv_denot]; cbn [nth map CLOB]; rewrite Ha0; unfold w64; rewrite Z.add_0_r, (unsigned_lit_small F) by (clear - HF4096 HFceil C1; lia); reflexivity) ].
- change (getr regsR 23) with (getr regsR (Z_to_bv 5 23)). pd_chain HKR HKP HKD 23.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 23)] => change (getr X (Z_to_bv 5 23)) with (getr X 23) end. rewrite D23.
try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia). exact E32.
- change (getr regsR 25) with (getr regsR (Z_to_bv 5 25)). pd_chain HKR HKP HKD 25.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 25)] => change (getr X (Z_to_bv 5 25)) with (getr X 25) end. rewrite D25.
first [ exact E529 | (cbn [sv_denot]; rewrite E529, Z.add_0_r, unsigned_lit_small by (clear - HF8lo HF8hi C1; unfold SHADOW_OFF; lia); reflexivity) ].
- change (getr regsR 3) with (getr regsR (Z_to_bv 5 3)). pd_chain HKR HKP HKD 3.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 3)] => change (getr X (Z_to_bv 5 3)) with (getr X 3) end. rewrite D3.
first [ (try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); exact (EE 3%nat (3%bv : bv 5) eq_refl)) | (cbn [sv_denot]; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 3%nat (3%bv : bv 5) eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned) ].
- change (getr regsR 4) with (getr regsR (Z_to_bv 5 4)). pd_chain HKR HKP HKD 4.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 4)] => change (getr X (Z_to_bv 5 4)) with (getr X 4) end. rewrite D4.
first [ (try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); exact (EE 4%nat (4%bv : bv 5) eq_refl)) | (cbn [sv_denot]; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 4%nat (4%bv : bv 5) eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned) ].
- change (getr regsR 27) with (getr regsR (Z_to_bv 5 27)). pd_chain HKR HKP HKD 27.
lazymatch goal with |- context [getr ?X (Z_to_bv 5 27)] => change (getr X (Z_to_bv 5 27)) with (getr X 27) end. rewrite D27.
first [ (try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); exact (EE 27%nat (27%bv : bv 5) eq_refl)) | (cbn [sv_denot]; try (rewrite ew_havoc_old by lia); try (rewrite ew_havoc_old by lia); rewrite (EE 27%nat (27%bv : bv 5) eq_refl), Z.add_0_r; apply Z_to_bv_bv_unsigned) ].
- unfold spZ. symmetry. apply Z_to_bv_bv_unsigned.
- exact Hra.
- clear - Hwlo Hstk Hes. unfold PUT_DEC_STK, ESTACK in *. lia.
- exact Hwhi.
- exact HJR.
- reflexivity.
- reflexivity.
- exact HFLR.
- exact SV1.
- exact SV8.
- exact SV9.
- exact SV18.
- exact SV19.
- exact SV20.
- exact SV21.
- exact SV22.
- exact SV23.
- exact SV24.
- exact SV25.
- exact SV26. }
cbv beta.
intros W6 c6 _ (-> & regsE & memE & mdE & HcE & HJE & HPE & HfrE & HabE & HnevE & HKEPTE & HPRESE).
idtac "AFTEREPI".
assert (KPOST : forall a, 0 <= a < 2 ^ 64 ->
~ (spZ regs - PUT_DEC_STK <= a < spZ regs) ->
~ (F <= a < F + 64) -> ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) -> a <> FL ->
~ (p <= a < p + 8) -> ~ (b + n <= a < b + n + dec_len v mn) ->
aview SEGS (w_H W) memE a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hw Hf Hfs Hfl Hp Hd.
rewrite (HKEPTE a Ha ltac:(clear - Hw Hstk Hes; unfold PUT_DEC_STK, ESTACK in *; lia) Hf Hfs Hfl).
rewrite (HKEPTR a Ha Hp ltac:(rewrite <- HdecK in *; clear - Hd HKm HdecK; lia)).
exact (KPM a Ha ltac:(clear - Hw Hes; unfold PUT_DEC_STK, ESTACK in *; lia) Hf Hfs). }
destruct (al_flag SEGS B LAWS lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (_ & HFLow & _ & HFLcl).
fold FL in HFLow, HFLcl.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTAT0 & _).
destruct HSTAT0 as (_ & _ & HSceil & HSlo & _).
assert (HNFL : forall a, awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a -> a <> FL).
{ intros a Hw Eq. rewrite Eq in Hw. clear Eq a.
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FL HJ Hw) as (_ & Hcases).
destruct Hcases as [[Hc _] | [[Happ (bb & mm & Hinb & Hrb & _)] | (cid2 & ps2 & Hinown & Hzz)]].
- clear - Hc HFLcl HSceil HSlo. lia.
- destruct (al_blocks SEGS B LAWS lyc S2 W mem2 md2 bb mm HAR2 ltac:(rewrite Eab; exact Hinb))
as (_ & _ & _ & _ & Hbp & _).
exact (proj2 (Hbp FL Hrb) HFLow).
- assert (Hin2 : In (cid2, ps2) (frames S2))
by (rewrite Hfrsc; right; apply in_or_app; left; exact Hinown).
destruct (al_frames SEGS B LAWS lyc S2 W mem2 md2 cid2 ps2 HAR2 Hin2) as (_ & _ & HFp & HFSp).
destruct Hzz as [[_ Hq] | [_ Hq]]; unfold in_zr, frame_rng in Hq; cbn [fst snd] in Hq.
+ exact (proj2 (HFp FL ltac:(clear - Hq; lia)) HFLow).
+ refine (proj2 (HFSp (FL - shadow_addr (frame_addr lyc cid2 ps2)) ltac:(clear - Hq; lia)) _).
replace (shadow_addr (frame_addr lyc cid2 ps2) + (FL - shadow_addr (frame_addr lyc cid2 ps2))) with FL
by (clear; lia). exact HFLow. }
assert (HNIMG : forall a, awr_byte STK sp0 FP (ablocks B ly Sa) (ablocks B lyc Sc) lyc own a ->
in_img SEGS a -> False).
{ intros a Hw Himg. pose proof (Hsegs a Himg) as Hlow0.
destruct (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (_ & Hcases).
destruct Hcases as [[Hc _] | [[Happ (bb & mm & Hinb & Hrb & _)] | (cid2 & ps2 & Hinown & Hzz)]].
- clear - Hc Hlow0 HSceil HSlo C1. unfold kLowMemEnd in *. lia.
- refine (proj2 (al_client_img SEGS B LAWS lyc S2 W mem2 md2 a HAR2 _) Himg).
left. exists bb, mm. split; [rewrite Eab; exact Hinb | exact Hrb].
- assert (Hin2 : In (cid2, ps2) (frames S2))
by (rewrite Hfrsc; right; apply in_or_app; left; exact Hinown).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 cid2 ps2 HAR2 Hin2) as (Hc0 & Hc1 & _).
destruct Hzz as [[_ Hq] | [_ Hq]]; unfold in_zr, frame_rng in Hq; cbn [fst snd] in Hq.
+ refine (proj2 (al_client_img SEGS B LAWS lyc S2 W mem2 md2 a HAR2 _) Himg).
right; left. exists cid2, ps2. split; [exact Hin2 | clear - Hq; lia].
+ pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid2 ps2)
ltac:(clear - Hc0 Hc1 C1; pose proof (fs_frame_bytes_nonneg cid2); unfold kHighMemEnd; lia)) as Hsb2.
unfold shadow_addr in Hq, Hsb2. clear - Hq Hsb2 Hlow0. unfold kLowMemEnd in *. lia. }
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (_ & _ & HFapp0).
destruct (al_frames SEGS B LAWS lyc S2 W mem2 md2 0 pos HAR2 Hfin2) as (HFal0 & _ & _ & _).
change (fs_frame_bytes 0) with 64 in HFapp0. fold F in HFapp0, HFal0.
apply SRr_ret. unfold tput_dec_post.
exists lyc, (stack_free_state 0 pos S2), regsE, memE, mdE.
split; [exact HcE|].
split; [eapply ajournal_mono_k; [exact HJE | unfold EV_PUT_DEC; clear; lia]|].
split; [exact HPE|].
split; [rewrite Hfrs2 in HfrE; injection HfrE as HfrE; exact HfrE|].
split; [rewrite HabE; exact Eab|].
split.
{ eapply (pd_tcj_of_parts B LAWS PUT_DEC_STK lyc Sc W memc W memE (spZ regs) _ F).
- intros a Ha Hw HEx Hf Hfs.
rewrite (KPOST a ltac:(clear - Ha C1; lia) Hw Hf Hfs
ltac:(clear - Ha HFLcl; lia) ltac:(clear - HEx; tauto) ltac:(clear - HEx; tauto)).
rewrite (proj1 HK a ltac:(clear - Ha C1; lia)
ltac:(clear - Hw Hes; unfold PUT_DEC_STK, ESTACK in *; lia)).
exact (KE a ltac:(clear - Ha C1; lia)
ltac:(clear - Hw Hes; unfold PUT_DEC_STK, ESTACK in *; lia)).
- intros bb mm i Hinb Hi HEx.
destruct (al_blocks SEGS B LAWS lyc S2 W mem2 md2 bb mm HAR2 ltac:(rewrite Eab; exact Hinb))
as (_ & Hb4096 & Hbceil & _ & Hbp & _).
assert (Hnf : ~ (F <= bb + i < F + 64)).
{ intros Hin0. refine (block_not_frame_zone SEGS B LAWS lyc S2 W mem2 md2 bb mm i 0 pos HAR2
ltac:(rewrite Eab; exact Hinb) Hfin2 Hi _). left.
unfold in_zr, frame_rng. cbn [fst snd]. fold F. change (fs_frame_bytes 0) with 64. clear - Hin0; lia. }
assert (Hns : ~ (SHADOW_OFF + F / 8 <= bb + i < SHADOW_OFF + F / 8 + 8)).
{ intros Hin0. refine (block_not_frame_zone SEGS B LAWS lyc S2 W mem2 md2 bb mm i 0 pos HAR2
ltac:(rewrite Eab; exact Hinb) Hfin2 Hi _). right.
unfold in_zr, shadow_addr. cbn [fst snd]. fold F. change (fs_frame_bytes 0 / 8) with 8.
clear - Hin0; lia. }
rewrite (KPOST (bb + i) ltac:(clear - Hb4096 Hbceil Hi C1; lia)
ltac:(clear - Hb4096 Hbceil Hi Hspsafe Hes; unfold PUT_DEC_STK, ESTACK in *; lia)
Hnf Hns ltac:(intros Eqf; pose proof HFLow as HFLo2; rewrite <- Eqf in HFLo2;
exact (proj2 (Hbp (bb + i) ltac:(clear - Hi; lia)) HFLo2))
ltac:(clear - HEx; tauto) ltac:(clear - HEx; tauto)).
rewrite (proj1 (proj2 HK) bb mm i Hinb Hi ltac:(intros [])).
exact (KE (bb + i) ltac:(clear - Hb4096 Hbceil Hi C1; lia)
ltac:(clear - Hb4096 Hbceil Hi Hspsafe Hes; unfold PUT_DEC_STK, ESTACK in *; lia)).
- intros a Hi Hns He.
pose proof (Hsegs a Hi) as Hlow.
assert (Hnf : ~ (F <= a < F + 64)).
{ intros Hin0. refine (proj2 (al_client_img SEGS B LAWS lyc S2 W mem2 md2 a HAR2 _) Hi).
right; left. exists 0, pos. split; [exact Hfin2|]. fold F. change (fs_frame_bytes 0) with 64.
clear - Hin0; lia. }
assert (Hnfl : a <> FL).
{ intros ->. refine (proj2 (al_client_img SEGS B LAWS lyc S2 W mem2 md2 FL HAR2 _) Hi).
right; right. exists 0, pos. split; [exact Hfin2 | reflexivity]. }
pose proof (YCbq.shadow_addr_bounds F ltac:(clear - HF4096 HFceil C1; unfold kHighMemEnd; lia)) as Hsb.
unfold shadow_addr in Hsb.
rewrite (KPOST a ltac:(clear - Hlow C1; unfold kLowMemEnd in *; lia)
ltac:(clear - Hlow C1 Hspsafe Hes; unfold kLowMemEnd, PUT_DEC_STK, ESTACK in *; lia)
Hnf ltac:(clear - Hlow Hsb C1; unfold kLowMemEnd in *; lia) Hnfl
ltac:(intros Hc; exact (HNIMG a (proj1 (WRp a Hc)) Hi))
ltac:(intros Hc; exact (HNIMG a (proj1 (WRd a Hc)) Hi))).
rewrite (proj1 (proj2 (proj2 HK)) a Hi Hns He).
exact (KE a ltac:(clear - Hlow C1; unfold kLowMemEnd in *; lia)
ltac:(clear - Hlow C1 Hspsafe Hes; unfold kLowMemEnd, PUT_DEC_STK, ESTACK in *; lia)).
- intros cid ps a Hin Hr HEx.
assert (Hin2 : In (cid, ps) (frames S2)) by (rewrite Hfrs2; right; exact Hin).
destruct (frame_zone SEGS B LAWS lyc S2 W mem2 md2 cid ps a HAR2 Hin2 Hr) as (Hac & Hcs).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 cid ps HAR2 Hin2) as (Hcf0 & Hcfc & _).
assert (Hab0 : 0 <= a < 2 ^ 64)
by (destruct Hcs as [(Hr1 & _) | Hr2]; [clear - Hr1 Hcf0 Hcfc C1; lia
| clear - Hr2 C1; unfold kLowMemEnd, kHighShadowEnd in *; lia]).
destruct (in_split (cid, ps) (frames Sc) Hin) as (m1 & m2 & Esp).
assert (Hfr2 : frames S2 = [] ++ (0, pos) :: m1 ++ (cid, ps) :: m2)
by (rewrite Hfrs2, Esp; reflexivity).
assert (Hnf : ~ (F <= a < F + 64) /\ ~ (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8)).
{ split; intros Hin0;
[ exact (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid, ps) [] m1 m2 a HAR2 Hfr2
ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold F;
change (fs_frame_bytes 0) with 64; clear - Hin0; lia) Hr)
| exact (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid, ps) [] m1 m2 a HAR2 Hfr2
ltac:(right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F;
change (fs_frame_bytes 0 / 8) with 8; clear - Hin0; lia) Hr) ]. }
assert (Hnfl : a <> FL).
{ destruct (al_frames SEGS B LAWS lyc S2 W mem2 md2 cid ps HAR2 Hin2) as (_ & _ & HFp & HFSp).
destruct Hr as [Hq | Hq]; unfold in_zr, frame_rng in Hq; cbn [fst snd] in Hq; intros ->.
- exact (proj2 (HFp FL ltac:(clear - Hq; lia)) HFLow).
- refine (proj2 (HFSp (FL - shadow_addr (frame_addr lyc cid ps)) ltac:(clear - Hq; lia)) _).
replace (shadow_addr (frame_addr lyc cid ps) + (FL - shadow_addr (frame_addr lyc cid ps))) with FL
by (clear; lia). exact HFLow. }
rewrite (KPOST a Hab0 ltac:(clear - Hac Hspsafe Hes; unfold PUT_DEC_STK, ESTACK in *; lia)
(proj1 Hnf) (proj2 Hnf) Hnfl ltac:(clear - HEx; tauto) ltac:(clear - HEx; tauto)).
rewrite (proj1 (proj2 (proj2 (proj2 HK))) cid ps a Hin Hr ltac:(intros [])).
exact (KE a Hab0 ltac:(clear - Hac Hspsafe Hes; unfold PUT_DEC_STK, ESTACK in *; lia)).
- intros a Ha Hw Hp.
apply HPRESE. apply HPRESR. apply HPRESP. apply HPRESD.
eapply apresent_grows; [exact HGS|].
apply (proj1 (proj2 (proj2 (proj2 (proj2 HK)))) a Ha
ltac:(clear - Hw Hes; unfold PUT_DEC_STK, ESTACK in *; lia)).
eapply apresent_grows; [exact HGE|]. exact Hp.
- intros a Ha.
pose proof HJE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresE & _).
apply HpresE. clear - Ha Hwlo Hwhi Hes. unfold PUT_DEC_STK, ESTACK in *. lia.
- clear - HF4096; lia.
- clear - HFceil; lia.
- exact HFapp0.
- exact HFal0.
- intros a Ha1 Ha2. clear - Ha1 Ha2 HFceil. lia. }
split.
{ rewrite Hdecrev.
eapply (garr8_frame SEGS (mrestrict (w_H W) memR)); [exact HGDR|].
intros a Ha. rewrite length_map, length_rev, HPLlen in Ha.
apply mbyte_of_aview.
apply (HKEPTE a ltac:(clear - Ha HDapp HdecK HKm Hb0 Hn0; lia)
ltac:(clear - Ha Hdside HdecK HPLlen Hes; unfold PUT_DEC_STK, ESTACK in *; lia)
(proj1 (HOUT a (proj1 (WRd a ltac:(clear - Ha HdecK HPLlen; lia)))))
(proj2 (HOUT a (proj1 (WRd a ltac:(clear - Ha HdecK HPLlen; lia)))))
(HNFL a (proj1 (WRd a ltac:(clear - Ha HdecK HPLlen; lia))))). }
{ rewrite HdecK, <- (Z2Nat.id Kmax ltac:(clear - HKm; lia)).
eapply (val_mem_kept SEGS (w_H W) (w_H W) memR memE p 8); [| exact HVPR].
intros kk Hkz.
apply (HKEPTE (p + kk) ltac:(clear - Hkz HP4096 HP47; lia)
ltac:(clear - Hkz Hpside Hes; unfold PUT_DEC_STK, ESTACK in *; lia)
(proj1 (HOUT (p + kk) (proj1 (WRp (p + kk) ltac:(clear - Hkz; lia)))))
(proj2 (HOUT (p + kk) (proj1 (WRp (p + kk) ltac:(clear - Hkz; lia)))))
(HNFL (p + kk) (proj1 (WRp (p + kk) ltac:(clear - Hkz; lia))))). }
Qed.



End e.
End d.
End b.
