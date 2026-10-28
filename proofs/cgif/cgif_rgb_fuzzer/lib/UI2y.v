(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m
YI00 YI02 YI01 YI03 YI04 YI5a UI1e UI2m UI26 UI2r
UI2s UI36 UI38 UI34.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma t2_x_U : forall E n s K c1 m2, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c1 = 2 * K -> m2 = -2 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m2)) (SLit c1)) = 2 * (K - s).
Proof.
intros E n s K c1 m2 Hn Hs HK -> ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_SLit _ (-2)), (U_atom _ n s Hn), (U_lit _ (2 * K)) by lia.
change (zcanon (-2)) with 18446744073709551614. unfold zcanon, M64.
rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551614 + 2 * K) with (2 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma t2_y_U : forall E n s K c2, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c2 = - K ->
U E (SAlu ALU_SUB (SLit 0) (SOff n c2)) = K - s.
Proof.
intros E n s K c2 Hn Hs HK ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, (U_lit _ 0), Hn, unsigned_lit_small by lia. unfold zcanon, M64.
rewrite Zminus_mod_idemp_r. replace (0 - (s + - K)) with (K - s) by lia. apply Z.mod_small. lia.
Qed.
Lemma t2_z_U : forall E n s K c3 m3, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c3 = 3 * K -> m3 = 18446744073709551613 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m3)) (SLit c3)) = 3 * (K - s).
Proof.
intros E n s K c3 m3 Hn Hs HK -> ->.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom _ n s Hn), !U_lit by lia. unfold zcanon, M64.
rewrite Zplus_mod_idemp_l. replace (s * 18446744073709551613 + 3 * K) with (3 * (K - s) + s * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma t2_chk_ne : forall E n s K c1 c2 c3 m2 m3, ew E n = Z_to_bv 64 s -> 1 <= s <= K -> K <= 256 ->
c1 = 2 * K -> c2 = - K -> c3 = 3 * K -> m2 = -2 -> m3 = 18446744073709551613 ->
negb (U E (SAluw ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m2)) (SLit c1)) (SAlu ALU_SUB (SLit 0) (SOff n c2))) =?
U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m3)) (SLit c3))) = false.
Proof.
intros E n s K c1 c2 c3 m2 m3 Hn Hs HK H1 H2 H3 H4 H5.
rewrite (t2_z_U E n s K c3 m3 Hn ltac:(lia) HK H3 H5).
rewrite U_of_S, S_SAluw, (t2_x_U E n s K c1 m2 Hn ltac:(lia) HK H1 H4), (t2_y_U E n s K c2 Hn ltac:(lia) HK H2). cbn [zalu_raw].
rewrite !Z.mod_small by lia. rewrite swrap32_id by lia. rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
apply negb_false_iff, Z.eqb_eq. lia.
Qed.
Lemma t2_cnt_U : forall E n s K c m, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c = 3 * K * 2 ^ 48 -> m = 18446744073709551613 * 2 ^ 48 ->
U E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m)) (SLit c)) (SLit 48)) = 3 * (K - s).
Proof.
intros E n s K c m Hn Hs HK -> ->.
assert (HP : 2 ^ 48 = 281474976710656) by reflexivity.
assert (H1 : U E (SMd M_MUL (SOff n 0) (SLit (18446744073709551613 * 2 ^ 48))) = (s * (2 ^ 64 - 3 * 2 ^ 48)) mod 2 ^ 64).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom _ n s Hn) by lia. rewrite U_SLit. unfold zcanon, M64.
replace ((18446744073709551613 * 2 ^ 48) mod 2 ^ 64) with (2 ^ 64 - 3 * 2 ^ 48) by (vm_compute; reflexivity). reflexivity. }
assert (H2 : U E (SLit (3 * K * 2 ^ 48)) = 3 * K * 2 ^ 48) by (apply U_lit; rewrite HP; lia).
assert (H3 : U E (SLit 48) = 48) by (apply U_lit; lia).
rewrite U_SAlu. cbn [zalu_raw].
rewrite U_SAlu. cbn [zalu_raw].
rewrite H1.
rewrite H2.
rewrite H3.
unfold zcanon, M64. rewrite Zplus_mod_idemp_l.
replace (s * (2 ^ 64 - 3 * 2 ^ 48) + 3 * K * 2 ^ 48) with (3 * (K - s) * 2 ^ 48 + s * 2 ^ 64) by ring.
rewrite Z_mod_plus_full. rewrite (Z.mod_small (3 * (K - s) * 2 ^ 48)) by (rewrite ?HP; lia).
change (Z.land 48 63) with 48. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (rewrite ?HP; lia). apply Z.mod_small. lia.
Qed.
Lemma t2_cnt_denot : forall E n s K c m, ew E n = Z_to_bv 64 s -> 0 <= s <= K -> K <= 256 -> c = 3 * K * 2 ^ 48 -> m = 18446744073709551613 * 2 ^ 48 ->
sv_denot E (SAlu ALU_SRL (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit m)) (SLit c)) (SLit 48)) = Z_to_bv 64 (3 * (K - s)).
Proof.
intros E n s K c m Hn Hs HK Hc Hm. rewrite denot_lit_U. f_equal. exact (t2_cnt_U E n s K c m Hn Hs HK Hc Hm).
Qed.
Definition ssT2n : sstate := ra_ss PC_T2 (sr_set sr_atoms 23%bv (SLit 0)) enc_chunks false [(70%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition ssT2l (p k : Z) : sstate :=
ra_ss PC_T2 (sr_set (sr_set sr_atoms 24%bv (SLit p)) 22%bv (SOff 9 30)) enc_chunks false [(23%nat, mkAF 1 k 0); (40%nat, mkAF 1 k 0); (70%nat, mkAF 0 (2^32-1) 0)] [] [].
Definition ssWX : sstate := ra_ss3 PC_WDBX (sr_set sr_atoms 20%bv (SLit ubs2_A_cgif_writecb)) enc_chunks false [(70%nat, mkAF 0 (2^32-1) 0); (18%nat, mkAF 4096 (CEIL_MAX - 96) 4)] [] [].
End b.
Ltac wr HE2 := eapply ra_wr_ok; [ew_havoc; exact HE2 | lia | lia | left; cbn; lia].
Ltac finish3 HS HJ Hid HE2 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS HE0 regs2 cx R2 R8 R4 R3 R27 Htpv MEQ :=
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK;
cbn [ms_regs mkst] in HK;
lazymatch type of HS with st_ok _ _ _ ?msf =>
let V := fresh "V" in let Q18 := fresh "Q18" in let Q21 := fresh "Q21" in
pose proof (enc_of_region _ _ (c_sp cx) _ _ _ (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) HE2 ltac:(cbv; tauto) ltac:(cbv; tauto) HE69 HE70 ltac:(lia) ltac:(lia)) as V;
(jreg HS (18%bv:reg) as Q18); cbn [ms_regs mkst] in Q18; rewrite HE44 in Q18;
(jreg HS (20%bv:reg) as Q21); cbn [ms_regs mkst] in Q21;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HJ with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf end;
eexists _, _, _; split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ|]; split; [exact Hid|];
split; [rewrite HK by (cbv; tauto); exact R2|]; split; [rewrite HK by (cbv; tauto); exact R8|];
split; [rewrite HK by (cbv; tauto); rewrite R4, Htpv; reflexivity|]; split; [rewrite HK by (cbv; tauto); exact R3|];
split; [rewrite HK by (cbv; tauto); exact R27|];
split; [exact Q18|]; split; [exact Q21|];
split; [exact HB2|]; split; [exact Hwt|];
split; [exact (proj1 V)|]; split; [change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in V; exact (proj2 (val_mem_mod _ _ _ _) (proj2 V))|]; split; [exact HM|];
split; [ eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; MEQ
| eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]; intros a Ha; MEQ ]
end.
Ltac lct_run API IMG LAWS pl K CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063 :=
lazymatch type of HFS with frame_savedN _ _ ?regs0 _ _ =>
lazymatch type of HE69 with _ = Z_to_bv 64 ?bb =>
lazymatch type of HE70 with _ = Z_to_bv 64 ?M' =>
match goal with LG : length (c_gvals cx) = 17%nat |- _ =>
apply (CASE pl K); [lia | reflexivity | lia | lia |];
let E0 := fresh "E0" in let HS := fresh "HS" in let HEE := fresh "HEE" in
intros E0 HS HEE; rewrite HEE in HS; clear HEE E0;
jrun_to LAWS ubs2tbl_ok HS HJ PC_WDB; [wr HE2|];
jbranch ubs2tbl HS;
[ exfalso;
let Hc := match goal with H : branch_taken _ _ _ = true |- _ => H end in
rewrite branch_ne_U, (t2_chk_ne _ 40 (c_slct cx) K) in Hc by (first [exact HE40 | lia]); discriminate Hc
| ];
let Hc0 := match goal with H : branch_taken _ _ _ = false |- _ => H end in clear Hc0;
jrun_to LAWS ubs2tbl_ok HS HJ PC_WDB; [wr HE2|];
jbranch ubs2tbl HS;
[
jrun_to LAWS ubs2tbl_ok HS HJ PC_T3; [wr HE2|];
finish3 HS HJ Hid HE2 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS HE0 regs2 cx R2 R8 R4 R3 R27 Htpv ltac:(mbyte_chain ltac:(fun H => rewrite ?HE2 in H))
|
let Hc := match goal with H : branch_taken _ _ _ = false |- _ => H end in
rewrite branch_eq_U, (t2_cnt_U _ 40 (c_slct cx) K), U_lit in Hc by (first [exact HE40 | reflexivity | lia]);
let Hne := fresh "Hne" in
assert (Hne : c_slct cx <> K) by (apply Z.eqb_neq in Hc; lia); clear Hc;
jrun_to LAWS ubs2tbl_ok HS HJ PC_WDB; [wr HE2|];
let W2 := fresh "W2" in let W18 := fresh "W18" in let W21 := fresh "W21" in let W22 := fresh "W22" in let W9 := fresh "W9" in
(jreg HS (2%bv:reg) as W2); rewrite <- (Z_to_bv_bv_unsigned 64 (ew _ 2)), HE2 in W2;
(jreg HS (18%bv:reg) as W18); rewrite HE44 in W18;
(jreg HS (20%bv:reg) as W21); (jreg HS (21%bv:reg) as W22);
pose proof (st_ok_reg _ _ _ _ (22%bv:reg) HS) as W9; eval_sr_get_in W9;
rewrite denot_lit_U, (t2_cnt_U _ 40 (c_slct cx) K) in W9 by (first [exact HE40 | reflexivity | lia]);
let HK := fresh "HK" in
pose proof (regs_kept_of_st_ok _ _ _ _ regs2 _ [2; 3; 4; 8; 27]%bv HS ltac:(rewrite HE0; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK;
lazymatch type of HS with st_ok _ _ _ ?msc =>
let Hobjs1 := fresh "Hobjs1" in let HFS1 := fresh "HFS1" in let V1 := fresh "V1" in
assert (Hobjs1 : objs_at (ms_mem msc) cx (c_rcur cx)) by (eapply objs_at_kept; [exact Hobjs | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
assert (HFS1 : frame_savedN ubs2_msyms 12 regs0 (ms_mem msc) (spZ regs0)) by (eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?HE2 in H));
pose proof (enc_of_region _ _ (c_sp cx) _ _ _ (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) HE2 ltac:(cbv; tauto) ltac:(cbv; tauto) HE69 HE70 ltac:(lia) ltac:(lia)) as V1;
rewrite (st_ok_mkst _ _ _ _ HS eq_refl); cbn [ss_pc];
eapply SR_bind;
[ eapply (rwdb_loop API IMG (Z.to_nat (3 * (K - c_slct cx))) (3 * (K - c_slct cx)) _ _ RAWADD_STK (spZ regs0) _ _ _ _ _ _ _ _ (c_g cx) (c_gvals cx) (c_sp cx));
[ lia | lia | exact HJ | exact (proj2 (proj2 Hobjs1)) | exact Hwfn | exact Hfile | lia | lia | exact Hg16
| exact W2 | exact Hspal | lia | lia | lia | exact W18 | exact W22 | exact W21 | exact W9 ]
| ];
cbv beta;
let regs4 := fresh "regs4" in let mem4 := fresh "mem4" in let HJ4 := fresh "HJ4" in let HK4 := fresh "HK4" in
let P22 := fresh "P22" in let P9 := fresh "P9" in let Hout4 := fresh "Hout4" in let Hgr4 := fresh "Hgr4" in
intros c' (regs4 & mem4 & -> & HJ4 & HK4 & P22 & P9 & Hout4 & Hgr4);
let MEQ4 := fresh "MEQ4" in
assert (MEQ4 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp cx - 16 <= a < c_sp cx) -> mbyte ubs2segs mem4 a = mbyte ubs2segs (ms_mem msc) a)
by (intros a Ha Hna; apply mbyte_eq_of1'; apply Hout4; rewrite unsigned_lit_small by lia; lia);
let Hobjs4 := fresh "Hobjs4" in let HFS4 := fresh "HFS4" in
assert (Hobjs4 : objs_at mem4 cx (c_rcur cx)) by (eapply objs_at_kept; [exact Hobjs1 | | |]; intros i Hi; apply MEQ4; lia);
assert (HFS4 : frame_savedN ubs2_msyms 12 regs0 mem4 (spZ regs0)) by (eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS1|]; intros a Ha; apply MEQ4; lia);
let E4 := fresh "E4" in let HE4 := fresh "HE4" in
remember (Ereg regs4 (ra_extra cx (c_rcur cx) [bb; M'])) as E4 eqn:HE4;
let HE' := fresh "HE'" in
assert (HE' : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E4 n = getr regs4 rr) by (intros; subst E4; apply ew_Ereg_nat; assumption);
let HY4 := fresh "HY4" in let HMo4 := fresh "HMo4" in
pose proof (E_rv regs4 cx (c_rcur cx) [bb; M']) as HY4; rewrite <- HE4 in HY4;
pose proof (E_morev regs4 cx (c_rcur cx) [bb; M'] LG) as HMo4; rewrite <- HE4 in HMo4;
let X2 := fresh "X2" in let X44 := fresh "X44" in let X69 := fresh "X69" in let X70 := fresh "X70" in let X18 := fresh "X18" in
assert (X2 : bv_unsigned (ew E4 2) = c_sp cx) by (rewrite (HE' 2%nat 2%bv eq_refl), (HK4 2%bv) by (vm_compute; reflexivity); rewrite W2; apply unsigned_lit_small; lia);
assert (X44 : ew E4 44 = Z_to_bv 64 (c_g cx)) by (apply (HY4 1%nat); reflexivity);
assert (X69 : ew E4 69 = Z_to_bv 64 bb) by (apply (HMo4 0%nat); reflexivity);
assert (X70 : ew E4 70 = Z_to_bv 64 M') by (apply (HMo4 1%nat); reflexivity);
assert (X18 : ew E4 18 = Z_to_bv 64 (c_g cx)) by (rewrite (HE' 18%nat 18%bv eq_refl), (HK4 18%bv) by (vm_compute; reflexivity); exact W18);
let HS4 := fresh "HS4" in
assert (HS4 : st_ok ubs2segs E4 ssWX (mkst regs4 (Z_to_bv 64 PC_WDBX) mem4 (seg_rom ubs2segs)));
[ rewrite HE4; unfold ssWX;
apply (ra_st_ok3 cx (c_rcur cx) regs4 [bb; M'] mem4 PC_WDBX _ false _ _ [] [] Hcx Hobjs4); rewrite <- ?HE4;
[ rewrite (HK4 2%bv) by (vm_compute; reflexivity); exact W2
| rewrite (HK4 8%bv) by (vm_compute; reflexivity); rewrite HK by (cbv; tauto); exact R8
| rewrite HE4; apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite (HK4 20%bv) by (vm_compute; reflexivity); exact W21]
| intros a Ha; apply (journal_stack_w _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4); lia
| intros X; discriminate X
| reflexivity
| constructor; [|constructor; [|constructor]];
[ eapply chunk_ok_val; [cbn [sv_denot]; rewrite X69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; intros k Hk; rewrite MEQ4 by lia; exact (proj1 V1 k Hk)]
| eapply chunk_ok_val; [cbn [sv_denot]; rewrite X70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | intros k Hk; rewrite MEQ4 by lia; exact (proj2 V1 k Hk)] ]
| cbn [atoms_ok]; unfold afact_ok, AC; cbn [af_lo af_hi af_al2]; rewrite X70, X18, !unsigned_lit_small by lia;
change (2 ^ 0) with 1; change (2 ^ 4) with 16; rewrite !Z.mod_1_r; repeat split; first [lia | exact Hg16]
| constructor
| constructor ]
| ];
change mem4 with (ms_mem (mkst regs4 (Z_to_bv 64 PC_WDBX) mem4 (seg_rom ubs2segs))) in HJ4;
jrun_to LAWS ubs2tbl_ok HS4 HJ4 PC_T3; [eapply ra_wr_ok3; [exact X2 | lia | lia | left; cbn; lia] |];
let HK5 := fresh "HK5" in
pose proof (regs_kept_of_st_ok _ _ _ _ regs4 _ [2; 3; 4; 8; 27]%bv HS4 ltac:(rewrite HE4; apply env_agree_refl) ltac:(vm_compute; reflexivity)) as HK5;
cbn [ms_regs mkst] in HK5;
lazymatch type of HS4 with st_ok _ _ _ ?msf =>
let V := fresh "V" in let Q18 := fresh "Q18" in let Q21 := fresh "Q21" in
pose proof (enc_of_region _ _ (c_sp cx) _ _ _ (st_ok_region_nth _ _ _ 0%nat _ HS4 eq_refl) X2 ltac:(cbv; tauto) ltac:(cbv; tauto) X69 X70 ltac:(lia) ltac:(lia)) as V;
(jreg HS4 (18%bv:reg) as Q18); cbn [ms_regs mkst] in Q18; rewrite X44 in Q18;
(jreg HS4 (20%bv:reg) as Q21); cbn [ms_regs mkst] in Q21;
rewrite (st_ok_mkst _ _ _ _ HS4 eq_refl); cbn [ss_pc]; apply SR_ret;
lazymatch type of HJ4 with journal _ _ _ _ _ _ _ _ _ ?Lf ?Af _ ?mdf =>
exists Lf, Af, (ms_regs msf), (ms_mem msf), mdf end;
eexists _, _, _; split; [reflexivity|]; cbn [ms_regs ms_mem mkst]; split; [exact HJ4|]; split; [exact Hid|];
split; [rewrite HK5 by (cbv; tauto); rewrite (HK4 2%bv) by (vm_compute; reflexivity); exact W2|];
split; [rewrite HK5 by (cbv; tauto); rewrite (HK4 8%bv) by (vm_compute; reflexivity); rewrite HK by (cbv; tauto); exact R8|];
split; [rewrite HK5 by (cbv; tauto); rewrite (HK4 4%bv) by (vm_compute; reflexivity); rewrite HK by (cbv; tauto); rewrite R4, Htpv; reflexivity|];
split; [rewrite HK5 by (cbv; tauto); rewrite (HK4 3%bv) by (vm_compute; reflexivity); rewrite HK by (cbv; tauto); exact R3|];
split; [rewrite HK5 by (cbv; tauto); rewrite (HK4 27%bv) by (vm_compute; reflexivity); rewrite HK by (cbv; tauto); exact R27|];
split; [exact Q18|]; split; [exact Q21|];
split; [exact HB2|]; split; [exact Hwt|];
split; [exact (proj1 V)|]; split; [change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)) in V; exact (proj2 (val_mem_mod _ _ _ _) (proj2 V))|]; split; [exact HM|];
split; [ eapply objs_at_kept; [exact Hobjs4 | | |]; intros i Hi; mbyte_chain ltac:(fun H => rewrite ?X2 in H)
| eapply (frame_savedN_kept ubs2_msyms 12); [lia | exact HFS4|]; intros a Ha; mbyte_chain ltac:(fun H => rewrite ?X2 in H) ]
end
end ]
end end end end.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Hypothesis IMG : img_laws ubs2_msyms MR.
Lemma ra_t2_nolct :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) -> c_slct cx = 0 ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (bb, Lbb) ->
word_mem ubs2segs mem2 (c_sp cx + 8) bb -> val_mem ubs2segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem2 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2)
(at_T3 API cx L A mem md regs0).
Proof.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M Hcx HO HJ Hid HB HR G23 G24 G22 Hz HB2 Hwt W32 W40 HM Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & _).
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (W40' : val_mem ubs2segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs2 cx (c_rcur cx) [bb; M']) as HX. pose proof (E_rv regs2 cx (c_rcur cx) [bb; M']) as HY. rewrite <- HE0 in HX, HY.
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (HS : st_ok ubs2segs E ssT2n (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs))).
{ subst E. unfold ssT2n.
apply (ra_st_ok cx (c_rcur cx) regs2 [bb; M'] mem2 PC_T2 _ false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite G23, Hz; reflexivity].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs))) in HJ.
jrun_to LAWS ubs2tbl_ok HS HJ PC_T3; [wr HE2|].
finish3 HS HJ Hid HE2 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS HE0 regs2 cx R2 R8 R4 R3 R27 Htpv ltac:(mbyte_chain ltac:(fun H => rewrite ?HE2 in H)).
Qed.
Lemma ra_t2_lct123 :
forall cx L A mem md L2 A2 md2 (regs0 regs2 : bvmap 5 word) (mem2 : word -> option byte) (p bb Lbb M : Z),
rcx_ok cx -> ra_origin cx regs0 ->
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L2 A2 mem2 md2 ->
st_init_done A2 = true -> Permutation (blocks L A) (c_blocks cx) ->
ra_regs regs2 cx -> getr regs2 23 = Z_to_bv 64 (c_slct cx) -> getr regs2 24 = Z_to_bv 64 p -> getr regs2 22 = Z_to_bv 64 (c_cfp cx + 30) -> c_slct cx <> 0 -> c_slct cx <= 2 ^ p -> (p = 1 \/ p = 2 \/ p = 3) ->
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks L A) ->
wtok' RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] (blocks L A) (bb, Lbb) ->
word_mem ubs2segs mem2 (c_sp cx + 8) bb -> val_mem ubs2segs mem2 (c_sp cx + 16) 4 M -> 1 <= M <= Lbb ->
objs_at mem2 cx (c_rcur cx) -> frame_savedN ubs2_msyms 12 regs0 mem2 (spZ regs0) ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2)
(at_T3 API cx L A mem md regs0).
Proof.
intros cx L A mem md L2 A2 md2 regs0 regs2 mem2 p bb Lbb M Hcx HO HJ Hid HB HR G23 G24 G22 Hnz Hsk Hpc HB2 Hwt W32 W40 HM Hobjs HFS.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HSTKv : RAWADD_STK = 8704) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof HO as (Hspe & Htp0 & Hgp0 & Hra0 & Hgp & H25o & H26o & H27o).
pose proof Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htpv) & Hslct).
pose proof (objs_fields_ok _ _ _ Hobjs) as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1' & G2' & G3' & G4' & G5' & G6' & G7' & G8' & LG).
pose proof HR as (R2 & R8 & R9 & R4 & R3 & R27).
pose proof (journal_heap _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HH2.
pose proof HJ as (_ & _ & _ & _ & _ & (Hsp0al & Hstk0 & Hceil & Hsp063 & Hstw) & _). cbn beta in Hstw.
assert (Hbbin : In (bb, Lbb) (blocks L2 A2)) by (eapply Permutation_in; [apply Permutation_sym; exact HB2 | left; reflexivity]).
destruct (heap_blocks_range _ _ LAWS L2 A2 mem2 md2 bb Lbb HH2 Hbbin ltac:(lia)) as (Hbb0 & Hbb1 & _).
set (M' := M mod 2 ^ 32).
pose proof (Z.mod_pos_bound M (2 ^ 32) ltac:(lia)) as HM'. fold M' in HM'.
assert (W40' : val_mem ubs2segs mem2 (c_sp cx + 16) 4 M') by (subst M'; change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)); apply (proj1 (val_mem_mod _ _ _ _)); exact W40).
remember (Ereg regs2 (ra_extra cx (c_rcur cx) [bb; M'])) as E eqn:HE0.
assert (HE : forall n (rr : reg), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs2 rr) by (intros; subst E; apply ew_Ereg_nat; assumption).
pose proof (E_cv regs2 cx (c_rcur cx) [bb; M']) as HX. pose proof (E_rv regs2 cx (c_rcur cx) [bb; M']) as HY. rewrite <- HE0 in HX, HY.
pose proof (E_morev regs2 cx (c_rcur cx) [bb; M'] LG) as HMo. rewrite <- HE0 in HMo.
assert (HE2 : bv_unsigned (ew E 2) = c_sp cx) by (rewrite (HE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia).
assert (HE8 : ew E 8 = Z_to_bv 64 (c_raw cx)) by (rewrite (HE 8%nat 8%bv eq_refl); exact R8).
assert (HE23 : ew E 23 = Z_to_bv 64 (c_slct cx)) by (rewrite (HE 23%nat 23%bv eq_refl); exact G23).
assert (HE9 : ew E 9 = Z_to_bv 64 (c_cfp cx)) by (rewrite (HE 9%nat 9%bv eq_refl); exact R9).
assert (HE40 : ew E 40 = Z_to_bv 64 (c_slct cx)) by (apply (HX 8%nat); reflexivity).
assert (HE44 : ew E 44 = Z_to_bv 64 (c_g cx)) by (apply (HY 1%nat); reflexivity).
assert (HE69 : ew E 69 = Z_to_bv 64 bb) by (apply (HMo 0%nat); reflexivity).
assert (HE70 : ew E 70 = Z_to_bv 64 M') by (apply (HMo 1%nat); reflexivity).
assert (CASE : forall pl K : Z, p = pl -> K = 2 ^ pl -> 1 <= c_slct cx <= K -> K <= 256 ->
(forall E0, st_ok ubs2segs E0 (ssT2l pl K) (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) -> E0 = E ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2) (at_T3 API cx L A mem md regs0)) ->
SR ubs2segs (mkCfg (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs)) md2) (at_T3 API cx L A mem md regs0)).
{ intros pl K Hpl HK Hsk2 HK2 RUN. apply (RUN E); [|reflexivity]. subst E. unfold ssT2l.
apply (ra_st_ok cx (c_rcur cx) regs2 [bb; M'] mem2 PC_T2 _ false _ _ [] [] Hcx Hobjs HR); rewrite <- ?HE0.
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite G24, Hpl; reflexivity]
| intros X; discriminate X | cbn [sv_denot]; rewrite G22, HE9, unsigned_lit_small by lia; reflexivity].
- intros a Ha. apply Hstw. lia.
- intros X. discriminate X.
- reflexivity.
- constructor; [|constructor; [|constructor]].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE69, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | apply val_mem_word_mem; exact W32].
+ eapply chunk_ok_val; [cbn [sv_denot]; rewrite HE70, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact W40'].
- cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE23, HE40, HE70, !unsigned_lit_small by lia.
change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia.
- constructor.
- constructor. }
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs))) in HJ.
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 PC_T2) mem2 (seg_rom ubs2segs))) in HJ.
destruct Hpc as [Hp | [Hp | Hp]]; rewrite Hp in Hsk; cbn in Hsk.
- lct_run API IMG LAWS 1 2 CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063.
- lct_run API IMG LAWS 2 4 CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063.
- lct_run API IMG LAWS 3 8 CASE HJ Hid HE HE0 HE2 HE8 HE40 HE44 HE69 HE70 HB2 Hwt HM Hobjs HFS regs2 cx R2 R8 R4 R3 R27 Htpv Hcx Hspal Hg0 Hg1 Hg16 Hfile Hwfn Hsp063.
Qed.
End S.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
