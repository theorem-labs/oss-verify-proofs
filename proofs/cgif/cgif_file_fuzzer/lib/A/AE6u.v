(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0v YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE3d AE20 AE2y AE6t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (d x n : Z).
Hypothesis HPRE : ecall_pre tfibsegs B ly S W regs mem md.
Hypothesis G10 : getr regs 10 = w64 d.
Hypothesis G11 : getr regs 11 = w64 x.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis Hn : 0 <= n < 2 ^ 32.
Hypothesis Hd : 0 <= d.
Hypothesis Hdn : d + n <= 2 ^ 63.
Hypothesis HDST : dest_ok tfibsegs B ly S W regs mem d n.
Hypothesis HRA : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n.
Hypothesis HHULL : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) d n.
Hypothesis HAM : amem_range d n.
Let sp0 : Z := spZ regs.
Let H := w_H W.
Let g0 : Z := d / 8.
Let g1 : Z := (d + n - 1) / 8.
Let du : Z := (d + 7) / 8 * 8.
Let de : Z := (d + n) / 8 * 8.
Let gu : Z := (d + 7) / 8.
Let ge : Z := (d + n) / 8.
Local Notation Env := (AE2y.Env regs).
Local Notation Env_reg := (AE2y.Env_reg regs).
Local Notation Env_x := (AE2y.Env_x regs).
Local Notation Env2 := (AE6t.Env2 regs).
Local Notation Env10 := (AE6t.Env10 regs d G10).
Local Notation Env12 := (AE6t.Env12 regs n G12).
Local Notation POSTm := (AE6t.POSTm B ly S W regs mem md d x n).
Local Notation basics := (AE6t.basics B ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation finish := (AE6t.finish B LAWS ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM).
Local Notation ent_stk := (AE6t.ent_stk B ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation ent_ro := (AE6t.ent_ro B TB ly S W regs mem md d n HPRE Hn Hd HAM).
Local Notation path0 := (AE6t.path0 B LAWS TB ly S W regs mem md d x n HPRE G10 G11 G12 Hn Hd Hdn HDST HAM).
Local Notation ent1_0 := (AE6t.ent1_0 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HAM).
Local Notation ent1_1 := (AE6t.ent1_1 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_2 := (AE6t.ent1_2 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_3 := (AE6t.ent1_3 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_4 := (AE6t.ent1_4 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_5 := (AE6t.ent1_5 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_6 := (AE6t.ent1_6 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_7 := (AE6t.ent1_7 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Local Notation ent1_8 := (AE6t.ent1_8 B TB ly S W regs mem md d n HPRE G10 G12 Hn Hd Hdn HRA HAM).
Lemma path1_0 : 1 <= n <= 64 -> g1 - g0 = 0 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_0 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_0_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_0_e0 13) (RG p1_0_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_0_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_0_e1 14) (RG p1_0_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_0_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_0_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450880) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450880 E32) by lia. f_equal. subst h2. replace (g0 + 2147450880) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_0_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_0_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_0_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_0z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_0z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_0_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_0n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_0n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 0%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_0n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_0n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_1 : 1 <= n <= 64 -> g1 - g0 = 1 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_1 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_1_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_1_e0 13) (RG p1_1_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_1_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_1_e1 14) (RG p1_1_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_1_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_1_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450881) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450881 E32) by lia. f_equal. subst h2. replace (g0 + 2147450881) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_1_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_1_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_1_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_1z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_1z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_1_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_1n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_1n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 1%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_1n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_1n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_2 : 1 <= n <= 64 -> g1 - g0 = 2 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_2 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_2_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_2_e0 13) (RG p1_2_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_2_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_2_e1 14) (RG p1_2_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_2_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_2_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450882) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450882 E32) by lia. f_equal. subst h2. replace (g0 + 2147450882) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_2_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_2_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_2_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_2z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_2z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_2_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_2n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_2n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 2%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_2n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_2n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_3 : 1 <= n <= 64 -> g1 - g0 = 3 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_3 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_3_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_3_e0 13) (RG p1_3_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_3_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_3_e1 14) (RG p1_3_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_3_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_3_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450883) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450883 E32) by lia. f_equal. subst h2. replace (g0 + 2147450883) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_3_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_3_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_3_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_3z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_3z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_3_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_3n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_3n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 3%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_3n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_3n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
Lemma path1_4 : 1 <= n <= 64 -> g1 - g0 = 4 -> SRr tfibsegs W (cfg_at tfibsegs MS_ENTRY regs mem md) POSTm.
Proof.
intros Hn64 Ht.
pose proof basics as (Bsp & Bhi & Bal & Bdn & Bpres & BM). assert (HSC : MS_SCR = 2200) by reflexivity.
unfold cfg_at. change (w64 MS_ENTRY) with (Z_to_bv 64 MS_ENTRY).
assert (MEQ0 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem (mkst regs (Z_to_bv 64 MS_ENTRY) mem (seg_rom tfibsegs)) z = mem z) by (intros; reflexivity).
assert (Hg0 : 0 <= g0 /\ 8 * g0 <= d < 8 * g0 + 8) by (subst g0; split; [apply Z.div_pos; lia | pose proof (Z.div_mod d 8 ltac:(lia)); pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia]).
assert (Hg1 : 8 * g1 <= d + n - 1 < 8 * g1 + 8) by (subst g1; pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
assert (Hg1hi : g1 < 2 ^ 44) by lia.
destruct (ra_last (aview tfibsegs H mem) d n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)); lia).
pose proof (HHULL ltac:(lia)) as HH.
set (h1 := (g0 + 2147450880) / 8 * 8). set (h2 := (g1 + 2147450880) / 8 * 8).
assert (Hh1 : h1 <= g0 + 2147450880 < h1 + 8) by (subst h1; pose proof (Z.div_mod (g0 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g0 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh2 : h2 <= g1 + 2147450880 < h2 + 8) by (subst h2; pose proof (Z.div_mod (g1 + 2147450880) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (g1 + 2147450880) 8 ltac:(lia)); lia).
assert (Hh12 : h1 <= h2) by (subst h1 h2; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
assert (Hsh1 : shadow_addr d / 8 * 8 = h1) by (subst h1; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g0; f_equal; f_equal; lia).
assert (Hsh2 : shadow_addr (d + n - 1) / 8 * 8 = h2) by (subst h2; unfold shadow_addr; change SHADOW_OFF with SB; unfold SB; subst g1; f_equal; f_equal; lia).
destruct (hull_rdword H mem d n h1 HH ltac:(lia) ltac:(lia)) as (q1 & Hq1 & Rq1).
destruct (hull_rdword H mem d n h2 HH ltac:(lia) ltac:(lia)) as (q2 & Hq2 & Rq2).
set (EE := Env [g0; g1; b1; q1; q2]). assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r) by (intros; apply Env_reg; assumption).
pose proof (Env2 [g0; g1; b1; q1; q2]) as EE2. pose proof (Env10 [g0; g1; b1; q1; q2]) as EE10. pose proof (Env12 [g0; g1; b1; q1; q2]) as EE12. fold EE in EE2, EE10, EE12.
assert (E32 : ew EE 32 = Z_to_bv 64 g0) by (apply (Env_x _ 0); reflexivity).
assert (E34 : ew EE 34 = Z_to_bv 64 b1) by (apply (Env_x _ 2); reflexivity).
assert (E35 : ew EE 35 = Z_to_bv 64 q1) by (apply (Env_x _ 3); reflexivity).
assert (E36 : ew EE 36 = Z_to_bv 64 q2) by (apply (Env_x _ 4); reflexivity).
pose proof (ent1_4 b1 q1 q2 Hn64 Ht Hb1 Hok) as HS0. fold EE in HS0.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS0 r_p1_4_0)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1 & HFr1). rewrite ?wvb_wvb in *.
assert (MEQ1 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms1 z = mem z).
{ intros z Hz. rewrite (HF1 z); [apply MEQ0; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF1 HFr1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (RG p1_4_e0 13) (RG p1_4_e0 12) HS1 (br_ovf_false EE 10 12 d n EE10 EE12 ltac:(lia) ltac:(lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'. clear HS1.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS1' r_p1_4_1)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2 & HFr2). rewrite ?wvb_wvb in *.
assert (MEQ2 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms2 z = mem z).
{ intros z Hz. rewrite (HF2 z); [apply MEQ1; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF2 HFr2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG p1_4_e1 14) (RG p1_4_e1 13) HS2 (br_cls_small EE n EE12 Hn64)) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'. clear HS2.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS2' r_p1_4_2)|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3 & HFr3). rewrite ?wvb_wvb in *.
assert (MEQ3 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms3 z = mem z).
{ intros z Hz. rewrite (HF3 z); [apply MEQ2; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF3 HFr3.
assert (HW4 : rdword (aview tfibsegs H (ms_mem ms3)) h1 = Some (bv_unsigned (ew EE 35))).
{ rewrite E35, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq1].
intros i Hi. apply aview_same. apply MEQ3. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (p1_4_e2) ms3 _ 16%bv 16%bv 538627 h1 35 48 HS3 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (U_hull_addr EE 32 g0 2147450880 E32 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW4)|].
cbv beta. intros W4 c4 _ (-> & ms4 & mat4 & -> & HS4 & HM4).
assert (MEQ4 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms4 z = mem z) by (intros z Hz; rewrite HM4; apply MEQ3; exact Hz).
clear HM4 HW4 HS3.
assert (Hrs2 : sv_denot EE (SAlu ALU_AND (SOff 32 2147450884) (SLit (-8))) = Z_to_bv 64 h2).
{ rewrite (U_hull_addr EE 32 g0 2147450884 E32) by lia. f_equal. subst h2. replace (g0 + 2147450884) with (g1 + 2147450880) by lia. reflexivity. }
assert (HW5 : rdword (aview tfibsegs H (ms_mem ms4)) h2 = Some (bv_unsigned (ew EE 36))).
{ rewrite E36, unsigned_lit_small by lia. apply (AF0x.rdword_ext (aview tfibsegs H mem)); [|exact Hq2].
intros i Hi. apply aview_same. apply MEQ4. rewrite unsigned_lit_small by lia. unfold MS_STK, kHighMemBeg in *. lia. }
eapply SRr_bind; [apply (icpt_ld8 W EE (set_regs_pc p1_4_e2 [((16%bv : bv 5), SOff 35 0)] (ss_pc p1_4_e2 + 4)) ms4 _ 17%bv 17%bv 571523 h2 36 48 HS4 eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_refl_bv) eq_refl (Hrs2) ltac:(lia) ltac:(unfold kHighMemBeg in *; lia) HW5)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HM5).
assert (MEQ5 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms5 z = mem z) by (intros z Hz; rewrite HM5; apply MEQ4; exact Hz).
clear HM5 HW5 HS4.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS5 r_p1_4_3)|].
cbv beta. intros W6 c6 _ (-> & ms6 & mat6 & -> & HS6 & HF6 & HFr6). rewrite ?wvb_wvb in *.
assert (MEQ6 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms6 z = mem z).
{ intros z Hz. rewrite (HF6 z); [apply MEQ5; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF6 HFr6.
destruct (Z.eq_dec (Z.lor q2 q1) 0) as [Hq|Hq].
+
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_NE (RG p1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_eq _ _) Hq)))) as HS6'.
change (neg_bc BC_NE) with BC_EQ in HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_4z_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
apply (finish EE p1_4z_e0 ms7 mat7 HS7 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ7. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms7) a); [apply MEQ7; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
+
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_NE (RG p1_4_e3 16) (SLit 0) HS6 (eq_trans (br_hull EE 35 36 q1 q2 E35 E36 Rq1 Rq2) (f_equal negb (proj2 (Z.eqb_neq _ _) Hq)))) as HS6'. clear HS6.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS6' r_p1_4n_0)|].
cbv beta. intros W7 c7 _ (-> & ms7 & mat7 & -> & HS7 & HF7 & HFr7). rewrite ?wvb_wvb in *.
assert (MEQ7 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms7 z = mem z).
{ intros z Hz. rewrite (HF7 z); [apply MEQ6; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF7 HFr7.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG p1_4n_e0 13) (SLit 0) HS7 (qc_flag_zero EE 4%nat 10 12 34 d n b1 EE10 EE12 E34 Hd ltac:(lia) Hdn ltac:(lia) Hok)) as HS7'. clear HS7.
eapply SRr_bind; [apply (icpt_phase W EE _ _ _ _ _ HS7' r_p1_4n_1)|].
cbv beta. intros W8 c8 _ (-> & ms8 & mat8 & -> & HS8 & HF8 & HFr8). rewrite ?wvb_wvb in *.
assert (MEQ8 : forall z : word, ~ (sp0 - MS_STK <= bv_unsigned z < sp0) -> ms_mem ms8 z = mem z).
{ intros z Hz. rewrite (HF8 z); [apply MEQ7; unfold MS_STK, MS_SCR in *; lia|]. intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- MS_STK) 0 sp0 _ EE2 Hin) as X; [vm_compute; reflexivity|]. unfold MS_STK, MS_SCR in *. lia. }
clear HF8 HFr8.
apply (finish EE p1_4n_e1 ms8 mat8 HS8 eq_refl ltac:(vm_compute; reflexivity) EEreg).
- intros z Hz. apply MEQ8. unfold MS_SCR, MS_STK in *. lia.
- intros a Ha; unfold MS_SCR, MS_STK in *; apply (apresent_same H mem (ms_mem ms8) a); [apply MEQ8; rewrite unsigned_lit_small by lia; lia | apply Bpres; lia].
Qed.
End c.
End b.
