(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpvH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpvH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
Set Default Proof Using "All".

Definition LV_J (E : env) : lvp := L_main_jo6 (atopE E).

Fixpoint zsum (l : list Z) : Z := match l with [] => 0 | x :: r => x + zsum r end.
Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. lia. Qed.
Lemma zsum_map_le : forall {T} (f g : T -> Z) l, (forall x, In x l -> f x <= g x) -> zsum (map f l) <= zsum (map g l).
Proof. intros T f g l H. induction l as [|x l IH]; cbn; [lia|]. pose proof (H x (or_introl eq_refl)). assert (zsum (map f l) <= zsum (map g l)) by (apply IH; intros; apply H; right; assumption). lia. Qed.
Lemma zsum_map_filter_le : forall {T} (f : T -> Z) p l, (forall x, In x l -> 0 <= f x) -> zsum (map f (List.filter p l)) <= zsum (map f l).
Proof.
intros T f p l H. induction l as [|x l IH]; cbn; [lia|].
assert (IH' : zsum (map f (List.filter p l)) <= zsum (map f l)) by (apply IH; intros; apply H; right; assumption).
pose proof (H x (or_introl eq_refl)). destruct (p x); cbn; lia.
Qed.

Definition wpages (iv : Z * Z) : Z := (snd iv - fst iv) / 4096 + 2.
Definition wshadow (iv : Z * Z) : Z := ((snd iv - fst iv) / 8 + 2) / 4096 + 2.
Definition wboth (iv : Z * Z) : Z := wpages iv + wshadow iv.

Lemma length_flat_map : forall {T U} (f : T -> list U) l, Z.of_nat (length (flat_map f l)) = zsum (map (fun x => Z.of_nat (length (f x))) l).
Proof. intros T U f l. induction l; cbn; [reflexivity|]. rewrite length_app, Nat2Z.inj_add, IHl. reflexivity. Qed.

Section Count.
Variable L : lvp.
Variable mo : Model.
Hypothesis Hwf : forall iv, In iv (appvis L mo) -> fst iv <= snd iv.

Lemma cand_pages_le : Z.of_nat (length (cand L mo)) <= zsum (map wboth (appvis L mo)).
Proof.
unfold cand. rewrite length_app, Nat2Z.inj_add, !length_flat_map.
assert (A : zsum (map (fun x => Z.of_nat (length (pages_meeting x))) (List.filter Qsn5.nonempty (appvis L mo)))
<= zsum (map wpages (appvis L mo))).
{ etransitivity; [apply zsum_map_le | apply zsum_map_filter_le].
- intros x Hx. apply filter_In in Hx as [Hx _]. destruct x as [lo hi]. unfold wpages. cbn [fst snd]. apply length_pages_meeting_le. exact (Hwf _ Hx).
- intros x Hx. unfold wpages. pose proof (Hwf x Hx). pose proof (Z.div_pos (snd x - fst x) 4096). lia. }
assert (B : zsum (map (fun x => Z.of_nat (length (pages_meeting x))) (shivs L mo)) <= zsum (map wshadow (appvis L mo))).
{ unfold shivs. rewrite map_map. etransitivity; [apply zsum_map_le | apply zsum_map_filter_le].
- intros x Hx. apply filter_In in Hx as [Hx Hne]. unfold Qsn5.nonempty in Hne. apply Z.ltb_lt in Hne.
destruct x as [lo hi]. unfold wshadow, Qsn5.sh_iv, Qsn5.shz. cbn [fst snd] in *.
etransitivity; [apply length_pages_meeting_le; cbn [fst snd]|].
+ pose proof (Z.div_le_mono lo (hi - 1) 8 ltac:(lia) ltac:(lia)). lia.
+ cbn [fst snd].
assert (Hd : (hi - 1) / 8 + 1 - lo / 8 <= (hi - lo) / 8 + 2).
{ pose proof (Z.div_mod (hi - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (hi - 1) 8 ltac:(lia)).
pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.mod_pos_bound lo 8 ltac:(lia)).
pose proof (Z.div_mod (hi - lo) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (hi - lo) 8 ltac:(lia)). lia. }
assert (Hm : (lv_shoff L + (hi - 1) / 8 + 1 - (lv_shoff L + lo / 8)) / 4096 <= ((hi - lo) / 8 + 2) / 4096)
by (apply Z.div_le_mono; lia).
replace (lv_shoff L + (hi - 1) / 8 + 1 - (lv_shoff L + lo / 8)) with ((hi - 1) / 8 + 1 - lo / 8) in Hm by lia.
replace (lv_shoff L + (hi - 1) / 8 + 1 - (lv_shoff L + lo / 8)) with ((hi - 1) / 8 + 1 - lo / 8) by lia. lia.
- intros x Hx. unfold wshadow. pose proof (Hwf x Hx). pose proof (Z.div_pos (snd x - fst x) 8).
pose proof (Z.div_pos ((snd x - fst x) / 8 + 2) 4096). lia. }
assert (C : zsum (map wboth (appvis L mo)) = zsum (map wpages (appvis L mo)) + zsum (map wshadow (appvis L mo))).
{ clear. induction (appvis L mo); cbn; [reflexivity|]. unfold wboth at 1. lia. }
lia.
Qed.
End Count.

Definition wlen (n : Z) : Z := n / 4096 + 2 + ((n / 8 + 2) / 4096 + 2).
Lemma wboth_wiv2z : forall e : word * word, wboth (wiv2z e) = wlen (bv_unsigned (snd e)).
Proof.
intros [b n]. unfold wboth, wpages, wshadow, wiv2z, wlen. cbn [fst snd].
replace (bv_unsigned b + bv_unsigned n - bv_unsigned b) with (bv_unsigned n) by lia. lia.
Qed.
Lemma wsum_objs : forall E (l : list (nat * Z)), Forall (fun o => 0 <= snd o < 2 ^ 64) l ->
zsum (map wboth (map wiv2z (map (obj_e E) l))) = zsum (map (fun o => wlen (snd o)) l).
Proof.
intros E l H. induction H as [|o l Ho _ IH]; [reflexivity|]. cbn [map zsum]. rewrite IH, wboth_wiv2z. unfold obj_e. cbn [snd edenot].
rewrite u64_lit by exact Ho. reflexivity.
Qed.

Definition kn_mem (K : kentry) (k : list kentry) : bool := existsb (kentry_eqb K) k.
Lemma kn_mem_In : forall K k, kn_mem K k = true -> In K k.
Proof. intros K k H. unfold kn_mem in H. apply existsb_exists in H as (K' & Hin & Heq). apply kentry_eqb_eq in Heq. subst K'. exact Hin. Qed.

Definition F208 : kentry := KRange (EVar 208) 4295491576 34326181871.
Definition F209 : kentry := KRange (EVar 209) 0 15.
Definition F0 : kentry := KRange (EVar 0) 4294901760 4294967295.
Definition F10 : kentry := KRange (EVar 10) 0 8.
Definition KZ_BAND : kentry :=
KZero {| a_base := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 10)); a_off := 2146402304 |}
(EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EVar 10))) (ELit 0x100000100000)).
Lemma HS2_facts : forall w ch, HSCLASS_S w ch -> In F208 (kn ch) /\ In F209 (kn ch) /\ In F0 (kn ch) /\ In F10 (kn ch) /\ In KZ_BAND (kn ch).
Proof. intros w ch HCL. repeat split; apply kn_mem_In; destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity. Qed.

Lemma e_top_eq : e_top = EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 4096) (EVar 10)).
Proof. reflexivity. Qed.

Lemma neg_scale_arith : forall V0 V10, 4294901760 <= V0 <= 4294967295 -> 0 <= V10 <= 8 ->
(((-4096) mod 2 ^ 64 * V0) mod 2 ^ 64 + ((-512) mod 2 ^ 64 * V10) mod 2 ^ 64) mod 2 ^ 64 = 2 ^ 64 - 4096 * V0 - 512 * V10.
Proof.
intros V0 V10 H0 H10.
rewrite !Z.mul_mod_idemp_l by lia. rewrite <- Zplus_mod.
replace (-4096 * V0 + -512 * V10) with ((2 ^ 64 - 4096 * V0 - 512 * V10) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma HS2_fd : forall w ch, HSCLASS_S w ch -> a_fd ch = FdStd.
Proof. intros [|] ch [-> | ->]; reflexivity. Qed.

Section Cinv.
Variable sp : word.
Variable rdraw : EntryDraw.
Variable brk0 : word.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variables uid hw : word.
Hypothesis Hsp : valid_sp sp.
Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (mo : Model).
Variable w : bool.
Variable ch : acs.
Hypothesis HCL : HSCLASS_S w ch.
Hypothesis CS : cs_ok JO6SEGS AJO6 QVWI.Mq0.LIMIT (bv_unsigned sp) (SINV0 JO6PH sp rdraw brk0 argv envp uid hw) (argH0 JO6PH sp rdraw argv envp uid hw) fs E ch R FULL mo.
#[local] Notation h := (m_vmmaps mo).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).
#[local] Notation LV := (LV_J E).

Lemma fdinv_main : fdinv mo.
Proof.
pose proof (P co_fds) as Hf. rewrite (HS2_fd w ch HCL) in Hf. cbn [fds_ok] in Hf.
unfold fdinv. rewrite Hf. unfold fds_std.
assert (LK : forall k : word, fd_lookup [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))] k
= if bv_eqb (Z_to_bv 64 0) k then Some (FdChannel (Z_to_bv 64 0))
else if bv_eqb (Z_to_bv 64 1) k then Some (FdChannel (Z_to_bv 64 1))
else if bv_eqb (Z_to_bv 64 2) k then Some (FdChannel (Z_to_bv 64 2)) else None) by reflexivity.
repeat split.
- intros k c Hk. rewrite LK in Hk.
destruct (bv_eqb (Z_to_bv 64 0) k) eqn:E0; [apply bv_eqb_eq in E0; subst k; rewrite u64_lit; lia|].
destruct (bv_eqb (Z_to_bv 64 1) k) eqn:E1; [apply bv_eqb_eq in E1; subst k; rewrite u64_lit; lia|].
destruct (bv_eqb (Z_to_bv 64 2) k) eqn:E2; [apply bv_eqb_eq in E2; subst k; rewrite u64_lit; lia|]. discriminate.
- intros k p off Hk. rewrite LK in Hk.
destruct (bv_eqb (Z_to_bv 64 0) k); [discriminate|]. destruct (bv_eqb (Z_to_bv 64 1) k); [discriminate|]. destruct (bv_eqb (Z_to_bv 64 2) k); discriminate.
- intros k e Hk. rewrite LK in Hk.
destruct (bv_eqb (Z_to_bv 64 0) k); [injection Hk as <-; exact I|]. destruct (bv_eqb (Z_to_bv 64 1) k); [injection Hk as <-; exact I|].
destruct (bv_eqb (Z_to_bv 64 2) k); [injection Hk as <-; exact I| discriminate].
Qed.

Lemma maps_below_top_main : maps_below_top h.
Proof.
split.
- pose proof (MA main_atop_bounds) as B.
rewrite (MA main_atop) in B. unfold grant_ceilA, sp_window_hi, stack_max_size. lia.
- exact (MA maps_below_atop).
Qed.

Lemma e_low_z : wiv2z (e_low E) = (0x7fff7000, 0x7fff7000 + 0x10000000).
Proof. unfold wiv2z, e_low. cbn [fst snd]. rewrite !(u_litE E) by lia. reflexivity. Qed.
Lemma e_gap_z : wiv2z (e_gap E) = (0x8fff7000, 0x8fff7000 + 0x20000000000).
Proof. unfold wiv2z, e_gap. cbn [fst snd]. rewrite !(u_litE E) by lia. reflexivity. Qed.
Lemma e_high_z : wiv2z (e_high E) = (0x2008fff7000, 0x2008fff7000 + 0xdfff0001000).
Proof. unfold wiv2z, e_high. cbn [fst snd]. rewrite !(u_litE E) by lia. reflexivity. Qed.

Lemma excl_low : excl_entry LV (e_low E) = true.
Proof. unfold excl_entry. rewrite e_low_z. reflexivity. Qed.
Lemma excl_gap : excl_entry LV (e_gap E) = true.
Proof. unfold excl_entry. rewrite e_gap_z. reflexivity. Qed.
Lemma excl_high : excl_entry LV (e_high E) = true.
Proof. unfold excl_entry. rewrite e_high_z. reflexivity. Qed.

Lemma zoverlap_false : forall a b : Z * Z, snd a <= fst b \/ snd b <= fst a -> zoverlap a b = false.
Proof.
intros [a1 a2] [b1 b2] H. unfold zoverlap. cbn [fst snd] in *. destruct H as [H|H].
- replace (b1 <? a2) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
- replace (a1 <? b2) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r, andb_false_l. reflexivity.
Qed.

Lemma not_excl : forall e, In e (vm_maps h) -> e <> e_low E -> e <> e_gap E -> e <> e_high E -> excl_entry LV e = false.
Proof.
intros e He H1 H2 H3.
pose proof ((MA maps_disj) _ _ He (MA e_low_in) H1) as D1.
pose proof ((MA maps_disj) _ _ He (MA e_gap_in) H2) as D2.
pose proof ((MA maps_disj) _ _ He (MA e_high_in) H3) as D3.
unfold iv_disjoint, e_low, e_gap, e_high in D1, D2, D3. cbn [fst snd] in D1, D2, D3. rewrite !(u_litE E) in D1, D2, D3 by lia.
unfold excl_entry, LV_J, L_main_jo6. cbn [lv_excl existsb].
rewrite !zoverlap_false by (unfold wiv2z; cbn [fst snd]; lia). reflexivity.
Qed.

Lemma excl_cases : forall e, In e (vm_maps h) -> excl_entry LV e = true -> e = e_low E \/ e = e_gap E \/ e = e_high E.
Proof.
intros e He Hx. destruct (decide (e = e_low E)) as [->|N1]; [left; reflexivity|].
destruct (decide (e = e_gap E)) as [->|N2]; [right; left; reflexivity|].
destruct (decide (e = e_high E)) as [->|N3]; [right; right; reflexivity|].
rewrite (not_excl e He N1 N2 N3) in Hx. discriminate.
Qed.

Lemma excl_inside_main : excl_inside LV mo.
Proof.
intros e He Hex. destruct (excl_cases e He Hex) as [ -> | [ -> | -> ] ].
- exists (0x7fff7000, 0x7fff7000 + 0x10000000). split; [cbn; tauto|]. unfold e_low. cbn [fst snd]. rewrite !(u_litE E) by lia. lia.
- exists (0x8fff7000, 0x8fff7000 + 0x20000000000). split; [cbn; tauto|]. unfold e_gap. cbn [fst snd]. rewrite !(u_litE E) by lia. lia.
- exists (0x2008fff7000, 0x2008fff7000 + 0xdfff0001000). split; [cbn; tauto|]. unfold e_high. cbn [fst snd]. rewrite !(u_litE E) by lia. lia.
Qed.

Lemma xinvA_main : xinvA LV mo.
Proof.
split; [exact fdinv_main|]. split; [exact (P co_wf)|]. split; [exact excl_inside_main | exact maps_below_top_main].
Qed.

Lemma obj_ne : forall o, In o (OBJS_W w) -> obj_e E o <> e_low E /\ obj_e E o <> e_gap E /\ obj_e E o <> e_high E.
Proof.
intros o Ho.
assert (L : snd o = 4096 \/ snd o = 8192 \/ snd o = 8388608 \/ snd o = 1048576 \/ snd o = 11571200 \/ snd o = 65536
\/ snd o = 137439023104 \/ snd o = 3727360).
{ destruct w; cbn in Ho; repeat (destruct Ho as [<-|Ho]; [cbn; tauto|]); destruct Ho. }
unfold obj_e, e_low, e_gap, e_high. split; [|split]; intros Heq;
apply (f_equal (fun e : word * word => bv_unsigned (snd e))) in Heq; cbn [fst snd edenot] in Heq;
rewrite !u64_lit in Heq by lia; lia.
Qed.

Lemma obj_appvis : forall o, In o (OBJS_W w) -> In (wiv2z (obj_e E o)) (appvis LV mo).
Proof.
intros o Ho. unfold appvis. apply in_app_iff. right. apply in_map. apply filter_In. split.
- exact ((MA in_maps_obj) o Ho).
- destruct (obj_ne o Ho) as (N1 & N2 & N3).
rewrite (not_excl _ ((MA in_maps_obj) o Ho) N1 N2 N3). reflexivity.
Qed.

Lemma obj_pos : forall o, In o (OBJS_W w) -> 0 < bv_unsigned (snd (obj_e E o)).
Proof. intros o Ho. exact ((MA maps_pos) _ ((MA in_maps_obj) o Ho)). Qed.

Definition inside_appvis (p : expr * expr) : Prop :=
exists iv, In iv (appvis LV mo) /\ fst iv < snd iv /\ fst iv <= uE E (fst p) /\ uE E (fst p) + uE E (snd p) <= snd iv.

Lemma inside_allowed : forall p z, inside_appvis p ->
((uE E (fst p) <=? z) && (z <? uE E (fst p) + uE E (snd p)) || (sh_lo AJO6 E p <=? z) && (z <? sh_hi AJO6 E p))%bool = true ->
allowed_byte LV mo z = true.
Proof.
intros p z (iv & Hiv & Hne & H1 & H2) Hz. unfold allowed_byte. apply orb_true_iff in Hz as [Hz|Hz];
apply andb_prop in Hz as [Z1 Z2]; apply Z.leb_le in Z1; apply Z.ltb_lt in Z2; apply orb_true_iff.
- left. unfold in_zivs. apply existsb_exists. exists iv. split; [exact Hiv|]. unfold zin. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
- right. unfold in_zivs, shivs. apply existsb_exists. exists (sh_iv LV iv). split.
+ apply in_map. apply filter_In. split; [exact Hiv|]. unfold Qsn5.nonempty. apply Z.ltb_lt. exact Hne.
+ unfold sh_lo, sh_hi in Z1, Z2. cbn [shadow_off AJO6] in Z1, Z2.
unfold zin, sh_iv, shz, LV_J, L_main_jo6. cbn [lv_shoff fst snd]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt].
* pose proof (Z.div_le_mono (fst iv) (uE E (fst p)) 8 ltac:(lia) H1). lia.
* pose proof (Z.div_le_mono (uE E (fst p) + uE E (snd p)) (snd iv) 8 ltac:(lia) H2).
pose proof (Z.div_mod (snd iv) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd iv) 8 ltac:(lia)).
pose proof (Z.div_mod (snd iv - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd iv - 1) 8 ltac:(lia)). lia.
Qed.

Lemma obj_inside : forall o, In o (OBJS_W w) -> inside_appvis (EMd Instr.M_MUL (ELit 4096) (EVar (fst o)), ELit (snd o)).
Proof.
intros o Ho. exists (wiv2z (obj_e E o)). split; [exact (obj_appvis o Ho)|]. pose proof (obj_pos o Ho) as Pp.
unfold wiv2z, obj_e, uE in *. cbn [fst snd] in *. lia.
Qed.

Definition PRES_PAGE_J : expr * expr :=
(EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (EMd Instr.M_MUL (ELit (-4096)) (EVar 209))) (ELit 137439019008), ELit 4096).
Lemma pres_page_inside : inside_appvis PRES_PAGE_J.
Proof.
assert (Ho : In (208%nat, 137439023104) (OBJS_W w)) by (destruct w; cbn; tauto).
exists (wiv2z (obj_e E (208%nat, 137439023104))). split; [exact (obj_appvis _ Ho)|].
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
destruct (HS2_facts w ch HCL) as (I1 & I2 & _).
pose proof (K _ I1) as K1. pose proof (K _ I2) as K2. unfold F208, F209 in K1, K2. cbn [kentry_ok edenot] in K1, K2.
unfold wiv2z, obj_e, PRES_PAGE_J, uE. cbn [fst snd edenot].
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite !u_lit64a.
set (x208 := bv_unsigned (ev E 208)) in *. set (x209 := bv_unsigned (ev E 209)) in *.
clearbody x208 x209. clear - K1 K2.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma hull_inside : inside_appvis (ELit 65536, ELit 6508544).
Proof.
exists (0x10000, 0x645000). split; [unfold appvis; apply in_app_iff; left; cbn; tauto|].
unfold uE. cbn [fst snd edenot]. rewrite !u64_lit by lia. lia.
Qed.

Definition ov (o : nat * Z) : expr * expr := (EMd Instr.M_MUL (ELit 4096) (EVar (fst o)), ELit (snd o)).

Definition PAGE2_B : expr * expr := (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar 423)) (ELit 4096), ELit 4096).
Definition HULL_J : expr * expr := (ELit 65536, ELit 6508544).
Definition VIS_W (w' : bool) : list (expr * expr) :=
[ov (2129%nat, 4096); ov (496%nat, 4096); ov (479%nat, 8388608); ov (478%nat, 1048576)]
++ (if w' then [ov (423%nat, 4096); ov (5%nat, 8192)] else [ov (424%nat, 4096); PAGE2_B])
++ [ov (406%nat, 11571200); ov (330%nat, 4096); ov (265%nat, 4096); ov (238%nat, 65536); ov (237%nat, 4096); PRES_PAGE_J; ov (207%nat, 3727360);
ov (78%nat, 65536); HULL_J; (e_stacklo, e_stacklen)].
Lemma VIS_eq : a_vis ch = VIS_W w.
Proof. destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity. Qed.

Definition F423 : kentry := KRange (EVar 423) 1 34359736319.
Lemma page2_inside : w = false -> inside_appvis PAGE2_B.
Proof.
intros Hw. assert (Ho : In (423%nat, 8192) (OBJS_W w)) by (rewrite Hw; cbn; tauto).
exists (wiv2z (obj_e E (423%nat, 8192))). split; [exact (obj_appvis _ Ho)|].
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
assert (I1 : In F423 (kn ch)) by (apply kn_mem_In; rewrite Hw in HCL; destruct HCL as [-> | ->]; vm_compute; reflexivity).
pose proof (K _ I1) as K1. unfold F423 in K1. cbn [kentry_ok edenot] in K1.
unfold wiv2z, obj_e, PAGE2_B, uE. cbn [fst snd edenot].
rewrite !u_add64, !u_mul64, !u64_lit by lia.
set (x423 := bv_unsigned (ev E 423)) in *. clearbody x423. clear - K1.
rewrite (Z.mod_small (4096 * x423)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma vis_cases : forall p, In p (a_vis ch) -> inside_appvis p \/ p = (e_stacklo, e_stacklen).
Proof.
intros p Hp. rewrite VIS_eq in Hp.
assert (C : (exists o, In o (OBJS_W w) /\ p = ov o) \/ p = PRES_PAGE_J \/ p = HULL_J \/ (w = false /\ p = PAGE2_B) \/ p = (e_stacklo, e_stacklen)).
{ destruct w; cbn [VIS_W app In] in Hp;
repeat (destruct Hp as [<-|Hp];
[ first [ left; eexists (_, _); split; [ | reflexivity ]; cbn; tauto
| right; left; reflexivity | right; right; left; reflexivity
| right; right; right; left; split; reflexivity | right; right; right; right; reflexivity ] |]);
destruct Hp. }
destruct C as [(o & Ho & ->) | [-> | [-> | [[Hw ->] | ->]]]].
- left. exact (obj_inside o Ho).
- left. exact pres_page_inside.
- left. exact hull_inside.
- left. exact (page2_inside Hw).
- right. reflexivity.
Qed.

Lemma u_stack : uE E e_stacklo = TOPP (bv_unsigned sp) - 8388608 /\ uE E e_stacklen = 2 ^ 47 + 8388608 - TOPP (bv_unsigned sp).
Proof.
pose proof (proj2 (P co_sp0)) as Htop. pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4).
unfold e_stacklo, e_stacklen, eaddz, esub, uE in *.
rewrite !mkAlu_denot. rewrite u_add64, u_sub64. rewrite Htop. cbn [edenot]. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, STACK_MAX, CEIL in *. change (bv_modulus 64) with (2 ^ 64).
clear - T1 T2 T3 T4.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma stack_shadow_zero : forall x : word,
sh_lo AJO6 E (e_stacklo, e_stacklen) <= bv_unsigned x < sh_hi AJO6 E (e_stacklo, e_stacklen) -> FULL x = Some (Z_to_bv 8 0).
Proof.
intros x Hx. unfold sh_lo, sh_hi in Hx. cbn [fst snd shadow_off AJO6] in Hx.
destruct u_stack as [U1 U2]. rewrite U1, U2 in Hx.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (T1 & T2 & T3 & T4). unfold STACK_MAX, CEIL in T4.
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
destruct (HS2_facts w ch HCL) as (_ & _ & I0 & I10 & IZ).
pose proof (K _ I0) as K0. pose proof (K _ I10) as K10. pose proof (K _ IZ) as [_ KZ].
unfold F0, F10 in K0, K10. cbn [kentry_ok edenot] in K0, K10.
pose proof (proj2 (P co_sp0)) as Htop. unfold uE in Htop. rewrite e_top_eq in Htop. cbn [edenot] in Htop.
rewrite u_add64, !u_mul64, !u64_lit in Htop by lia.
unfold estart, elenZ in KZ. cbn [a_base a_off edenot] in KZ.
rewrite !u_add64, !u_mul64 in KZ. rewrite (u64_lit 4096), (u64_lit 512), (u64_lit 0x100000100000) in KZ by lia. rewrite !u_lit64a in KZ.
set (V0 := bv_unsigned (ev E 0)) in *. set (V10 := bv_unsigned (ev E 10)) in *.
rewrite (neg_scale_arith V0 V10 K0 K10) in KZ.
assert (HT : TOPP (bv_unsigned sp) = 32768 * V0 + 4096 * V10).
{ rewrite <- Htop. rewrite (Z.mod_small (32768 * V0)), (Z.mod_small (4096 * V10)), Z.mod_small by lia. reflexivity. }
assert (A1 : (4096 * V0) mod 2 ^ 64 = 4096 * V0) by (apply Z.mod_small; lia).
assert (A2 : (512 * V10) mod 2 ^ 64 = 512 * V10) by (apply Z.mod_small; lia).
rewrite A1, A2 in KZ. rewrite (Z.mod_small (4096 * V0 + 512 * V10)) in KZ by lia.
assert (A3 : (2 ^ 64 - 4096 * V0 - 512 * V10 + 17592187092992) mod 2 ^ 64 = 17592187092992 - 4096 * V0 - 512 * V10).
{ replace (2 ^ 64 - 4096 * V0 - 512 * V10 + 17592187092992) with (17592187092992 - 4096 * V0 - 512 * V10 + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite A3 in KZ.
assert (D1 : (TOPP (bv_unsigned sp) - 8388608) / 8 = 4096 * V0 + 512 * V10 - 1048576).
{ rewrite HT. replace (32768 * V0 + 4096 * V10 - 8388608) with ((4096 * V0 + 512 * V10 - 1048576) * 8) by lia. apply Z.div_mul. lia. }
assert (D2 : (TOPP (bv_unsigned sp) - 8388608 + (2 ^ 47 + 8388608 - TOPP (bv_unsigned sp))) / 8 = 2 ^ 44).
{ replace (TOPP (bv_unsigned sp) - 8388608 + (2 ^ 47 + 8388608 - TOPP (bv_unsigned sp))) with (2 ^ 44 * 8) by lia. apply Z.div_mul. lia. }
rewrite D1, D2 in Hx.
specialize (KZ (bv_unsigned x - (4096 * V0 + 512 * V10 + 2146402304)) ltac:(lia)).
replace (4096 * V0 + 512 * V10 + 2146402304 + (bv_unsigned x - (4096 * V0 + 512 * V10 + 2146402304))) with (bv_unsigned x) in KZ by lia.
rewrite Z_to_bv_bv_unsigned in KZ.
unfold Mr, mrestrict in KZ. destruct (hid _ _ _ _ _ _ x); [discriminate KZ | exact KZ].
Qed.

Lemma band_kinds : forall x : word, in_bands LV x = true ->
in_ivs (bv_unsigned x) (vm_maps h) = true /\ in_ivs (bv_unsigned x) (vm_noaccess h) = false
/\ page_in_ranges (page_base x) (m_vm_lazy mo) = true /\ 0x7fff8000 <= bv_unsigned x < 0x10007fff8000.
Proof.
intros x Hb. unfold in_bands, LV_J, L_main_jo6, in_zivs, zin in Hb. cbn [lv_bands existsb fst snd] in Hb. rewrite orb_false_r in Hb.
pose proof (P co_kinds) as KI. rewrite (MAPS_W_eq w ch HCL), Forall_forall in KI.
apply orb_true_iff in Hb as [Hb|Hb]; apply andb_prop in Hb as [Z1 Z2]; apply Z.leb_le in Z1; apply Z.ltb_lt in Z2.
- assert (Hm : In {| am_base := ELit 2147446784; am_len := ELit 268435456; am_kind := KRWLAZY |} (MAPS_W w)) by (destruct w; vm_compute; tauto).
destruct (KI _ Hm eq_refl x) as [N L]; [cbn [am_base am_len edenot]; rewrite !u64_lit by lia; lia|].
split; [|split; [exact N| split; [exact L| lia]]].
apply in_ivs_true. exists (e_low E). split; [exact (MA e_low_in)|].
unfold e_low. cbn [fst snd edenot]. rewrite !u64_lit by lia. lia.
- assert (Hm : In {| am_base := ELit 2201439137792; am_len := ELit 15392894357504; am_kind := KRWLAZY |} (MAPS_W w)) by (destruct w; vm_compute; tauto).
destruct (KI _ Hm eq_refl x) as [N L]; [cbn [am_base am_len edenot]; rewrite !u64_lit by lia; lia|].
split; [|split; [exact N| split; [exact L| lia]]].
apply in_ivs_true. exists (e_high E). split; [exact (MA e_high_in)|].
unfold e_high. cbn [fst snd edenot]. rewrite !u64_lit by lia. lia.
Qed.

Lemma jsome_main : jsome LV mo FULL.
Proof.
intros x Hb Hhid. destruct (band_kinds x Hb) as (Hm & Hna & Hlz & Hx).
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
destruct (in_allow AJO6 E ch (bv_unsigned x)) eqn:Hal.
-
assert (Hp : exists p, In p (a_vis ch) /\
((uE E (fst p) <=? bv_unsigned x) && (bv_unsigned x <? uE E (fst p) + uE E (snd p))
|| (sh_lo AJO6 E p <=? bv_unsigned x) && (bv_unsigned x <? sh_hi AJO6 E p))%bool = true).
{ unfold in_allow, in_vis, in_sh in Hal. apply orb_true_iff in Hal as [Hal|Hal]; apply existsb_exists in Hal as (p & Hp & Hz);
exists p; (split; [exact Hp|]); rewrite Hz; [reflexivity | apply orb_true_r]. }
destruct Hp as (p & Hp & Hz). destruct (vis_cases p Hp) as [Hin | ->].
+ exfalso. unfold hidden in Hhid. rewrite (inside_allowed p _ Hin Hz) in Hhid. discriminate.
+ apply orb_true_iff in Hz as [Hz|Hz]; apply andb_prop in Hz as [Z1 Z2]; apply Z.leb_le in Z1; apply Z.ltb_lt in Z2.
* exfalso. cbn [fst snd] in Z1. rewrite (proj1 u_stack) in Z1.
pose proof (TOPP_facts _ (usp_ok0 sp Hsp)) as (_ & _ & _ & T4). unfold STACK_MAX, CEIL in T4. lia.
* rewrite (stack_shadow_zero x (conj Z1 Z2)). discriminate.
- assert (Hh : hid AJO6 (bv_unsigned sp) (argH0 JO6PH sp rdraw argv envp uid hw) E ch mo x = true).
{ unfold hid. apply orb_true_iff. right. apply negb_true_iff. unfold vis. rewrite Hm, Hna, Hlz, Hal. cbn [negb andb orb].
unfold in_hull. cbn [img_lo img_hi AJO6].
replace ((65536 <=? bv_unsigned x) && (bv_unsigned x <? 6574080))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
unfold ATOP, STACK_MAX. unfold alloc_top, stack_max_size in AB. rewrite (MA main_init_sp) in AB.
replace (bv_unsigned sp - 8388608 <=? bv_unsigned x) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
assert (Hg : in_ghost AJO6 E ch (bv_unsigned x) = false).
{ unfold in_ghost. replace (in_shwin AJO6 (bv_unsigned x)) with true; [apply andb_false_r|].
symmetry. unfold in_shwin. cbn [shadow_off AJO6]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
rewrite (P co_zero x Hh Hm Hna Hlz Hg). discriminate.
Qed.

Lemma appvis_wf : forall iv, In iv (appvis LV mo) -> fst iv <= snd iv.
Proof.
pose proof (MA main_atop_bounds) as AB.
intros iv Hin. unfold appvis in Hin. apply in_app_iff in Hin as [Hin|Hin].
- cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn; lia.
- apply in_map_iff in Hin as (e & <- & Hin). apply filter_In in Hin as [Hin _]. unfold wiv2z. cbn [fst snd]. pose proof (u64_range (snd e)). lia.
Qed.

Lemma objs_wsum : zsum (map wboth (map wiv2z (map (obj_e E) (OBJS_W w)))) = 37757956.
Proof.
rewrite wsum_objs by (destruct w; repeat constructor; cbn; lia).
destruct w; vm_compute; reflexivity.
Qed.

Lemma cand_bytes_main : cand_bytes LV mo <= 160000000000.
Proof.
unfold cand_bytes. pose proof (cand_pages_le LV mo appvis_wf) as CP.
assert (S : zsum (map wboth (appvis LV mo)) <= 39000000); [|lia].
pose proof (MA main_atop_bounds) as AB.
unfold appvis. rewrite map_app, zsum_app.
rewrite (MA main_vm_maps), !filter_app.
replace (List.filter (fun e => negb (excl_entry LV e)) [e_high E; e_gap E; e_low E]) with (@nil (word * word))
by (cbn [List.filter]; rewrite excl_high, excl_gap, excl_low; reflexivity).
rewrite app_nil_r.

assert (B0 : zsum (map wboth (lv_base LV)) <= 593924).
{ unfold LV_J, L_main_jo6. cbn [lv_base map zsum].
assert (H0 : wboth (0x10000, 0x645000) = 1791) by reflexivity.
assert (H1 : wboth (atopE E, 0x800000000000) <= 592133).
{ unfold wboth, wpages, wshadow. cbn [fst snd].
assert (D1 : (0x800000000000 - atopE E) / 4096 <= 526336) by (apply Z.div_le_upper_bound; lia).
assert (D2 : (0x800000000000 - atopE E) / 8 <= 269484032) by (apply Z.div_le_upper_bound; lia).
assert (D3 : ((0x800000000000 - atopE E) / 8 + 2) / 4096 <= 65793) by (apply Z.div_le_upper_bound; lia).
lia. }
lia. }

assert (NN : forall l : list (word * word), forall x, In x l -> 0 <= wboth (wiv2z x)).
{ intros l x _. rewrite wboth_wiv2z. unfold wlen. pose proof (u64_range (snd x)).
pose proof (Z.div_pos (bv_unsigned (snd x)) 4096). pose proof (Z.div_pos (bv_unsigned (snd x)) 8).
pose proof (Z.div_pos (bv_unsigned (snd x) / 8 + 2) 4096). lia. }
assert (F1 : forall l, zsum (map wboth (map wiv2z (List.filter (fun e => negb (excl_entry LV e)) l))) <= zsum (map wboth (map wiv2z l))).
{ intros l. rewrite !map_map. apply zsum_map_filter_le. intros x Hx. exact (NN l x Hx). }
pose proof (F1 (map (obj_e E) (OBJS_W w))) as O1. rewrite objs_wsum in O1. lia.
Qed.

Lemma main_backing_bound : vm_backing_used mo <= a_eager ch + a_abytes ch.
Proof.
rewrite vm_backing_used_split.
pose proof (P co_minv) as MI. pose proof (P co_eager) as HE. pose proof (P co_abytes) as HA.
pose proof (allowed_pages_bound (allowA AJO6 E ch) (m_vm_materialized mo) (A_wf_allowA AJO6 (fun _ => None) (fun _ _ _ => None) XE0 XB0 0%nat E ch)
(minv_nodup _ _ MI) (minv_aligned _ _ MI) (minv_allowed _ _ MI)) as HP.
unfold page_size in *. lia.
Qed.

Lemma main_backing : vm_backing_used mo <= 2480000000.
Proof.
pose proof main_backing_bound as B.
assert (HAE : a_eager ch + a_abytes ch <= 2480000000) by (apply Z.leb_le; destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity). lia.
Qed.

Lemma main_Phi_bound : Phi LV mo <= 0x2800000000.
Proof. pose proof (Phi_le_cand LV mo). pose proof cand_bytes_main. pose proof main_backing. lia. Qed.

Lemma main_limit : vm_limit h = 0x8000000000.
Proof. rewrite (P co_limit). reflexivity. Qed.

Lemma lv_inv_main : lv_inv LV mo.
Proof. unfold lv_inv. rewrite main_limit. pose proof main_Phi_bound. lia. Qed.

Theorem main_cinvA : forall ms, ms_mem ms = FULL -> cinvA LV ms mo.
Proof.
intros ms Hm. unfold cinvA, cinv. split; [exact xinvA_main|]. split; [exact lv_inv_main|]. rewrite Hm. exact jsome_main.
Qed.
End Cinv.
