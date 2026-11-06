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

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzgH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7z8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYLF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxyE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCoy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCoy. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLPb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QY73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QY73. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q72M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q72M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDRB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDRB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QvDJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo4M. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrQA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrQA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLJz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLJz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFop.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QVyC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.
Set Default Proof Using "All".

Definition pv_ok_in (k : list kentry) (o : nat * Z) : bool :=
existsb (fun K => match K with KRange (EVar v) lo hi => (Nat.eqb v (fst o) && (1 <=? lo) && (hi <=? 34359736319))%bool | _ => false end) k.
Lemma PV_COVER : forall w ch, HSCLASS_S w ch -> forallb (pv_ok_in (kn ch)) (OBJS_W w) = true.
Proof. intros [|] ch [-> | ->]; vm_compute; reflexivity. Qed.

Definition PRES (E : env) : Z := 4096 * bv_unsigned (ev E 208).
Definition SB (E : env) : Z := PRES E + 0x10000 - 4096 * bv_unsigned (ev E 209).
Definition PARR (E : env) : Z := 4096 * bv_unsigned (ev E 236).
Definition F209id : kentry :=
KRange (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit (-4096)) (EVar 209)) (EAlu Instr.ALU_AND (EMd Instr.M_MUL (ELit 4096) (EVar 208)) (ELit 65535))) 0 0.
Lemma HS2_layout_facts : forall w ch, HSCLASS_S w ch -> In F208 (kn ch) /\ In F209 (kn ch) /\ In F209id (kn ch).
Proof. intros w ch HCL. repeat split; apply kn_mem_In; destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity. Qed.

Definition GRP_O (w : bool) : nat * Z := if w then (423%nat, 4096) else (424%nat, 4096).
Definition META_O (w : bool) : nat * Z := if w then (5%nat, 8192) else (423%nat, 8192).

Definition OBJS_K (w : bool) : list (nat * Z) :=
[(2129%nat, 4096); (496%nat, 4096); (479%nat, 8388608); (478%nat, 1048576); META_O w;
(406%nat, 11571200); (330%nat, 4096); (265%nat, 4096); (238%nat, 65536); (237%nat, 4096); (207%nat, 3727360); (78%nat, 65536)].
Lemma OBJS_K_sub : forall w o, In o (OBJS_K w) -> In o (OBJS_W w).
Proof. intros [|] o Ho; cbn in Ho |- *; tauto. Qed.
Lemma GRP_O_in : forall w, In (GRP_O w) (OBJS_W w).  Proof. intros [|]; cbn; tauto. Qed.
Lemma PRES_O_in : forall w, In (208%nat, 137439023104) (OBJS_W w).  Proof. intros [|]; cbn; tauto. Qed.
Lemma PARR_O_in : forall w, In (236%nat, 8388608) (OBJS_W w).  Proof. intros [|]; cbn; tauto. Qed.
Definition objs_of (w : bool) (E : env) : list (Z * Z) := map (fun o => wiv2z (obj_e E o)) (OBJS_K w).

Section Ledger.
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
#[local] Notation LV := (LV_J E).
#[local] Notation P f := (f _ _ _ _ _ _ _ _ _ _ _ _ CS) (only parsing).
#[local] Notation MA L := (L sp rdraw brk0 argv envp fs uid hw Hsp E R FULL mo w ch HCL CS) (only parsing).

Lemma pv_bound : forall o, In o (OBJS_W w) -> 1 <= bv_unsigned (ev E (fst o)) <= 34359736319.
Proof.
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
pose proof (PV_COVER w ch HCL) as PC. rewrite forallb_forall in PC.
intros o Ho. pose proof (PC o Ho) as X. unfold pv_ok_in in X. apply existsb_exists in X as (K' & HK' & Hok).
destruct K' as [| | | | |e lo hi| | | |]; try discriminate. destruct e; try discriminate.
apply andb_prop in Hok as [Hok H2]. apply andb_prop in Hok as [H0 H1]. apply Nat.eqb_eq in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (K _ HK') as Kx. cbn [kentry_ok edenot] in Kx. subst n. lia.
Qed.

Lemma obj_len_bound : forall o, In o (OBJS_W w) -> 0 < snd o < 2^40.
Proof. intros o Ho. destruct w; cbn in Ho; repeat (destruct Ho as [<-|Ho]; [cbn; lia|]); destruct Ho. Qed.

Lemma u_obj_base : forall o, In o (OBJS_W w) -> bv_unsigned (fst (obj_e E o)) = 4096 * bv_unsigned (ev E (fst o)).
Proof.
intros o Ho. pose proof (pv_bound o Ho). unfold obj_e. cbn [fst edenot]. rewrite u_mul64, u64_lit by lia.
rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma u_obj_len : forall o, In o (OBJS_W w) -> bv_unsigned (snd (obj_e E o)) = snd o.
Proof. intros o Ho. pose proof (obj_len_bound o Ho). unfold obj_e. cbn [snd edenot]. rewrite u64_lit by lia. reflexivity. Qed.

Lemma obj_lowhigh : forall o, In o (OBJS_W w) ->
bv_unsigned (fst (obj_e E o)) + bv_unsigned (snd (obj_e E o)) <= QzgH.kLowEnd
\/ Qqcs.Mq0.kHighMemBeg <= bv_unsigned (fst (obj_e E o)).
Proof.
intros o Ho. destruct ((MA obj_ne) o Ho) as (N1 & N2 & N3).
pose proof ((MA in_maps_obj) o Ho) as Hin.
pose proof ((MA maps_disj) _ _ Hin (MA e_low_in) N1) as D1.
pose proof ((MA maps_disj) _ _ Hin (MA e_gap_in) N2) as D2.
pose proof ((MA maps_disj) _ _ Hin (MA e_high_in) N3) as D3.
pose proof ((MA maps_pos) _ Hin) as Pp.
unfold iv_disjoint, e_low, e_gap, e_high in D1, D2, D3. cbn [fst snd] in D1, D2, D3. rewrite !(u_litE E) in D1, D2, D3 by lia.
unfold QzgH.kLowEnd, Qqcs.Mq0.kHighMemBeg. lia.
Qed.

Lemma z2w_wiv2z : forall e : word * word, bv_unsigned (fst e) + bv_unsigned (snd e) < 2^64 -> QzgH.z2w (wiv2z e) = e.
Proof.
intros [b n] Hb. unfold QzgH.z2w, QzgH.w64, wiv2z. cbn [fst snd] in *. pose proof (u64_range b). pose proof (u64_range n).
f_equal; apply bv_eq; rewrite u64_lit by lia; lia.
Qed.

Lemma entry_top : forall e, In e (vm_maps h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top h.
Proof. exact (MA maps_below_atop). Qed.

Lemma entry_perm : forall e, In e (vm_maps h) ->
let r := wiv2z e in
In (QzgH.z2w r) (vm_maps h) /\
(forall e', In e' (vm_maps h) -> e' = QzgH.z2w r \/ QzgH.zdisj (wiv2z e') r) /\
count_occ QzgH.pdec (vm_maps h) (QzgH.z2w r) = 1%nat /\
region_free (vm_reserved h) (fst (QzgH.z2w r)) (snd (QzgH.z2w r)) = true.
Proof.
intros e He r. pose proof (entry_top e He) as T. pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
assert (EQ : QzgH.z2w r = e) by (apply z2w_wiv2z; lia). rewrite EQ.
split; [exact He|]. split; [|split].
- intros e' He'. destruct (decide (e' = e)) as [->|Hne]; [left; reflexivity| right].
pose proof ((MA maps_disj) _ _ He' He Hne) as D. unfold iv_disjoint in D. unfold QzgH.zdisj, r, wiv2z. cbn [fst snd]. lia.
- apply (proj1 (NoDup_count_occ' QzgH.pdec (vm_maps h))); [|exact He].
exact (QYLF.Mq0.seps_NoDup _ (P co_seps) (MA maps_pos)).
- apply QYLF.Mq0.region_free_intro. intros a sz Hin. rewrite (P co_res) in Hin.
pose proof asan_res_hull as RH. rewrite Forall_forall in RH. pose proof (RH _ Hin) as [R1 R2]. cbn [fst snd img_lo img_hi AJO6] in R1, R2.
pose proof (P co_bounds) as B. rewrite Forall_forall in B. pose proof (B e He) as (_ & _ & _ & B4 & _).
cbn [img_lo img_hi AJO6] in B4.
unfold iv_overlap. apply andb_false_iff. destruct B4 as [B4|B4]; [right| left]; apply Z.ltb_ge; lia.
Qed.

Lemma pres_obj : (PRES E, PRES E + Q7z8.kPrimResLen) = wiv2z (obj_e E (208%nat, 137439023104)).
Proof. unfold wiv2z. rewrite (u_obj_base _ (PRES_O_in w)), (u_obj_len _ (PRES_O_in w)). unfold PRES, Q7z8.kPrimResLen. reflexivity. Qed.
Lemma parr_obj : (PARR E, PARR E + Q7z8.kPtrArrLen) = wiv2z (obj_e E (236%nat, 8388608)).
Proof. unfold wiv2z. rewrite (u_obj_base _ (PARR_O_in w)), (u_obj_len _ (PARR_O_in w)). unfold PARR, Q7z8.kPtrArrLen. reflexivity. Qed.

Lemma sb_layout : SB E mod 65536 = 0 /\ PRES E <= SB E /\ SB E + 2 ^ 37 <= PRES E + 0x2000011000.
Proof.
pose proof (P co_know) as K. unfold know_ok in K. rewrite Forall_forall in K.
destruct (HS2_layout_facts w ch HCL) as (I1 & I2 & I3).
pose proof (K _ I1) as K1. pose proof (K _ I2) as K2. pose proof (K _ I3) as K3.
unfold F208, F209, F209id in *. cbn [kentry_ok edenot] in K1, K2, K3.
rewrite u_add64, u_mul64, u_and64, u_mul64, !u_lit64 in K3. unfold two64 in K3.
set (x208 := bv_unsigned (ev E 208)) in *. set (x209 := bv_unsigned (ev E 209)) in *.
unfold SB, PRES. fold x208 x209.
assert (Hm208 : (4096 mod 2 ^ 64 * x208) mod 2 ^ 64 = 4096 * x208) by (rewrite Z.mod_small; [rewrite (Z.mod_small 4096); lia | rewrite (Z.mod_small 4096) by lia; lia]).
rewrite Hm208 in K3.
rewrite (Z.mod_small 65535) in K3 by lia. change 65535 with (Z.ones 16) in K3. rewrite Z.land_ones in K3 by lia.
assert (Hid : 4096 * x209 = (4096 * x208) mod 2 ^ 16).
{ pose proof (Z.mod_pos_bound (4096 * x208) (2 ^ 16) ltac:(lia)) as B.
set (r := (4096 * x208) mod 2 ^ 16) in *. clearbody r.
destruct (Z.eq_dec x209 0) as [Z0|Z0].
- rewrite Z0 in K3 |- *. rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_l in K3 by lia. rewrite Z.mod_small in K3 by lia. lia.
- assert (Hneg : ((-4096) mod 2 ^ 64 * x209) mod 2 ^ 64 = 2 ^ 64 - 4096 * x209).
{ rewrite Z.mul_mod_idemp_l by lia. replace (-4096 * x209) with ((2 ^ 64 - 4096 * x209) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
rewrite Hneg in K3.
destruct (Z.lt_ge_cases r (4096 * x209)) as [Hlt|Hge].
+ exfalso. rewrite Z.mod_small in K3 by lia. lia.
+ replace (2 ^ 64 - 4096 * x209 + r) with ((r - 4096 * x209) + 1 * 2 ^ 64) in K3 by lia.
rewrite Z.mod_add in K3 by lia. rewrite Z.mod_small in K3 by lia. lia. }
pose proof (Z.div_mod (4096 * x208) (2 ^ 16) ltac:(lia)) as DM.
pose proof (Z.mod_pos_bound (4096 * x208) (2 ^ 16) ltac:(lia)) as B16.
split; [|change (2 ^ 16) with 65536 in *; change (2 ^ 37) with 137438953472; lia].
replace (4096 * x208 + 65536 - 4096 * x209) with (((4096 * x208) / 2 ^ 16 + 1) * 65536)
by (rewrite Hid; change (2 ^ 16) with 65536 in *; lia).
apply Z_mod_mult.
Qed.

Lemma main_addrs : Q7z8.main_addrs_ok (SB E) (PRES E) (PARR E).
Proof.
destruct sb_layout as (S1 & S2 & S3).
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
pose proof (obj_lowhigh _ (PRES_O_in w)) as LH1. pose proof (obj_lowhigh _ (PARR_O_in w)) as LH2.
pose proof (entry_top _ ((MA in_maps_obj) _ (PRES_O_in w))) as T1. pose proof (entry_top _ ((MA in_maps_obj) _ (PARR_O_in w))) as T2.
pose proof (pv_bound _ (PRES_O_in w)) as B1. pose proof (pv_bound _ (PARR_O_in w)) as B2. cbn [fst] in B1, B2.
rewrite (u_obj_base _ (PRES_O_in w)), (u_obj_len _ (PRES_O_in w)) in LH1, T1.
rewrite (u_obj_base _ (PARR_O_in w)), (u_obj_len _ (PARR_O_in w)) in LH2, T2. cbn [fst snd] in LH1, LH2, T1, T2.
assert (PM : (4096 * bv_unsigned (ev E 236)) mod 4096 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
constructor; unfold Q7z8.lowhigh, QzgH.kLowEnd, Qqcs.Mq0.kHighMemBeg, Q7z8.kPrimResLen,
Q7z8.kPtrArrLen, Q7z8.CEIL, PRES, PARR in *; cbn [fst snd]; try lia; try exact PM;
lia.
Qed.

Lemma main_objs_ok : Q7z8.objs_ok (objs_of w E).
Proof.
unfold Q7z8.objs_ok, objs_of. apply Forall_forall. intros r Hr. apply in_map_iff in Hr as (o & <- & Ho).
apply OBJS_K_sub in Ho. pose proof (obj_lowhigh o Ho) as LH. pose proof (pv_bound o Ho) as PB.
pose proof (u_obj_base o Ho) as UB. pose proof ((MA obj_pos) o Ho) as Pp.
pose proof (entry_top _ ((MA in_maps_obj) o Ho)) as T.
pose proof (MA main_atop_bounds) as AB. rewrite (MA main_atop) in AB.
unfold Q7z8.lowhigh, Q7z8.CEIL, wiv2z. cbn [fst snd].
unfold QzgH.kLowEnd, Qqcs.Mq0.kHighMemBeg in *. lia.
Qed.

Lemma excl_mapped_main : excl_mapped LV mo.
Proof.
intros x y Hx Hy. cbn in Hx. rewrite <- QxyE.in_ivs_covered. apply in_ivs_true.
destruct Hx as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Hy.
- exists (e_low E). split; [exact (MA e_low_in)|]. unfold e_low. cbn [fst snd]. rewrite !(u_litE E) by lia. lia.
- exists (e_gap E). split; [exact (MA e_gap_in)|]. unfold e_gap. cbn [fst snd]. rewrite !(u_litE E) by lia. lia.
- exists (e_high E). split; [exact (MA e_high_in)|]. unfold e_high. cbn [fst snd]. rewrite !(u_litE E) by lia. lia.
Qed.

Lemma resv_low : forall e, In e (vm_reserved h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= QzgH.kLowEnd.
Proof.
intros e He. rewrite (P co_res) in He.
pose proof asan_res_hull as RH. rewrite Forall_forall in RH. pose proof (RH _ He) as [R1 R2]. cbn [img_lo img_hi AJO6] in R1, R2.
unfold QzgH.kLowEnd. lia.
Qed.

Lemma hull_reserved : forall y, 0x10000 <= y < 0x645000 ->
exists e, In e (vm_reserved h) /\ bv_unsigned (fst e) <= y < bv_unsigned (fst e) + bv_unsigned (snd e).
Proof.
intros y Hy. rewrite (P co_res), asan_segments_reserved.
destruct (Z.lt_ge_cases y 0x3d000); [exists (Z_to_bv 64 0x10000, Z_to_bv 64 0x2d000); split; [cbn; tauto| cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
destruct (Z.lt_ge_cases y 0xe2000); [exists (Z_to_bv 64 0x3d000, Z_to_bv 64 0xa5000); split; [cbn; tauto| cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
destruct (Z.lt_ge_cases y 0xe7000); [exists (Z_to_bv 64 0xe2000, Z_to_bv 64 0x5000); split; [cbn; tauto| cbn [fst snd]; rewrite !u64_lit by lia; lia]|].
exists (Z_to_bv 64 0xe7000, Z_to_bv 64 0x55e000). split; [cbn; tauto| cbn [fst snd]; rewrite !u64_lit by lia; lia].
Qed.

Lemma sum_sizes_gw : forall l, Qqcs.Mq0.gw_sizes l = sum_sizes l.
Proof. induction l as [|iv l IH]; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Definition TOT_J : Z := 17729700000000.
Lemma main_tot : Qqcs.Mq0.gw_sizes (vm_reserved h ++ vm_maps h) <= TOT_J.
Proof.
rewrite sum_sizes_gw. pose proof (P co_totsz) as T.
assert (HTS : a_totsz ch <= TOT_J) by (apply Z.leb_le; destruct w; destruct HCL as [-> | ->]; vm_compute; reflexivity). lia.
Qed.

Lemma main_len : QOb0.Mq0.zlen (vm_reserved h ++ vm_maps h) = 22.
Proof.
unfold QOb0.Mq0.zlen. rewrite (P co_res), asan_segments_reserved, (MA main_vm_maps). rewrite !length_app, length_map.
destruct w; reflexivity.
Qed.

Lemma base_cov : forall PERM iv y, In iv (lv_base LV) -> fst iv <= y < snd iv ->
alloc_top h <= y \/ QzgH.app_cov LV PERM h y \/ (exists y', QzgH.app_cov LV PERM h y' /\ y = shz LV y').
Proof.
intros PERM iv y Hiv Hy. unfold LV_J, L_main_jo6 in Hiv. cbn [lv_base In] in Hiv. destruct Hiv as [<-|[<-|[]]]; cbn [fst snd] in Hy.
- right. left. left. exact (hull_reserved y Hy).
- left. rewrite <- (MA main_atop). lia.
Qed.

Definition GRPB : Z := 4096 * bv_unsigned (ev E (fst (GRP_O w))).
Lemma grp_obj : QvDJ.civ (GRPB, 4096) = wiv2z (obj_e E (GRP_O w)).
Proof.
unfold QvDJ.civ, wiv2z, GRPB. rewrite (u_obj_base _ (GRP_O_in w)), (u_obj_len _ (GRP_O_in w)). cbn [fst snd]. destruct w; reflexivity.
Qed.

Lemma obj_e_inj : forall o o', In o (OBJS_W w) -> In o' (OBJS_W w) -> obj_e E o = obj_e E o' -> o = o'.
Proof.
intros o o' Ho Ho' Heq.
pose proof (QYLF.Mq0.seps_NoDup _ (P co_seps) (MA maps_pos)) as ND. rewrite (MA main_vm_maps) in ND.
apply NoDup_app_remove_r in ND.
clear - ND Ho Ho' Heq. revert ND Ho Ho'. induction (OBJS_W w) as [|x l IH]; intros ND Ho Ho'; [destruct Ho|]. cbn [map] in ND. inversion ND as [|y l' Hni ND']; subst.
destruct Ho as [->|Ho], Ho' as [->|Ho']; [reflexivity | | | exact (IH ND' Ho Ho')].
- exfalso. apply Hni. rewrite Heq. apply in_map. exact Ho'.
- exfalso. apply Hni. rewrite <- Heq. apply in_map. exact Ho.
Qed.

Definition PERM0_J : list (Z * Z) := Q7z8.PERM_main (PRES E) (PARR E) (objs_of w E).
Definition PERMc_J : list (Z * Z) := QvDJ.civ (GRPB, 4096) :: PERM0_J.

Lemma perm_entry : forall r, In r PERMc_J -> exists e, In e (vm_maps h) /\ r = wiv2z e.
Proof.
intros r Hr. destruct Hr as [<-|Hr].
- exists (obj_e E (GRP_O w)). split; [exact ((MA in_maps_obj) _ (GRP_O_in w)) | exact grp_obj].
- unfold PERM0_J, Q7z8.PERM_main in Hr. apply in_app_iff in Hr as [Hr|Hr].
+ cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
* exists (obj_e E (208%nat, 137439023104)). split; [exact ((MA in_maps_obj) _ (PRES_O_in w)) | exact pres_obj].
* exists (obj_e E (236%nat, 8388608)). split; [exact ((MA in_maps_obj) _ (PARR_O_in w)) | exact parr_obj].
* exists (e_high E). split; [exact (MA e_high_in) | rewrite (MA e_high_z); reflexivity].
* exists (e_low E). split; [exact (MA e_low_in) | rewrite (MA e_low_z); reflexivity].
* exists (e_gap E). split; [exact (MA e_gap_in) | rewrite (MA e_gap_z); reflexivity].
+ unfold objs_of in Hr. apply in_map_iff in Hr as (o & <- & Ho). exists (obj_e E o). split; [|reflexivity].
apply (MA in_maps_obj). apply OBJS_K_sub. exact Ho.
Qed.

Definition BC_J : Z := 0x5800000000.

Theorem KI_main_J : forall g0, QvDJ.g_chunks g0 = [] -> 0 <= QvDJ.g_spent g0 ->
QzgH.KI LV BC_J PERMc_J TOT_J 22 g0 mo.
Proof.
intros g0 Hch Hsp0. constructor; rewrite ?Hch.
- exact (MA xinvA_main).
- exact excl_mapped_main.
- intros r Hr. destruct (perm_entry r Hr) as (e & He & ->). destruct (entry_perm e He) as (A1 & A2 & A3 & A4).
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. intros c Hc. rewrite Hch in Hc. destruct Hc.
- intros c Hc. rewrite ?Hch in Hc. destruct Hc.
- constructor.
- exact (MA maps_pos).
- exact Hsp0.
- pose proof (MA main_Phi_bound). rewrite (MA main_limit). unfold BC_J. lia.
- exact resv_low.
- exact (base_cov PERMc_J).
- cbn [map]. change (QPa2.zsum []) with 0. change (QOb0.Mq0.zlen (@nil (Z * Z))) with 0.
pose proof main_tot. rewrite main_len. lia.
Qed.

Theorem ll_ok_main_J :
QzgH.ll_ok (QVyC.LA_J (SB E) (PRES E) (PARR E) (objs_of w E) (atopE E)) LV 0 PERM0_J QVyC.TMAX_J QVyC.NMAX_J.
Proof.
pose proof (MA main_atop_bounds) as AB.
apply QVyC.ll_ok_J; [apply QVyC.L_main_jo6_alloc_ok | exact main_addrs | exact main_objs_ok | cbn; tauto | cbn; tauto | lia].
Qed.
End Ledger.
