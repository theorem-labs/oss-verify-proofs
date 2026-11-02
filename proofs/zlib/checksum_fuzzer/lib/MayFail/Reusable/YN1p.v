(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN1p.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0c.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0x.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0k.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN2b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1z.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN20.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1y.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN1q.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bt_ltu a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_LTU (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros Ha Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !lit64_small by assumption. reflexivity. Qed.
Lemma bt_geu a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_GEU (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros Ha Hb. cbn [branch_taken]. unfold bv_ltu. rewrite !lit64_small by assumption. reflexivity. Qed.
Lemma bt_eq a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_EQ (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros Ha Hb. cbn [branch_taken]. unfold bv_eqb. rewrite !lit64_small by assumption. reflexivity. Qed.
Lemma bt_ne a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> branch_taken BC_NE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a =? b).
Proof. intros Ha Hb. cbn [branch_taken]. unfold bv_eqb. rewrite !lit64_small by assumption. reflexivity. Qed.
End c.
Ltac lits := unfold DEB, SCT, src0_D_debruijn32, src0_D_size_classes in *.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section T0.
Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (n : Z).
Hypothesis PRE : call_pre B (MRx B) L A regs mem md.
Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 n.
Let rom := seg_rom src0segs.
Definition SP0 : Z := spZ regs.
Definition kk : Z := (n + 3) / 16.
Lemma PRE_facts : MRx B L A mem md /\ WF A /\ bounded A /\ YK0s.ret_ok (getr regs 1) /\
SP0 mod 16 = 0 /\ alloc_ceiling + 8192 <= SP0 /\ SP0 < 2 ^ 63 /\
(forall a, SP0 - 8192 <= a < SP0 -> writable_at src0segs mem a) /\ getr regs 4 = Z_to_bv 64 (ms_tp B) /\
(forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at src0segs mem a) /\
(st_init_done A = false -> auxv_pre B (ly_sec L) SP0 mem).
Proof. unfold call_pre, ALLOC_STACK in PRE. exact PRE. Qed.
Lemma kk_facts : 0 <= kk <= 8190 /\ (n < 157 <-> kk < 10) /\ size_to_class n = class_of_units kk.
Proof.
unfold kk, size_to_class, MMAP_THRESHOLD, IB in *. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
replace (n + 4 - 1) with (n + 3) by lia. split; [|split; [|reflexivity]].
- assert ((n + 3) / 16 < 8191) by (apply Z.div_lt_upper_bound; lia). split; [apply Z.div_pos; lia | lia].
- split; intros H; [apply Z.div_lt_upper_bound; lia|]. destruct (Z_lt_le_dec n 157) as [Hl|Hl]; [exact Hl|].
exfalso. assert (10 <= (n + 3) / 16) by (apply Z.div_le_lower_bound; lia). lia.
Qed.
Record at_PA (regs1 : bvmap 5 word) (mem1 : word -> option byte) : Prop := PA_ {
pa_20 : getr regs1 20 = Z_to_bv 64 (size_to_class n);
pa_8 : getr regs1 8 = Z_to_bv 64 n;
pa_9 : getr regs1 9 = Z_to_bv 64 LOCK;
pa_19 : getr regs1 19 = Z_to_bv 64 DEB;
pa_2 : getr regs1 2 = Z_to_bv 64 (SP0 - 48);
pa_4 : getr regs1 4 = Z_to_bv 64 TP;
pa_cs : forall i, In i CSAVED -> getr regs1 (nat_to_reg i) = getr regs (nat_to_reg i);
pa_frame : forall off r, In (off, r) FRAME_SLOTS -> bytes_are mem1 (SP0 - 48 + off) 8 (bv_unsigned (getr regs (nat_to_reg r)));
pa_out : forall x, 0 <= x < 2 ^ 64 -> ~ (SP0 - 48 <= x < SP0) -> mem1 (Z_to_bv 64 x) = mem (Z_to_bv 64 x);
pa_win : forall a, SP0 - 48 <= a < SP0 -> writable_at src0segs mem1 a }.
Definition xs (i : nat) : Z := if (i <? 32)%nat then bv_unsigned (getr regs (nat_to_reg i)) else if Nat.eqb i aK then kk else 0.
Definition xb (i : nat) : Z := if (i <? 32)%nat then bv_unsigned (getr regs (nat_to_reg i)) else xv_of (t0_env kk) i.
Lemma xs_reg k : (k <= 31)%nat -> xs k = bv_unsigned (getr regs (nat_to_reg k)).
Proof. intros Hk. unfold xs. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma xb_reg k : (k <= 31)%nat -> xb k = bv_unsigned (getr regs (nat_to_reg k)).
Proof. intros Hk. unfold xb. replace (k <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. Qed.
Lemma X10 : bv_unsigned (getr regs (nat_to_reg 10)) = n.
Proof. change (nat_to_reg 10) with (10%bv : bv 5). rewrite R10. apply lit64_small. unfold MMAP_THRESHOLD in Hn. lia. Qed.
Lemma X2 : bv_unsigned (getr regs (nat_to_reg 2)) = SP0.
Proof. reflexivity. Qed.
Lemma XRs : forall k, 0 <= xs k < 2 ^ 64.
Proof.
intros k. pose proof kk_facts as (K & _). unfold xs. destruct (k <? 32)%nat; [apply u64_range|]. destruct (Nat.eqb k aK); lia.
Qed.
Section f.
Hypothesis BIG : 157 <= n.
Let e := t0_e kk.
Lemma kk_big : 10 <= kk <= 8190.
Proof. pose proof kk_facts as (K1 & K2 & _). destruct (Z_lt_le_dec kk 10); [exfalso; apply K2 in l; lia | lia]. Qed.
Lemma BF : andx_f kk = 2 ^ e /\ UZof (t0_env kk) TQ1X = DEB + dbj_idx (2 ^ e) /\ UZof (t0_env kk) TQ2X = SCT + 2 * (4 * e - 3) /\
UZof (t0_env kk) (TQ3X (t0_b1 kk)) = SCT + 2 * t0_i3 kk /\ UZof (t0_env kk) (RESX (t0_b1 kk)) = class_of_units kk /\
3 <= e <= 12 /\ znth (dbj_idx (2 ^ e)) DEBRUIJN = e.
Proof. exact (t0_facts kk kk_big). Qed.
Lemma e_facts : 3 <= e <= 12 /\ 8 <= 2 ^ e <= 4096 /\ 0 <= dbj_idx (2 ^ e) < 32 /\ 9 <= 4 * e - 3 <= 45 /\
8 <= t0_i3 kk <= 46 /\ t0_i3 kk <> 4 * e - 3 /\ 1 <= t0_t1 kk <= 8191 /\ 1 <= znth (t0_i3 kk) size_classes <= 8191.
Proof.
pose proof BF as (_ & _ & _ & _ & _ & He & _).
assert (P : 8 <= 2 ^ e <= 4096).
{ split; [change 8 with (2 ^ 3); apply Z.pow_le_mono_r; lia | change 4096 with (2 ^ 12); apply Z.pow_le_mono_r; lia]. }
pose proof (dbj_idx_range (2 ^ e)) as D.
assert (I3 : 8 <= t0_i3 kk <= 46 /\ t0_i3 kk <> 4 * e - 3) by (unfold t0_i3; fold e; destruct (t0_b1 kk); lia).
split; [exact He|]. split; [exact P|]. split; [exact D|]. split; [lia|]. split; [exact (proj1 I3)|]. split; [exact (proj2 I3)|].
split; [unfold t0_t1; fold e; apply size_classes_range; lia | apply size_classes_range; lia].
Qed.
Lemma XRb : forall k, 0 <= xb k < 2 ^ 64.
Proof.
intros k. pose proof kk_big as K. pose proof e_facts as (E1 & E2 & E3 & E4 & E5 & _ & E7 & E8).
unfold xb. destruct (k <? 32)%nat; [apply u64_range|].
unfold xv_of, t0_env. fold e. lits.
do 41 (destruct k as [|k]; [cbn [xv_of t0_env find fst snd aK aE aP aTQ1 aT1 aTQ2 aT2 aTQ3 Nat.eqb]; lia|]).
cbn [xv_of t0_env find fst snd aK aE aP aTQ1 aT1 aTQ2 aT2 aTQ3 Nat.eqb]. lia.
Qed.
Lemma xb_env : forall p, In p (t0_env kk) -> xb (fst p) = snd p.
Proof.
intros p Hp. unfold t0_env in Hp. cbn [In] in Hp.
decompose [or] Hp; try contradiction; subst p; reflexivity.
Qed.
Lemma big_denots :
sv_denot (EV xb) ANDX = Z_to_bv 64 (2 ^ e) /\
sv_denot (EV xb) TQ1X = Z_to_bv 64 (DEB + dbj_idx (2 ^ e)) /\
sv_denot (EV xb) TQ2X = Z_to_bv 64 (SCT + 2 * (4 * e - 3)) /\
sv_denot (EV xb) (TQ3X (t0_b1 kk)) = Z_to_bv 64 (SCT + 2 * t0_i3 kk) /\
sv_denot (EV xb) (RESX (t0_b1 kk)) = Z_to_bv 64 (class_of_units kk).
Proof.
pose proof BF as (F1 & F2 & F3 & F4 & F5 & _).
split. { rewrite UZ_sound, andx_f_ok. change (xb aK) with kk. rewrite F1. reflexivity. }
split. { rewrite (UZ_by_atoms (t0_env kk) xb TQ1X eq_refl xb_env), F2. reflexivity. }
split. { rewrite (UZ_by_atoms (t0_env kk) xb TQ2X eq_refl xb_env), F3. reflexivity. }
split. { rewrite (UZ_by_atoms (t0_env kk) xb (TQ3X (t0_b1 kk))), F4; [reflexivity | destruct (t0_b1 kk); reflexivity | exact xb_env]. }
rewrite (UZ_by_atoms (t0_env kk) xb (RESX (t0_b1 kk))), F5; [reflexivity | destruct (t0_b1 kk); reflexivity | exact xb_env].
Qed.
End f.
Lemma frame0_ok xv : (forall k, 0 <= xv k < 2 ^ 64) -> xv 2%nat = SP0 -> region_ok src0segs (EV xv) mem R_frame0.
Proof.
intros XR X2'. pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & Hstk & _). pose proof (proj1 alloc_ceiling_val).
apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_frame0]; rewrite (base_val_EV xv XR), X2'; [lia | lia | | apply Forall_nil].
intros o Ho. apply Hstk. lia.
Qed.
Lemma regs_ok0 xv : (forall k, (k <= 31)%nat -> xv k = bv_unsigned (getr regs (nat_to_reg k))) -> regs_ok (EV xv) (regs_lit [(4%nat, TP)]) regs.
Proof.
intros XV. pose proof PRE_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Htp & _).
apply regs_ok_lit. intros k Hk. destruct (Nat.eq_dec k 4) as [->|Hk4]; [cbn; exact Htp|].
replace (find (fun p : nat * Z => Nat.eqb (fst p) k) [(4%nat, TP)]) with (@None (nat * Z)).
2:{ cbn [find fst]. replace (Nat.eqb 4 k) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
rewrite XV by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma sp_fact xv : (forall k, 0 <= xv k < 2 ^ 64) -> xv 2%nat = SP0 -> afact_ok (EV xv) 2%nat F_spE.
Proof.
intros XR X2'. pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val).
unfold afact_ok. cbn [af_lo af_hi af_al2 F_spE]. rewrite (ew_EV xv XR), X2'. unfold CEIL. change (2 ^ 4) with 16. lia.
Qed.
Lemma alias_k xv : (forall k, 0 <= xv k < 2 ^ 64) -> xv 10%nat = n -> xv aK = kk ->
sv_denot (EV xv) (SAlu ALU_SRL (SOff 10 3) (SLit 4)) = sv_denot (EV xv) (SOff aK 0).
Proof.
intros XR Xn Xk. pose proof kk_facts as (K & _). unfold MMAP_THRESHOLD in Hn.
rewrite !UZ_sound. f_equal. cbn [UZ]. rewrite Xn, Xk. unfold zalu64. cbn [zalu_raw].
rewrite !(zcanon_id n), !(zcanon_id 4), !(zcanon_id (n + 3)), !(zcanon_id kk), Z.add_0_r, (zcanon_id kk) by (unfold M64; lia).
change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. fold kk. apply zcanon_id. unfold M64. lia.
Qed.
Lemma T0s_st_ok : n < 157 -> st_ok src0segs (EV xs) ss_T0s (mkst regs (Z_to_bv 64 src0_A_malloc) mem rom).
Proof.
intros SMALL. pose proof kk_facts as (K1 & K2 & _). pose proof XRs as XR.
assert (XSP : xs 2%nat = SP0) by (rewrite xs_reg by lia; reflexivity).
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T0s resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok0. intros k Hk. apply xs_reg. lia.
- split; [vm_compute; reflexivity|]. split; [| cbn [pairwise_disjoint all_disjoint t0s_mem]; exact (conj I I)].
apply Forall_cons; [apply (frame0_ok xs XR XSP) | apply Forall_nil].
- split; [|split; [exact I|]].
+ cbn [atoms_ok t0s_facts f_atoms]. split; [apply (sp_fact xs XR XSP)|]. split; [|split; [|exact I]].
* unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_EV xs XR), xs_reg, X10 by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
* unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite (ew_EV xs XR). change (xs aK) with kk. change (2 ^ 0) with 1. rewrite Z.mod_1_r.
assert (kk < 10) by (apply K2; exact SMALL). lia.
+ cbn [alias_ok t0s_facts f_alias AL_k]. split; [|exact I]. apply (alias_k xs XR); [rewrite xs_reg by lia; apply X10 | reflexivity].
Qed.
Lemma T0b_st_ok : 157 <= n -> st_ok src0segs (EV xb) (ss_T0b (t0_b1 kk)) (mkst regs (Z_to_bv 64 src0_A_malloc) mem rom).
Proof.
intros BIG. pose proof (kk_big BIG) as K. pose proof (XRb BIG) as XR. pose proof (e_facts BIG) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
pose proof (big_denots BIG) as (D1 & D2 & D3 & D4 & D5). pose proof (BF BIG) as (_ & _ & _ & _ & _ & _ & Fdbj).
set (e := t0_e kk) in *.
pose proof PRE_facts as (MX & _ & _ & _ & Hal & Hceil & Hsp63 & Hstk & _). pose proof (proj1 alloc_ceiling_val) as HCV.
pose proof (mid_statics _ _ _ _ _ (MRx_midrep B L A mem md MX)) as ST.
assert (XSP : xb 2%nat = SP0) by (rewrite xb_reg by lia; reflexivity).
assert (XK : xb aK = kk) by reflexivity.
assert (XE : xb aE = e) by reflexivity.
assert (XP : xb aP = 2 ^ e) by reflexivity.
assert (XQ1 : xb aTQ1 = DEB + dbj_idx (2 ^ e)) by reflexivity.
assert (XT1 : xb aT1 = t0_t1 kk) by reflexivity.
assert (XQ2 : xb aTQ2 = SCT + 2 * (4 * e - 3)) by reflexivity.
assert (XT2 : xb aT2 = znth (t0_i3 kk) size_classes) by reflexivity.
assert (XQ3 : xb aTQ3 = SCT + 2 * t0_i3 kk) by reflexivity.
assert (TBL : 4096 <= DEB /\ DEB + 32 <= SCT /\ SCT + 96 <= 2 ^ 32 /\ SCT mod 2 = 0) by (unfold DEB, SCT, src0_D_debruijn32, src0_D_size_classes; repeat split; reflexivity || lia).
unfold st_ok. cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_resv ss_regs ss_mem ss_facts ss_T0b resv_denot].
repeat (split; [reflexivity|]). split; [|split].
- apply regs_ok0. intros k Hk. apply xb_reg. lia.
- split; [vm_compute; reflexivity|]. split.
+ unfold t0b_mem. apply Forall_cons; [apply (frame0_ok xb XR XSP)|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
(apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_tq1 R_tq2 R_tq3]; rewrite (base_val_EV xb XR); [lia | lia | intros; lia |]);
(apply Forall_cons; [|apply Forall_nil]).
* eapply (chunk_ok_val xb _ _ _ 1); [apply (U_off0 xb XR) | rewrite XE; change (2 ^ (8 * Z.of_N 1)) with 256; lia |].
rewrite XQ1, XE, Z.add_0_r. pose proof (deb_byte mem ST (dbj_idx (2 ^ e)) E3) as DB. rewrite Fdbj in DB. exact DB.
* eapply (chunk_ok_val xb _ _ _ 2); [apply (U_off0 xb XR) | rewrite XT1; change (2 ^ (8 * Z.of_N 2)) with 65536; lia |].
rewrite XQ2, XT1, Z.add_0_r. unfold t0_t1. fold e. apply (sct_bytes mem ST). lia.
* eapply (chunk_ok_val xb _ _ _ 2); [apply (U_off0 xb XR) | rewrite XT2; change (2 ^ (8 * Z.of_N 2)) with 65536; lia |].
rewrite XQ3, XT2, Z.add_0_r. apply (sct_bytes mem ST). lia.
+ cbn [pairwise_disjoint all_disjoint t0b_mem]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_frame0 R_tq1 R_tq2 R_tq3].
rewrite !(base_val_EV xb XR), XSP, XQ1, XQ2, XQ3. repeat split; try exact I; lia.
- split; [|split].
+ cbn [atoms_ok t0b_facts t0b_atoms f_atoms]. split; [apply (sp_fact xb XR XSP)|].
unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite !(ew_EV xb XR), xb_reg, X10, XK, XE, XP, XQ1, XT1, XQ2, XT2, XQ3 by lia.
change (2 ^ 0) with 1. change (2 ^ 1) with 2. rewrite !Z.mod_1_r. unfold MMAP_THRESHOLD in Hn. destruct TBL as (TB1 & TB2 & TB3 & TB4).
repeat split; try lia.
* rewrite Z.mul_comm, Z_mod_plus_full. exact TB4.
* rewrite Z.mul_comm, Z_mod_plus_full. exact TB4.
+ cbn [conds_ok t0b_facts f_conds]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b C_b1].
rewrite !(den_off0 xb XR), XK, XT1. unfold t0_b1 in *.
destruct (kk <? t0_t1 kk) eqn:Eb.
* rewrite bt_ltu by lia. exact Eb.
* rewrite bt_geu by lia. rewrite Eb. reflexivity.
+ cbn [alias_ok t0b_facts f_alias AL_k AL_p AL_q1 AL_q2 AL_q3].
split; [apply (alias_k xb XR); [rewrite xb_reg by lia; apply X10 | exact XK]|].
split; [rewrite D1, (den_off0 xb XR), XP; reflexivity|].
split; [rewrite D2, (den_off0 xb XR), XQ1; reflexivity|].
split; [rewrite D3, (den_off0 xb XR), XQ2; reflexivity|].
split; [rewrite D4, (den_off0 xb XR), XQ3; reflexivity| exact I].
Qed.
Lemma T0_post_gen xv (ss1 : sstate) (s4 : sv) (rest : smem) ms1 (mm : smem) :
(forall k, 0 <= xv k < 2 ^ 64) -> (forall k, (k <= 31)%nat -> xv k = bv_unsigned (getr regs (nat_to_reg k))) ->
cview T0_VIEW ss1 = (PA, None, R_frame1 :: rest, [SOff 2 (-48); SLit TP; SOff 10 0; SLit LOCK; SLit DEB; s4] ++ csaved_svs) ->
sv_denot (EV xv) s4 = Z_to_bv 64 (size_to_class n) ->
Forall (fun r => r_wlo r = 0 /\ r_whi r = 0) (tl mm) -> hd_error mm = Some R_frame0 ->
st_ok src0segs (EV xv) ss1 ms1 -> frame_of (EV xv) mm mem (ms_mem ms1) ->
ms1 = mkst (ms_regs ms1) (Z_to_bv 64 PA) (ms_mem ms1) rom /\ at_PA (ms_regs ms1) (ms_mem ms1).
Proof.
intros XR XV V Hs4 Hmm Hhd HS1 HF. destruct (cview_regs _ _ _ _ _ _ V) as (Hpc & Hrv & Hmem & _).
pose proof PRE_facts as (_ & _ & _ & _ & Hal & Hceil & Hsp63 & _). pose proof (proj1 alloc_ceiling_val) as HCV.
assert (XSP : xv 2%nat = SP0) by (rewrite XV by lia; reflexivity).
pose proof (reg_of _ _ _ 2 _ HS1 ltac:(lia) ltac:(reg_eq V 0%nat)) as G2.
pose proof (reg_of _ _ _ 4 _ HS1 ltac:(lia) ltac:(reg_eq V 1%nat)) as G4.
pose proof (reg_of _ _ _ 8 _ HS1 ltac:(lia) ltac:(reg_eq V 2%nat)) as G8.
pose proof (reg_of _ _ _ 9 _ HS1 ltac:(lia) ltac:(reg_eq V 3%nat)) as G9.
pose proof (reg_of _ _ _ 19 _ HS1 ltac:(lia) ltac:(reg_eq V 4%nat)) as G19.
pose proof (reg_of _ _ _ 20 _ HS1 ltac:(lia) ltac:(reg_eq V 5%nat)) as G20.
assert (GS : forall i, In i CSAVED -> getr (ms_regs ms1) (nat_to_reg i) = sv_denot (EV xv) (SOff i 0)).
{ intros i Hi. pose proof (csaved_cases i Hi) as C.
assert (E : nth i (ss_regs ss1) (SLit 0) = SOff i 0).
{ decompose [or] C; subst i; [reg_eq V 6%nat | reg_eq V 7%nat | reg_eq V 8%nat | reg_eq V 9%nat | reg_eq V 10%nat | reg_eq V 11%nat | reg_eq V 12%nat | reg_eq V 13%nat]. }
exact (reg_of _ _ _ i _ HS1 ltac:(decompose [or] C; subst i; lia) E). }
pose proof (st_ok_mem_ok src0segs _ _ _ HS1) as (_ & MOK & _). rewrite Hmem in MOK. apply Forall_inv in MOK.
destruct MOK as (_ & _ & WR & CH). cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_frame1] in WR, CH. rewrite (base_val_EV xv XR), XSP in WR, CH.
pose proof (Forall_inv CH) as C1. pose proof (Forall_inv (Forall_inv_tail CH)) as C2. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail CH))) as C3.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))) as C4.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH))))) as C5.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail CH)))))) as C6.
pose proof (st_ok_mkst src0segs _ _ _ HS1 Hrv) as SHAPE. rewrite Hpc in SHAPE. clear CH V Hpc Hrv Hmem.
split; [exact SHAPE|]. split.
- change (20%bv : bv 5) with (nat_to_reg 20). rewrite G20. exact Hs4.
- change (8%bv : bv 5) with (nat_to_reg 8). rewrite G8, (den_off0 xv XR), XV by lia. rewrite X10. reflexivity.
- change (9%bv : bv 5) with (nat_to_reg 9). rewrite G9. reflexivity.
- change (19%bv : bv 5) with (nat_to_reg 19). rewrite G19. reflexivity.
- change (2%bv : bv 5) with (nat_to_reg 2). rewrite G2, (den_off xv XR) by (rewrite XSP; lia). rewrite XSP. f_equal; lia.
- change (4%bv : bv 5) with (nat_to_reg 4). rewrite G4. reflexivity.
- intros i Hi. rewrite (GS i Hi), (den_off0 xv XR), XV by (pose proof (csaved_cases i Hi); lia). apply Z_to_bv_bv_unsigned.
- intros off r Hin. unfold FRAME_SLOTS in Hin. cbn [In] in Hin.
decompose [or] Hin; try contradiction;
match goal with H : (_, _) = (off, r) |- _ => injection H as <- <- end;
[ replace (SP0 - 48 + 0) with (SP0 + -48) by lia; apply (chunk_bytes_small xv _ _ _ 8 (SOff 20 0)); [exact C1 | rewrite (U_off0 xv XR), XV by lia; reflexivity | apply u64_range]
| replace (SP0 - 48 + 8) with (SP0 + -40) by lia; apply (chunk_bytes_small xv _ _ _ 8 (SOff 19 0)); [exact C2 | rewrite (U_off0 xv XR), XV by lia; reflexivity | apply u64_range]
| replace (SP0 - 48 + 16) with (SP0 + -32) by lia; apply (chunk_bytes_small xv _ _ _ 8 (SOff 18 0)); [exact C3 | rewrite (U_off0 xv XR), XV by lia; reflexivity | apply u64_range]
| replace (SP0 - 48 + 24) with (SP0 + -24) by lia; apply (chunk_bytes_small xv _ _ _ 8 (SOff 9 0)); [exact C4 | rewrite (U_off0 xv XR), XV by lia; reflexivity | apply u64_range]
| replace (SP0 - 48 + 32) with (SP0 + -16) by lia; apply (chunk_bytes_small xv _ _ _ 8 (SOff 8 0)); [exact C5 | rewrite (U_off0 xv XR), XV by lia; reflexivity | apply u64_range]
| replace (SP0 - 48 + 40) with (SP0 + -8) by lia; apply (chunk_bytes_small xv _ _ _ 8 (SOff 1 0)); [exact C6 | rewrite (U_off0 xv XR), XV by lia; reflexivity | apply u64_range] ].
- intros x Hx Hnx. apply (HF (Z_to_bv 64 x)). rewrite lit64_small by exact Hx.
intros (r & Hin & Hr). destruct mm as [|r0 mm']; [discriminate|]. cbn [hd_error] in Hhd. injection Hhd as ->. cbn [tl] in Hmm.
destruct Hin as [<- | Hin].
+ cbn [r_base r_wlo r_whi R_frame0] in Hr. rewrite (base_val_EV xv XR), XSP in Hr. lia.
+ pose proof (proj1 (Forall_forall _ _) Hmm r Hin) as [W1 W2]. rewrite W1, W2 in Hr. lia.
- intros a Ha. replace a with (SP0 + (a - SP0)) by lia. apply WR. lia.
Qed.
Theorem T0_SR :
SR src0segs (mkCfg (mkst regs (Z_to_bv 64 src0_A_malloc) mem rom) md)
(fun c' => exists regs1 mem1, c' = mkCfg (mkst regs1 (Z_to_bv 64 PA) mem1 rom) md /\ at_PA regs1 mem1).
Proof.
pose proof PRE_facts as (MX & _). destruct (mc_md _ _ _ _ _ (MRx_MRc _ _ _ _ _ MX)) as (Hh & Hlz & _).
destruct (Z_lt_le_dec n 157) as [SMALL | BIG].
- eapply SR_mono; [eapply (T0s_run (EV xs)); [exact (T0s_st_ok SMALL) | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). cbn [ms_mem mkst] in HF.
destruct (T0_post_gen xs SST0s (SOff aK 0) [] ms1 t0s_mem XRs ltac:(intros k Hk; apply xs_reg; lia) SST0s_view) as [SHAPE POST];
[| repeat constructor | reflexivity | exact HS1 | exact HF |].
+ rewrite (den_off0 xs XRs). change (xs aK) with kk. pose proof kk_facts as (_ & K2 & ->).
unfold class_of_units. replace (kk <? 10) with true by (symmetry; apply Z.ltb_lt; apply K2; exact SMALL). reflexivity.
+ exists (ms_regs ms1), (ms_mem ms1). split; [rewrite SHAPE at 1; reflexivity | exact POST].
- eapply SR_mono; [eapply (T0b_run (t0_b1 kk) (EV xb)); [exact (T0b_st_ok BIG) | exact Hh | exact Hlz]|].
intros c' (ms1 & -> & HS1 & HF). cbn [ms_mem mkst] in HF.
destruct (T0_post_gen xb (SST0b (t0_b1 kk)) (RESX (t0_b1 kk)) (tl t0b_mem) ms1 t0b_mem (XRb BIG) ltac:(intros k Hk; apply xb_reg; lia) (SST0b_view (t0_b1 kk))) as [SHAPE POST];
[| repeat constructor | reflexivity | exact HS1 | exact HF |].
+ pose proof (big_denots BIG) as (_ & _ & _ & _ & D5). rewrite D5. pose proof kk_facts as (_ & _ & ->). reflexivity.
+ exists (ms_regs ms1), (ms_mem ms1). split; [rewrite SHAPE at 1; reflexivity | exact POST].
Qed.
End T0.
End d.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
