(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_rgb_fuzzer/lib/UO13.v, with its module paths and module names changed; 323 of its 349 lines of code are new or changed and 165 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0a YO0c YO0g YO0d YN03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK15 YK0n YP0n YM06.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YH00 YH03 YH02 YN0b_cf YN07_cf YN1q_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable.Q Require Import YW0e_cf YV00_cf YV10_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YN1y_cf YN1d_cf YN1e_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM06_cf YO0d_cf.
Import ListNotations.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition aKr := 110%nat. Definition aEr := 111%nat. Definition aPr := 112%nat. Definition aQ1r := 113%nat.
Definition aT1r := 114%nat. Definition aQ2r := 115%nat. Definition aT2r := 116%nat. Definition aQ3r := 117%nat.
Definition aCLr := 118%nat.
Definition DEBr : Z := src0_D_debruijn32.
Definition SCTr : Z := src0_D_size_classes.
Definition R_q1r : region := mkRegion (Some aQ1r) 0 1 0 0 [mkChunk 0 (CVal 1 (SOff aEr 0))].
Definition R_q2r : region := mkRegion (Some aQ2r) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aT1r 0))].
Definition R_q3r : region := mkRegion (Some aQ3r) 0 2 0 0 [mkChunk 0 (CVal 2 (SOff aT2r 0))].
Definition smr : sv := SOff aKr 1.
Definition sm1r : sv := SAlu ALU_OR (SAlu ALU_OR (SAluw ALU_SRL smr (SLit 2)) smr) (SAluw ALU_SRL smr (SLit 1)).
Definition sm2r : sv := SAlu ALU_OR (SAluw ALU_SRL sm1r (SLit 2)) (SAluw ALU_SRL smr (SLit 1)).
Definition sm3r : sv := SAlu ALU_OR (SAlu ALU_SRL sm2r (SLit 4)) sm2r.
Definition sm4r : sv := SAlu ALU_OR (SAlu ALU_SRL sm3r (SLit 8)) sm3r.
Definition ANDXr : sv := SAlu ALU_AND (SAlu ALU_ADD sm4r (SLit 1)) (SAlu ALU_XOR sm4r (SLit (-1))).
Definition TQ1r : sv := SAlu ALU_ADD (SLit DEBr) (SAluw ALU_SRL (SMd M_MUL (SOff aPr 0) (SLit 125613361)) (SLit 27)).
Definition C4r : sv := SAlu ALU_XOR (SAlu ALU_SLL (SOff aEr 0) (SLit 2)) (SLit 124).
Definition I2Cr (b1 : bool) : Z := if b1 then 120 else 122.
Definition TQ2r : sv := SAlu ALU_ADD (SLit SCTr) (SAlu ALU_SLL (SAlu ALU_SUB (SLit 121) C4r) (SLit 1)).
Definition TQ3r (b1 : bool) : sv := SAlu ALU_ADD (SLit SCTr) (SAlu ALU_SLL (SAlu ALU_SUB (SLit (I2Cr b1)) C4r) (SLit 1)).
Definition C_b1r (b1 : bool) : acond := mkAC (if b1 then BC_LTU else BC_GEU) (SOff aKr 0) (SOff aT1r 0).
Definition RESr (b1 : bool) : sv :=
SAlu ALU_OR (SAlu ALU_SUB (SLit (I2Cr b1)) C4r) (SAlu ALU_XOR (SAlu ALU_SLTU (SOff aKr 0) (SOff aT2r 0)) (SLit 1)).
Definition atomsr : list (nat * afact) :=
[(aKr, mkAF 10 8190 0); (aEr, mkAF 3 12 0); (aPr, mkAF 8 4096 0); (aQ1r, mkAF DEBr (DEBr + 31) 0); (aT1r, mkAF 0 8191 0);
(aQ2r, mkAF SCTr (SCTr + 94) 1); (aT2r, mkAF 0 8191 0); (aQ3r, mkAF SCTr (SCTr + 94) 1); (aCLr, mkAF 0 47 0)].
Definition aliasr (b1 : bool) : list (sv * sv) :=
[(ANDXr, SOff aPr 0); (TQ1r, SOff aQ1r 0); (TQ2r, SOff aQ2r 0); (TQ3r b1, SOff aQ3r 0); (RESr b1, SOff aCLr 0)].
Definition envr (k : Z) : list (nat * Z) :=
[(aKr, k); (aEr, t0_e k); (aPr, 2 ^ t0_e k); (aQ1r, DEBr + dbj_idx (2 ^ t0_e k)); (aT1r, t0_t1 k);
(aQ2r, SCTr + 2 * (4 * t0_e k - 3)); (aT2r, znth (t0_i3 k) size_classes); (aQ3r, SCTr + 2 * t0_i3 k);
(aCLr, class_of_units k)].
Definition atom_chk (l : list (nat * Z)) (p : nat * afact) : bool :=
let v := YN1y_cf.xv_of l (fst p) in
YN1y_cf.uses_of l (fst p) && (0 <=? v) && (v <? 2 ^ 64) && (af_lo (snd p) <=? v) && (v <=? af_hi (snd p)) &&
(0 <=? af_al2 (snd p)) && (af_al2 (snd p) <=? 64) && (v mod 2 ^ af_al2 (snd p) =? 0).
Definition alias_chk (l : list (nat * Z)) (p : sv * sv) : bool :=
YN1y_cf.sv_uses (YN1y_cf.uses_of l) (fst p) && YN1y_cf.sv_uses (YN1y_cf.uses_of l) (snd p) &&
(YN1y_cf.UZ (YN1y_cf.xv_of l) (fst p) =? YN1y_cf.UZ (YN1y_cf.xv_of l) (snd p)).
Definition cond_chk (l : list (nat * Z)) (c : acond) : bool :=
YN1y_cf.sv_uses (YN1y_cf.uses_of l) (ac_a c) && YN1y_cf.sv_uses (YN1y_cf.uses_of l) (ac_b c) &&
branch_taken (ac_c c) (Z_to_bv 64 (YN1y_cf.UZ (YN1y_cf.xv_of l) (ac_a c))) (Z_to_bv 64 (YN1y_cf.UZ (YN1y_cf.xv_of l) (ac_b c))).
Definition tab_chk (k : Z) : bool :=
(znth (dbj_idx (2 ^ t0_e k)) DEBRUIJN =? t0_e k) && (0 <=? 4 * t0_e k - 3) && (4 * t0_e k - 3 <? 48) &&
(0 <=? t0_i3 k) && (t0_i3 k <? 48) && negb (t0_i3 k =? 4 * t0_e k - 3).
Definition rchk (k : Z) : bool :=
forallb (atom_chk (envr k)) atomsr && forallb (alias_chk (envr k)) (aliasr (t0_b1 k)) &&
cond_chk (envr k) (C_b1r (t0_b1 k)) && tab_chk k.
Lemma rchk_all : forallb rchk (zseq 10 8181) = true.
Proof using. vm_compute. reflexivity. Qed.
Lemma k_UZ n : 0 <= n < 2 ^ 62 -> YN1y_cf.UZ (fun _ => n) (SAlu ALU_SRL (SOff aN 3) (SLit 4)) = (n + 3) / 16.
Proof using.
intros Hn. cbn [YN1y_cf.UZ]. unfold zalu64. cbn [zalu_raw].
rewrite !(zcanon_id n) by (unfold M64; lia). rewrite !(zcanon_id (n + 3)) by (unfold M64; lia).
rewrite !(zcanon_id 4) by (unfold M64; lia). change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 4) with 16. apply zcanon_id. unfold M64. split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia.
Qed.
Lemma rchk_sound k : rchk k = true ->
forallb (atom_chk (envr k)) atomsr = true /\ forallb (alias_chk (envr k)) (aliasr (t0_b1 k)) = true /\
cond_chk (envr k) (C_b1r (t0_b1 k)) = true /\ znth (dbj_idx (2 ^ t0_e k)) DEBRUIJN = t0_e k /\
0 <= 4 * t0_e k - 3 < 48 /\ 0 <= t0_i3 k < 48 /\ t0_i3 k <> 4 * t0_e k - 3.
Proof using.
unfold rchk, tab_chk. intros C.
apply andb_prop in C as [C T]. apply andb_prop in C as [C CC]. apply andb_prop in C as [CA CL].
apply andb_prop in T as [T T6]. apply andb_prop in T as [T T5]. apply andb_prop in T as [T T4].
apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
apply Z.eqb_eq in T1. apply Z.leb_le in T2. apply Z.ltb_lt in T3. apply Z.leb_le in T4. apply Z.ltb_lt in T5.
apply negb_true_iff in T6. apply Z.eqb_neq in T6.
split; [exact CA|]. split; [exact CL|]. split; [exact CC|]. split; [exact T1|].
split; [lia|]. split; [lia|]. exact T6.
Qed.
Definition env_of (E2 : env) (l : list (nat * Z)) : Prop :=
forall n, YN1y_cf.uses_of l n = true -> ew E2 n = Z_to_bv 64 (YN1y_cf.xv_of l n).
Lemma den_chk E2 l v : env_of E2 l -> YN1y_cf.sv_uses (YN1y_cf.uses_of l) v = true ->
sv_denot E2 v = Z_to_bv 64 (YN1y_cf.UZ (YN1y_cf.xv_of l) v).
Proof using.
intros H Hv. rewrite (YN1y_cf.sv_denot_agree (YN1y_cf.uses_of l) E2 (EV (YN1y_cf.xv_of l)) v Hv H). apply YN1y_cf.UZ_sound.
Qed.
Lemma chk_val E2 l al n f : env_of E2 l -> forallb (atom_chk l) al = true -> In (n, f) al ->
bv_unsigned (ew E2 n) = YN1y_cf.xv_of l n /\ af_lo f <= YN1y_cf.xv_of l n <= af_hi f.
Proof using.
intros H C Hin. pose proof (proj1 (forallb_forall _ _) C _ Hin) as C1. unfold atom_chk in C1. cbn [fst snd] in C1.
apply andb_prop in C1 as [C1 _]. apply andb_prop in C1 as [C1 _]. apply andb_prop in C1 as [C1 _].
apply andb_prop in C1 as [C1 Hhi]. apply andb_prop in C1 as [C1 Hlo]. apply andb_prop in C1 as [C1 Hv2].
apply andb_prop in C1 as [Hu Hv1].
apply Z.leb_le in Hhi. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hv2. apply Z.leb_le in Hv1.
rewrite (H n Hu), lit64_small by lia. split; [reflexivity | lia].
Qed.
Lemma atoms_chk_ok E2 l al : env_of E2 l -> forallb (atom_chk l) al = true -> atoms_ok E2 al.
Proof using.
intros H. induction al as [|[n f] al IH]; cbn [atoms_ok forallb]; intros C; [exact I|].
apply andb_prop in C as [C1 C2]. split; [|exact (IH C2)].
unfold atom_chk in C1. cbn [fst snd] in C1.
apply andb_prop in C1 as [C1 Hm]. apply andb_prop in C1 as [C1 Ha2]. apply andb_prop in C1 as [C1 Ha1].
apply andb_prop in C1 as [C1 Hhi]. apply andb_prop in C1 as [C1 Hlo]. apply andb_prop in C1 as [C1 Hv2].
apply andb_prop in C1 as [Hu Hv1].
apply Z.eqb_eq in Hm. apply Z.leb_le in Ha2. apply Z.leb_le in Ha1. apply Z.leb_le in Hhi. apply Z.leb_le in Hlo.
apply Z.ltb_lt in Hv2. apply Z.leb_le in Hv1.
unfold afact_ok. rewrite (H n Hu), lit64_small by (clear Hm; lia).
split; [clear Hm; lia|]. split; [exact Hm | clear Hm; lia].
Qed.
Lemma alias_chk_ok E2 l als : env_of E2 l -> forallb (alias_chk l) als = true -> alias_ok E2 als.
Proof using.
intros H. induction als as [|[a b] als IH]; cbn [alias_ok forallb]; intros C; [exact I|].
apply andb_prop in C as [C1 C2]. split; [|exact (IH C2)]. unfold alias_chk in C1. cbn [fst snd] in C1.
apply andb_prop in C1 as [C1 C3]. apply andb_prop in C1 as [Ca Cb]. apply Z.eqb_eq in C3.
rewrite (den_chk E2 l a H Ca), (den_chk E2 l b H Cb), C3. reflexivity.
Qed.
Lemma cond_chk_ok E2 l c : env_of E2 l -> cond_chk l c = true -> acond_ok E2 c.
Proof using.
intros H C. unfold cond_chk in C. apply andb_prop in C as [C C3]. apply andb_prop in C as [Ca Cb].
unfold acond_ok. rewrite (den_chk E2 l _ H Ca), (den_chk E2 l _ H Cb). exact C3.
Qed.
Definition kkE (E : env) : Z := (bv_unsigned (ew E aN) + 3) / 16.
Definition Ex (E : env) : env :=
mkEnv (fun i => if (i <? 110)%nat then ew E i else Z_to_bv 64 (YN1y_cf.xv_of (envr (kkE E)) i)) (ed E).
Lemma uses_envr k n : YN1y_cf.uses_of (envr k) n = true -> (110 <= n)%nat.
Proof using.
unfold YN1y_cf.uses_of, envr. cbn [existsb fst]. intros H.
repeat (apply orb_prop in H as [H|H]; [apply Nat.eqb_eq in H; rewrite <- H; cbv [aKr aEr aPr aQ1r aT1r aQ2r aT2r aQ3r aCLr]; lia|]).
discriminate.
Qed.
Lemma Ex_agree E : env_agree 110 E (Ex E).
Proof using.
split; [|reflexivity]. intros n Hn. cbn [ew Ex]. replace (n <? 110)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hn).
reflexivity.
Qed.
Lemma Ex_env E : env_of (Ex E) (envr (kkE E)).
Proof using.
intros n Hn. pose proof (uses_envr _ n Hn) as H1. cbn [ew Ex].
replace (n <? 110)%nat with false by (symmetry; apply Nat.ltb_ge; exact H1). reflexivity.
Qed.
Definition PK : Z := src0_A_realloc + 0x208.
Definition S0b (r : rcase) : sstate := S0n 157 131051 [mkAC BC_GEU (SOff aEP 0) (SOff aN 0)] r.
Definition S3a (r : rcase) : sstate := fst (sym_run_toN src0segs src0tbl FUEL PK (S0b r)).
Lemma S3a_run_ok r : run_to_ok PK (S0b r) (S3a r).
Proof using. split; destruct r; vm_compute; reflexivity. Qed.
Lemma S3a_shape r : ss_resv (S3a r) = None /\ sr_get (ss_regs (S3a r)) 12%bv = SAlu ALU_SRL (SOff aN 3) (SLit 4) /\
ss_mem (S3a r) = mem_fin r /\ regs_atoms_lt 110 (ss_regs (S3a r)) = true /\ facts_atoms_lt 110 (ss_facts (S3a r)) = true.
Proof using. destruct r; vm_compute; repeat split; reflexivity. Qed.
Definition S3b (r : rcase) (b1 : bool) : sstate :=
mkSS PK (sr_set (ss_regs (S3a r)) 12%bv (SOff aKr 0)) [R_q1r; R_q2r; R_q3r] None
(facts_app (ss_facts (S3a r)) atomsr [C_b1r b1] (aliasr b1)).
Definition S4b (r : rcase) (b1 : bool) : sstate :=
fst (sym_run_toN src0segs src0tbl FUEL src0_A_libc_malloc_impl (S3b r b1)).
Lemma S4b_run_ok r b1 : run_to_ok src0_A_libc_malloc_impl (S3b r b1) (S4b r b1).
Proof using. split; destruct r, b1; vm_compute; reflexivity. Qed.
Lemma S4b_shape r b1 : ss_resv (S4b r b1) = None /\ regs_view (ss_regs (S4b r b1)) = arr_view r.
Proof using. destruct r, b1; vm_compute; repeat split; reflexivity. Qed.
Lemma wr_entry_r : forall E r x, in_wrange E (entry_mem r) x ->
(base_val E (Some aSP) - 8256 <= x < base_val E (Some aSP)) \/ (base_val E (Some aTP) - 164 <= x < base_val E (Some aTP) - 160).
Proof using.
intros E r x (rg & Hin & Hx). unfold entry_mem in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
cbn [r_base r_wlo r_whi reg_hdr0 reg_grp reg_meta0 reg_area reg_ctx reg_nl reg_stkR reg_got reg_guard reg_errnoR] in Hx; lia.
- assert (H0 : r_wlo rg = 0 /\ r_whi rg = 0).
{ destruct r; cbn [r_mem] in Hin;
repeat (destruct Hin as [<-|Hin]; [split; reflexivity|]); destruct Hin. }
lia.
Qed.
Ltac tl := unfold DEBr, SCTr, src0_D_debruijn32, src0_D_size_classes in *; lia.
Section b.
Variables (E : env) (r : rcase) (ms ms1 : machine_state).
Hypothesis HS : st_ok src0segs E (S0b r) ms.
Hypothesis ST : statics_ok src0_msyms (ms_mem ms).
Hypothesis HS1 : st_ok src0segs E (S3a r) ms1.
Hypothesis HF1 : frame_of E (entry_mem r) (ms_mem ms) (ms_mem ms1).
Lemma entry_atoms_E : 157 <= bv_unsigned (ew E aN) <= 131051 /\ CEIL_MIN + 8256 <= bv_unsigned (ew E aSP).
Proof using HS.
pose proof (st_ok_facts_ok src0segs E _ _ HS) as (HA & _).
cbn [S0b S0n ss_facts entry_facts_n f_atoms entry_atoms_n atoms_ok] in HA.
destruct HA as (HN & _ & _ & _ & _ & _ & HSP & _). destruct HN as [HN _]. destruct HSP as [HSP _].
cbn [af_lo af_hi] in HN, HSP. lia.
Qed.
Lemma kk_range : 10 <= kkE E < 10 + 8181.
Proof using HS.
pose proof entry_atoms_E as [HN _]. unfold kkE. split.
- apply Z.div_le_lower_bound; lia.
- apply Z.div_lt_upper_bound; lia.
Qed.
Lemma rchk_E : rchk (kkE E) = true.
Proof using HS. exact (proj1 (forallb_zseq_iff rchk 10 8181) rchk_all _ kk_range). Qed.
Lemma vals :
bv_unsigned (ew (Ex E) aEr) = t0_e (kkE E) /\ 3 <= t0_e (kkE E) <= 12 /\
bv_unsigned (ew (Ex E) aQ1r) = DEBr + dbj_idx (2 ^ t0_e (kkE E)) /\
bv_unsigned (ew (Ex E) aT1r) = t0_t1 (kkE E) /\ 0 <= t0_t1 (kkE E) <= 8191 /\
bv_unsigned (ew (Ex E) aQ2r) = SCTr + 2 * (4 * t0_e (kkE E) - 3) /\
bv_unsigned (ew (Ex E) aT2r) = znth (t0_i3 (kkE E)) size_classes /\ 0 <= znth (t0_i3 (kkE E)) size_classes <= 8191 /\
bv_unsigned (ew (Ex E) aQ3r) = SCTr + 2 * t0_i3 (kkE E) /\
bv_unsigned (ew (Ex E) aKr) = kkE E.
Proof using HS.
destruct (rchk_sound _ rchk_E) as (CA & _).
pose proof (fun n f H => chk_val _ _ _ n f (Ex_env E) CA H) as CV.
destruct (CV aKr _ ltac:(unfold atomsr; cbn [In]; left; reflexivity)) as [V0 _].
destruct (CV aEr _ ltac:(unfold atomsr; cbn [In]; do 1 right; left; reflexivity)) as [V1 R1].
destruct (CV aQ1r _ ltac:(unfold atomsr; cbn [In]; do 3 right; left; reflexivity)) as [V3 _].
destruct (CV aT1r _ ltac:(unfold atomsr; cbn [In]; do 4 right; left; reflexivity)) as [V4 R4].
destruct (CV aQ2r _ ltac:(unfold atomsr; cbn [In]; do 5 right; left; reflexivity)) as [V5 _].
destruct (CV aT2r _ ltac:(unfold atomsr; cbn [In]; do 6 right; left; reflexivity)) as [V6 R6].
destruct (CV aQ3r _ ltac:(unfold atomsr; cbn [In]; do 7 right; left; reflexivity)) as [V7 _].
split; [exact V1|]. split; [exact R1|]. split; [exact V3|]. split; [exact V4|]. split; [exact R4|].
split; [exact V5|]. split; [exact V6|]. split; [exact R6|]. split; [exact V7|]. exact V0.
Qed.
Lemma reg12_val : sv_denot E (SAlu ALU_SRL (SOff aN 3) (SLit 4)) = sv_denot (Ex E) (SOff aKr 0).
Proof using HS.
pose proof entry_atoms_E as [HN _].
destruct vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VK).
assert (A : sv_denot E (SAlu ALU_SRL (SOff aN 3) (SLit 4)) =
sv_denot (EV (fun _ => bv_unsigned (ew E aN))) (SAlu ALU_SRL (SOff aN 3) (SLit 4))).
{ apply (YN1y_cf.sv_denot_agree (fun i => Nat.eqb i 11)); [reflexivity|]. intros i Hi. apply Nat.eqb_eq in Hi. subst i.
cbn [ew EV]. symmetry. apply Z_to_bv_bv_unsigned. }
rewrite A, YN1y_cf.UZ_sound.
rewrite (k_UZ (bv_unsigned (ew E aN))) by lia.
cbn [sv_denot]. rewrite VK, Z.add_0_r. reflexivity.
Qed.
Lemma regs3 b1 : regs_ok (Ex E) (ss_regs (S3b r b1)) (ms_regs ms1).
Proof using HS HS1.
destruct (S3a_shape r) as (_ & H12 & _ & Hrl & _).
intros q. cbn [S3b ss_regs].
destruct (bv_eqb q 12%bv) eqn:Hq.
- unfold bv_eqb in Hq. apply Z.eqb_eq in Hq. apply bv_eq in Hq. subst q.
rewrite sr_get_set_same by reflexivity. rewrite (st_ok_reg src0segs E _ _ 12%bv HS1), H12. exact reg12_val.
- rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in Hq; discriminate).
rewrite (st_ok_reg src0segs E _ _ q HS1). symmetry.
exact (YP06.sv_denot_agree 110 E (Ex E) _ (Ex_agree E) (sr_get_atoms 110 _ q Hrl)).
Qed.
Lemma tbl_same a : src0_D_debruijn32 <= a < src0_D_size_classes + 96 ->
mbyte src0segs (ms_mem ms1) a = mbyte src0segs (ms_mem ms) a.
Proof using HF1 HS HS1.
intros Ha. pose proof entry_atoms_E as [_ HSP].
pose proof (st_ok_mem_ok src0segs E _ _ HS) as (_ & R0 & _).
pose proof (st_ok_mem_ok src0segs E _ _ HS1) as (_ & R1 & _).
destruct (S3a_shape r) as (_ & _ & Hm1 & _). rewrite Hm1 in R1.
assert (E0 : In reg_errnoR (ss_mem (S0b r))).
{ cbn [S0b S0n ss_mem entry_mem]. apply in_or_app. left. cbn [In]. do 9 right. left. reflexivity. }
pose proof (proj1 (Forall_forall _ _) R0 _ E0) as (_ & _ & _ & C0).
pose proof (proj1 (Forall_forall _ _) R1 _ (errno_in r)) as (_ & _ & _ & C1).
cbn [r_chunks r_base reg_errnoR] in C0, C1. apply Forall_inv in C0. apply Forall_inv in C1.
assert (ER : (base_val E (Some aTP) - 164 <= a < base_val E (Some aTP) - 160) \/
~ (base_val E (Some aTP) - 164 <= a < base_val E (Some aTP) - 160)) by lia.
destruct ER as [ER|ER].
- destruct (C0 (a - (base_val E (Some aTP) - 164)) ltac:(cbn [c_len c_val cv_len Z.of_N]; lia)) as (b0 & B0 & M0).
destruct (C1 (a - (base_val E (Some aTP) - 164)) ltac:(cbn [c_len c_val cv_len Z.of_N]; lia)) as (b1 & B1 & M1).
cbn [c_off] in M0, M1. rewrite B0 in B1. injection B1 as <-.
replace (base_val E (Some aTP) + -164 + (a - (base_val E (Some aTP) - 164))) with a in M0, M1 by lia.
rewrite M0, M1. reflexivity.
- apply YN1d_cf.mbyte_ext1. apply HF1. rewrite lit64_small by tl.
intros W. apply wr_entry_r in W. destruct W as [W|W]; [cbn [base_val] in W; tl | exact (ER W)].
Qed.
Lemma tbl_bytes a w v : src0_D_debruijn32 <= a -> a + Z.of_nat w <= src0_D_size_classes + 96 ->
YN07_cf.bytes_are (ms_mem ms) a w v -> YN07_cf.bytes_are (ms_mem ms1) a w v.
Proof using HF1 HS HS1. intros H1 H2 Hb k Hk. rewrite tbl_same by lia. exact (Hb k Hk). Qed.
Lemma mem_ok3 : mem_ok src0segs (Ex E) (ms_mem ms1) [R_q1r; R_q2r; R_q3r].
Proof using HF1 HS HS1 ST.
destruct vals as (VE & RE & VQ1 & VT1 & RT1 & VQ2 & VT2 & RT2 & VQ3 & _).
destruct (rchk_sound _ rchk_E) as (_ & _ & _ & TD & T43 & TI3 & TNE).
pose proof (dbj_idx_range (2 ^ t0_e (kkE E))) as DR.
split; [vm_compute; reflexivity|]. split.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_q1r base_val]; rewrite ?VQ1.
* tl.
* tl.
* intros; lia.
* apply Forall_cons; [|apply Forall_nil]. apply (YN1e_cf.chunk_ok_val' _ _ _ _ 1 (SOff aEr 0) (t0_e (kkE E))).
-- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact VE.
-- change (2 ^ (8 * Z.of_N 1)) with 256. lia.
-- rewrite Z.add_0_r. change (N.to_nat 1) with 1%nat. apply tbl_bytes; [tl | cbn [Z.of_nat]; tl |].
pose proof (YN1y_cf.deb_byte _ ST _ DR) as DB. rewrite TD in DB. exact DB.
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_q2r base_val]; rewrite ?VQ2.
* tl.
* tl.
* intros; lia.
* apply Forall_cons; [|apply Forall_nil]. apply (YN1e_cf.chunk_ok_val' _ _ _ _ 2 (SOff aT1r 0) (t0_t1 (kkE E))).
-- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact VT1.
-- change (2 ^ (8 * Z.of_N 2)) with 65536. lia.
-- rewrite Z.add_0_r. change (N.to_nat 2) with 2%nat. apply tbl_bytes; [tl | cbn [Z.of_nat]; tl |].
unfold t0_t1. exact (YN1y_cf.sct_bytes _ ST _ T43).
+ apply region_ok_intro; cbn [r_base r_lo r_hi r_wlo r_whi r_chunks R_q3r base_val]; rewrite ?VQ3.
* tl.
* tl.
* intros; lia.
* apply Forall_cons; [|apply Forall_nil].
apply (YN1e_cf.chunk_ok_val' _ _ _ _ 2 (SOff aT2r 0) (znth (t0_i3 (kkE E)) size_classes)).
-- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact VT2.
-- change (2 ^ (8 * Z.of_N 2)) with 65536. lia.
-- rewrite Z.add_0_r. change (N.to_nat 2) with 2%nat. apply tbl_bytes; [tl | cbn [Z.of_nat]; tl |].
exact (YN1y_cf.sct_bytes _ ST _ TI3).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint. cbn [r_base r_lo r_hi R_q1r R_q2r R_q3r base_val].
rewrite VQ1, VQ2, VQ3. repeat split; try exact I; tl.
Qed.
Lemma facts3 : facts_ok (Ex E) (ss_facts (S3b r (t0_b1 (kkE E)))).
Proof using HS HS1.
destruct (S3a_shape r) as (_ & _ & _ & _ & Hfl).
pose proof (facts_ok_agree 110 E (Ex E) _ (Ex_agree E) Hfl (st_ok_facts_ok src0segs E _ _ HS1)) as (A & C & Al).
destruct (rchk_sound _ rchk_E) as (CA & CL & CC & _).
cbn [S3b ss_facts facts_app f_atoms f_conds f_alias].
split; [apply atoms_ok_app; [exact (atoms_chk_ok _ _ _ (Ex_env E) CA) | exact A]|].
split; [apply conds_ok_app; [exact (conj (cond_chk_ok _ _ _ (Ex_env E) CC) I) | exact C]|].
apply alias_ok_app; [exact (alias_chk_ok _ _ _ (Ex_env E) CL) | exact Al].
Qed.
Lemma st_ok3 : st_ok src0segs (Ex E) (S3b r (t0_b1 (kkE E))) ms1.
Proof using HF1 HS HS1 ST.
destruct (S3a_shape r) as (Hrv & _).
pose proof HS1 as (F1 & F2 & F3 & F4 & F5 & F6 & _).
unfold st_ok. split; [exact F1|]. split; [rewrite F2, (proj2 (S3a_run_ok r)); reflexivity|].
split; [exact F3|]. split; [rewrite F4, Hrv; reflexivity|]. split; [exact F5|]. split; [exact F6|].
split; [exact (regs3 _)|]. split; [exact mem_ok3 | exact facts3].
Qed.
End b.
Theorem k3b_small_big (E : env) (r : rcase) ms md :
st_ok src0segs E (S0n 157 131051 [mkAC BC_GEU (SOff aEP 0) (SOff aN 0)] r) ms ->
statics_ok src0_msyms (ms_mem ms) ->
m_halted md = None -> m_vm_lazy md = [] ->
SR_cfv src0segs (mkCfg ms md) (arrives E r (ms_mem ms) md).
Proof using.
intros HS ST Hh Hlz.
eapply SR_cfv_bind; [exact (SR_run_to' PK E _ _ ms md HS (S3a_run_ok r) Hh Hlz)|].
intros c (ms1 & -> & HS1 & HF1). change (ss_mem (S0b r)) with (entry_mem r) in HF1.
pose proof (st_ok3 E r ms ms1 HS ST HS1 HF1) as HSb.
eapply SR_cfv_mono; [exact (SR_run_to' _ (Ex E) _ _ ms1 md HSb (S4b_run_ok r _) Hh Hlz)|].
intros c (ms4 & -> & HS4 & HF4).
destruct (S4b_shape r (t0_b1 (kkE E))) as (Hrv & V).
destruct (S3a_shape r) as (_ & _ & Hm1 & _).
pose proof (st_ok_mem_ok src0segs E _ _ HS1) as (_ & ROK & _). rewrite Hm1 in ROK.
exists (ms_regs ms4), (ms_mem ms4). split.
- rewrite (st_ok_mkst src0segs (Ex E) _ _ HS4 Hrv) at 1. rewrite (proj2 (S4b_run_ok r _)). reflexivity.
- apply (arr_intro E (Ex E) r (ms_mem ms) (ms_mem ms1) (ms_mem ms4) (ss_regs (S4b r (t0_b1 (kkE E)))) (ms_regs ms4)
(Ex_agree E) (st_ok_regs_ok src0segs (Ex E) _ _ HS4) V).
+ intros x. apply HF4. intros (rg & Hin & Hx). cbn [S3b ss_mem In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [r_wlo r_whi R_q1r R_q2r R_q3r] in Hx; lia.
+ exact (proj1 (Forall_forall _ _) ROK _ (stk1_in r)).
+ exact (proj1 (Forall_forall _ _) ROK _ (errno_in r)).
+ exact HF1.
Qed.
End a.
