(* nl_error on image A: the lemmas every phase of the walk (lib/A/Prog/nl_error_*.v) uses on the data of
   nl_error_defs.v. Section 1: the atoms of a seated state. Section 2: what the contract's premises give
   (ne_base_facts). Section 3: THE SEAT (ne_seat): a join's concrete invariant (ne_j) gives the symbolic state
   ne_ss with its shadow entries ne_SH, so a phase can run the engine from it.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j YI0s YI01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal PaJournalFs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide PcapRelro nl_error_c nl_error_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   0. Image-free helpers
   ========================================================================== *)

(* A register file in which every assignment of upd already holds. *)
Lemma regs_ok_sets_keep : forall E sr regs upd,
  regs_ok E sr regs ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\ getr regs (fst eu) = sv_denot E (snd eu)) upd ->
  regs_ok E (sr_sets sr upd) regs.
Proof.
  intros E sr regs upd. revert sr. induction upd as [|[r e] upd IH]; intros sr Hsr HF; cbn [sr_sets]; [exact Hsr|].
  inversion HF as [|? ? [H0 He] HF']; subst. cbn [fst snd] in H0, He. apply IH; [|exact HF'].
  intros r'. destruct (Z.eq_dec (bv_unsigned r') (bv_unsigned r)) as [Heq|Hne].
  - assert (r' = r) as -> by (apply bv_eq; exact Heq).
    rewrite sr_get_set_same by exact H0. exact He.
  - rewrite sr_get_set_other by (intros ->; apply Hne; reflexivity). apply Hsr.
Qed.

Lemma w64_bv_unsigned : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.

(* the shadow cell of a constant offset of an atom *)
Lemma denot_shadow_cell_off : forall E n m v c base,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> ew E m = Z_to_bv 64 base -> 0 <= base ->
  base + (v + c) / 8 < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (base + (v + c) / 8).
Proof.
  intros E n m v c base Hn Hv Hvc Hm Hb Hs. rewrite denot_lit_U. f_equal.
  assert (Hd : 0 <= (v + c) / 8) by (apply Z.div_pos; lia).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (U_atom_off E n v c Hn ltac:(lia) ltac:(lia)), (U_atom_off E m base 0 Hm ltac:(lia) ltac:(lia)).
  rewrite !Z.add_0_r. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_id ((v + c) / 8)) by (rewrite M64_val; assert ((v + c) / 8 <= v + c) by (apply Z.div_le_upper_bound; lia); lia).
  rewrite zcanon_id by (rewrite M64_val; lia). lia.
Qed.

Lemma sv_offc : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros E n v c H Hv. cbn [sv_denot]. rewrite H. rewrite unsigned_lit_small by exact Hv. reflexivity.
Qed.

(* the room tests a phase decides, as engine conditions on an atom k (= n) plus an offset d *)
Lemma ne_acond_ltu : forall E (k : nat) v c d, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  c < (v + d) mod 2 ^ 64 -> acond_ok E (mkAC BC_LTU (SLit c) (SOff k d)).
Proof.
  intros E k v c d Hk Hv Hc H. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, U_lit, U_SOff by exact Hc. rewrite Hk, unsigned_lit_small by exact Hv.
  rewrite zcanon_wrap. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.ltb_lt. exact H.
Qed.
Lemma ne_acond_geu : forall E (k : nat) v c d, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  (v + d) mod 2 ^ 64 <= c -> acond_ok E (mkAC BC_GEU (SLit c) (SOff k d)).
Proof.
  intros E k v c d Hk Hv Hc H. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, U_lit, U_SOff by exact Hc. rewrite Hk, unsigned_lit_small by exact Hv.
  rewrite zcanon_wrap. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply negb_true_iff. apply Z.ltb_ge. exact H.
Qed.

(* signed tests against 0 (`bgez`) *)
Lemma ne_acond_ge0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 ->
  acond_ok E (mkAC BC_GE (SOff k 0) (SLit 0)).
Proof.
  intros E k v Hk Hv. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
  change (bv_lts (sv_denot E (SOff k 0)) (sv_denot E (SLit 0))) with (Sg E (SOff k 0) <? Sg E (SLit 0)).
  rewrite S_SOff, S_SLit, Hk, unsigned_lit_small by lia. rewrite Z.add_0_r, bv_swrap_0.
  rewrite bv_swrap_small by (change (bv_half_modulus 64) with (2 ^ 63); lia).
  apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma ne_acond_lt0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 2 ^ 63 <= v < 2 ^ 64 ->
  acond_ok E (mkAC BC_LT (SOff k 0) (SLit 0)).
Proof.
  intros E k v Hk Hv. unfold acond_ok. cbn [ac_c ac_a ac_b branch_taken].
  change (bv_lts (sv_denot E (SOff k 0)) (sv_denot E (SLit 0))) with (Sg E (SOff k 0) <? Sg E (SLit 0)).
  rewrite S_SOff, S_SLit, Hk, unsigned_lit_small by lia. rewrite Z.add_0_r, bv_swrap_0.
  rewrite bv_swrap_hi by (first [discriminate | change (bv_half_modulus 64) with (2 ^ 63); lia
                               | change (bv_modulus 64) with (2 ^ 64); lia]).
  change (bv_modulus 64) with (2 ^ 64). apply Z.ltb_lt. lia.
Qed.
(* tests on a sum of two atoms (the cut put's room) and on an atom against 0 (`beqz`) *)
Lemma ne_U_add2 : forall E (k1 k2 : nat) v1 v2, ew E k1 = Z_to_bv 64 v1 -> ew E k2 = Z_to_bv 64 v2 ->
  0 <= v1 -> 0 <= v2 -> v1 + v2 < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff k1 0) (SOff k2 0)) = v1 + v2.
Proof.
  intros E k1 k2 v1 v2 H1 H2 Hv1 Hv2 Hs. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E k1 v1 H1), (U_atom E k2 v2 H2) by lia. apply zcanon_id. rewrite M64_val. lia.
Qed.
Lemma ne_acond_sum_ltu : forall E (k1 k2 : nat) v1 v2 c, ew E k1 = Z_to_bv 64 v1 -> ew E k2 = Z_to_bv 64 v2 ->
  0 <= v1 -> 0 <= v2 -> v1 + v2 < c -> c < 2 ^ 64 ->
  acond_ok E (mkAC BC_LTU (SAlu ALU_ADD (SOff k1 0) (SOff k2 0)) (SLit c)).
Proof.
  intros E k1 k2 v1 v2 c H1 H2 Hv1 Hv2 Hs Hc. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, (ne_U_add2 E k1 k2 v1 v2 H1 H2) by lia. rewrite U_lit by lia. apply Z.ltb_lt. lia.
Qed.
Lemma ne_acond_sum_geu : forall E (k1 k2 : nat) v1 v2 c, ew E k1 = Z_to_bv 64 v1 -> ew E k2 = Z_to_bv 64 v2 ->
  0 <= v1 -> 0 <= v2 -> v1 + v2 < 2 ^ 64 -> 0 <= c <= v1 + v2 ->
  acond_ok E (mkAC BC_GEU (SAlu ALU_ADD (SOff k1 0) (SOff k2 0)) (SLit c)).
Proof.
  intros E k1 k2 v1 v2 c H1 H2 Hv1 Hv2 Hs Hc. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, (ne_U_add2 E k1 k2 v1 v2 H1 H2) by lia. rewrite U_lit by lia.
  apply negb_true_iff. apply Z.ltb_ge. lia.
Qed.
Lemma ne_acond_eq0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v = 0 ->
  acond_ok E (mkAC BC_EQ (SOff k 0) (SLit 0)).
Proof.
  intros E k v Hk Hv H0. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_eq_U, (U_atom E k v Hk Hv), U_lit by lia. apply Z.eqb_eq. exact H0.
Qed.
Lemma ne_acond_ne0 : forall E (k : nat) v, ew E k = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> v <> 0 ->
  acond_ok E (mkAC BC_NE (SOff k 0) (SLit 0)).
Proof.
  intros E k v Hk Hv H0. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ne_U, (U_atom E k v Hk Hv), U_lit by lia. apply negb_true_iff. apply Z.eqb_neq. exact H0.
Qed.
(* unsigned tests between two atoms (nl_end's `bltu n, at + 4`) *)
Lemma ne_acond_atoms_ltu : forall E (k1 k2 : nat) v1 v2 d, ew E k1 = Z_to_bv 64 v1 -> ew E k2 = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v2 + d < 2 ^ 64 -> v1 < v2 + d ->
  acond_ok E (mkAC BC_LTU (SOff k1 0) (SOff k2 d)).
Proof.
  intros E k1 k2 v1 v2 d H1 H2 Hv1 Hv2 Hd Hlt. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_ltu_U, (U_atom E k1 v1 H1 Hv1), (U_atom_off E k2 v2 d H2 Hv2 Hd). apply Z.ltb_lt. exact Hlt.
Qed.
Lemma ne_acond_atoms_geu : forall E (k1 k2 : nat) v1 v2 d, ew E k1 = Z_to_bv 64 v1 -> ew E k2 = Z_to_bv 64 v2 ->
  0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> 0 <= v2 + d < 2 ^ 64 -> v2 + d <= v1 ->
  acond_ok E (mkAC BC_GEU (SOff k1 0) (SOff k2 d)).
Proof.
  intros E k1 k2 v1 v2 d H1 H2 Hv1 Hv2 Hd Hge. unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite branch_geu_U, (U_atom E k1 v1 H1 Hv1), (U_atom_off E k2 v2 d H2 Hv2 Hd).
  apply negb_true_iff. apply Z.ltb_ge. exact Hge.
Qed.

(* the shadow hull of a sub-range *)
Lemma ne_hull_sub : forall (rd : Z -> option Z) w N d n, shadow_hull_vis rd w N -> w <= d -> d + n <= w + N -> 0 < n ->
  shadow_hull_vis rd d n.
Proof. intros rd w N d n H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *. lia. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ==========================================================================
   1. The atoms of a seated state
   ========================================================================== *)

Lemma ne_E_reg : forall cx pos regs3 n f (k : nat) (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (ne_E cx pos regs3 n f) k = getr regs3 r.
Proof.
  intros cx pos regs3 n f k r H. unfold ne_E.
  pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
Lemma ne_E_extra : forall cx pos regs3 n f j, (j < 28)%nat ->
  ew (ne_E cx pos regs3 n f) (32 + j) = nth j (ne_extra cx pos n f) (Z_to_bv 64 0).
Proof. intros cx pos regs3 n f j Hj. unfold ne_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. Qed.

Section e.
Variables (cx : necx) (pos : Z) (regs3 : bvmap 5 word) (n f : Z).
#[local] Notation E := (ne_E cx pos regs3 n f).
Lemma ne_E32 : ew E 32 = w64 SHADOW_OFF. Proof. exact (ne_E_extra cx pos regs3 n f 0 ltac:(lia)). Qed.
Lemma ne_E33 : ew E 33 = w64 n. Proof. exact (ne_E_extra cx pos regs3 n f 1 ltac:(lia)). Qed.
Lemma ne_E34 : ew E 34 = w64 f. Proof. exact (ne_E_extra cx pos regs3 n f 2 ltac:(lia)). Qed.
Lemma ne_E35 : ew E 35 = w64 (ne_w cx). Proof. exact (ne_E_extra cx pos regs3 n f 3 ltac:(lia)). Qed.
Lemma ne_E36 : ew E 36 = w64 (ne_F cx pos). Proof. exact (ne_E_extra cx pos regs3 n f 4 ltac:(lia)). Qed.
Lemma ne_E37 : ew E 37 = w64 (ne_FL cx pos). Proof. exact (ne_E_extra cx pos regs3 n f 5 ltac:(lia)). Qed.
Lemma ne_E38 : ew E 38 = w64 (ne_Fsh cx pos). Proof. exact (ne_E_extra cx pos regs3 n f 6 ltac:(lia)). Qed.
Lemma ne_E39 : ew E 39 = w64 (ne_sp cx). Proof. exact (ne_E_extra cx pos regs3 n f 7 ltac:(lia)). Qed.
Lemma ne_E40 : ew E 40 = w64 (ne_sp1 cx). Proof. exact (ne_E_extra cx pos regs3 n f 8 ltac:(lia)). Qed.
Lemma ne_E41 : ew E 41 = w64 (ne_n0 cx). Proof. exact (ne_E_extra cx pos regs3 n f 9 ltac:(lia)). Qed.
Lemma ne_E42 : ew E 42 = getr (n_regs cx) 11.
Proof. refine (eq_trans (ne_E_extra cx pos regs3 n f 10 ltac:(lia)) _). apply w64_bv_unsigned. Qed.
Lemma ne_E43 : ew E 43 = w64 (ne_cutv (ne_cut cx)). Proof. exact (ne_E_extra cx pos regs3 n f 11 ltac:(lia)). Qed.
Lemma ne_Esave : forall i, (i < 13)%nat ->
  ew E (44 + i) = getr (n_regs cx) (snd (nth i ne_saves (0, 0%bv))).
Proof.
  intros i Hi. replace (44 + i)%nat with (32 + (12 + i))%nat by lia.
  rewrite (ne_E_extra cx pos regs3 n f (12 + i) ltac:(lia)).
  do 13 (destruct i as [|i]; [reflexivity|]). lia.
Qed.
Lemma ne_E57 : ew E 57 = w64 (ne_cut cx). Proof. exact (ne_E_extra cx pos regs3 n f 25 ltac:(lia)). Qed.
Lemma ne_E58 : ew E 58 = w64 (ne_w cx + n). Proof. exact (ne_E_extra cx pos regs3 n f 26 ltac:(lia)). Qed.
Lemma ne_E59 : ew E 59 = w64 (ne_w cx + ne_n0 cx). Proof. exact (ne_E_extra cx pos regs3 n f 27 ltac:(lia)). Qed.
End e.

(* ==========================================================================
   2. What the contract's premises give
   ========================================================================== *)

Lemma ne_base_facts : forall cx, ne_base SK B cx ->
  0 <= ne_w cx /\ ne_w cx + NW_SIZE + 1 <= 2 ^ 47 /\
  (ne_w cx + NW_SIZE < SHADOW_OFF \/ kHighMemBeg <= ne_w cx) /\
  ne_sp cx mod 16 = 0 /\ alloc_ceiling + NL_ERROR_AK <= ne_sp cx /\ ne_sp cx <= 2 ^ 47 /\
  n_sp0 cx - n_STK cx <= ne_sp cx - NL_ERROR_AK /\ ne_sp cx <= n_sp0 cx /\
  (ne_w cx + NW_SIZE <= ne_sp cx - NL_ERROR_AK \/ ne_sp cx <= ne_w cx) /\
  0 <= ne_n0 cx <= 4096 /\ 0 <= ne_cutv (ne_cut cx) <= 20 /\ 0 <= ne_cut cx < 2 ^ 64 /\
  ne_sp cx - 176 <= ne_sp1 cx <= ne_sp cx - 160 /\ ne_sp1 cx mod 32 = 0.
Proof.
  intros cx (HPRE & HA & HWF & HAP & HCUT & HAM & HRA & HHV).
  pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
  assert (Hceil : alloc_ceiling <= n_sp0 cx - n_STK cx) by (eapply (aj_stk_ceiling SK SEGS B); exact HJ).
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & _ & _ & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (bv_unsigned_in_range 64 (getr (n_regs cx) 2)) as Hsp64.
  pose proof (bv_unsigned_in_range 64 (getr (n_regs cx) 12)) as Hc64.
  change (bv_modulus 64) with (2 ^ 64) in Hsp64, Hc64.
  pose proof HA as ((HAB & _) & _). pose proof HAB as (Hw0 & _ & _).
  destruct HWF as [Hn Hf]. unfold NL_CHUNK_MAX in Hn.
  unfold amem_range, NW_SIZE, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
  unfold apart_frame in HAP. fold (ne_sp cx) in Hal16, Hwlo, Hwhi, HAP. fold (ne_w cx) in HAP, Hw0.
  assert (Hsp2 : 0 <= ne_sp cx - 160).
  { unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in Hwlo. lia. }
  pose proof (sp1_facts (ne_sp cx - 160) Hsp2 ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hs1 & Hs2 & _).
  unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *.
  unfold ne_cutv, ne_cut, ne_w, ne_n0, ne_sp1, aarg, argZ in *. fold (ne_sp cx) in *.
  pose proof (bv_unsigned_in_range 64 (getr (n_regs cx) (Z_to_bv 5 (10 + 2)))) as Hc64'.
  change (bv_modulus 64) with (2 ^ 64) in Hc64'.
  unfold NL_ERR_BODY, SHADOW_OFF, NW_SIZE in *. rewrite C3.
  repeat split; try lia;
    try (destruct (_ <? _) eqn:E; [apply Z.ltb_lt in E; destruct HCUT; lia | apply Z.ltb_ge in E; lia]);
    try exact Hs2.
Qed.

(* the values of s3 (w + 4096) and s11 (its shadow cell) in a seated state *)
Lemma ne_den19 : forall cx pos regs3 n f, sv_denot (ne_E cx pos regs3 n f) (SOff 35 4096) = w64 (ne_w cx + 4096).
Proof.
  intros cx pos regs3 n f. pose proof (bv_unsigned_in_range 64 (getr (n_regs cx) (Z_to_bv 5 (10 + 0)))) as Hw.
  change (bv_modulus 64) with (2 ^ 64) in Hw.
  apply (sv_offc _ 35 (ne_w cx) 4096 (ne_E35 cx pos regs3 n f)). unfold ne_w, aarg, argZ. exact Hw.
Qed.
Lemma ne_den27 : forall cx pos regs3 n f, ne_base SK B cx ->
  sv_denot (ne_E cx pos regs3 n f) ne_s11sv = w64 (SHADOW_OFF + (ne_w cx + 4096) / 8).
Proof.
  intros cx pos regs3 n f HB. pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & _).
  unfold NW_SIZE in Hw47. unfold ne_s11sv.
  apply (denot_shadow_cell_off _ 35 32 (ne_w cx) 4096 SHADOW_OFF (ne_E35 cx pos regs3 n f) ltac:(lia) ltac:(lia)
    (ne_E32 cx pos regs3 n f)); unfold SHADOW_OFF; [lia|].
  assert ((ne_w cx + 4096) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.


(* F's shadow bytes, as the chunks of region 38 *)
Lemma ne_sh_chunks_ok : forall E (H : word -> bool) m base sh,
  (forall i, (i < 16)%nat -> aview SEGS H m (base + Z.of_nat i) = Some (nth i sh 0)) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict H m) base) (ne_sh_chunks sh).
Proof.
  intros E H m base sh Hsh. unfold ne_sh_chunks. apply Forall_forall. intros c Hc.
  apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
  specialize (Hsh i ltac:(lia)). unfold aview in Hsh.
  destruct (mbyte SEGS (mrestrict H m) (base + Z.of_nat i)) as [b|] eqn:Eb; [|discriminate].
  cbn [option_map] in Hsh. injection Hsh as Hv.
  pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
  apply (chunk_ok_val SEGS E _ base (Z.of_nat i) 1%N (SLit (nth i sh 0)) (nth i sh 0)).
  - rewrite denot_lit_U, U_SLit, zcanon_id by (rewrite M64_val; lia). reflexivity.
  - cbn. lia.
  - cbn. lia.
  - apply val_mem1_of_mbyte; [lia|]. rewrite Eb. f_equal. rewrite <- Hv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ==========================================================================
   3. THE SEAT
   ========================================================================== *)

Lemma ne_seat : forall cx pos S3 memA regs3 mem3 md3 n f sh o upd wsh xr xc,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> ne_j SK B cx pos S3 memA regs3 mem3 md3 n f sh ->
  Forall (fun eu : bv 5 * sv => bv_eqb (fst eu) 0 = false /\
            getr regs3 (fst eu) = sv_denot (ne_E cx pos regs3 n f) (snd eu)) upd ->
  ne_xr_ok cx n xr -> conds_ok (ne_E cx pos regs3 n f) xc ->
  img_env pa_val A_LIM (ne_E cx pos regs3 n f) /\
  st_ok_pi SEGS pa_val (ne_E cx pos regs3 n f) (ne_ss o upd wsh sh xr xc)
    (restrict (w_H (n_W cx)) (mkst regs3 (Z_to_bv 64 (BASE + (AF_nl_error + o))) mem3 (seg_rom SEGS))) /\
  sh_ok SEGS ne_Bx ne_SH (ne_E cx pos regs3 n f) (mrestrict (w_H (n_W cx)) mem3).
Proof.
  intros cx pos S3 memA regs3 mem3 md3 n f sh o upd wsh xr xc HB HF HJ HU HX HC.
  pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & Hcut' & Hcut64 & Hs1r & Hs1a).
  destruct HF as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  destruct HJ as (HJX & _ & _ & R2 & R3 & R4 & R8 & R9 & R26 & HSV & HSL & HNW & Hn0n &
    HSW & HHV & HFLv & HFp & Hshl & Hsh & HFsp & UN & HG).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct HNW as (_ & _ & Hpres & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in Hnr.
  unfold NW_SIZE, NW_N, NW_FULL, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *.
  set (E := ne_E cx pos regs3 n f) in *.
  assert (HEI : img_env pa_val A_LIM E) by (unfold E, ne_E; apply Eimg_env).
  set (w := ne_w cx) in *. set (F := ne_F cx pos) in *. set (sp := ne_sp cx) in *. set (sp1 := ne_sp1 cx) in *.
  assert (HF8 : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + F / 8) by reflexivity.
  assert (U35 : bv_unsigned (ew E 35) = w) by (unfold E; rewrite ne_E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = F) by (unfold E; rewrite ne_E36; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = SHADOW_OFF + F / 8)
    by (unfold E; rewrite ne_E38, HFsh; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U39 : bv_unsigned (ew E 39) = sp) by (unfold E; rewrite ne_E39; apply unsigned_lit_small; lia).
  assert (U40 : bv_unsigned (ew E 40) = sp1) by (unfold E; rewrite ne_E40; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (unfold E; rewrite ne_E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U58 : bv_unsigned (ew E 58) = w + n) by (unfold E; rewrite ne_E58; apply unsigned_lit_small; lia).
  assert (U59 : bv_unsigned (ew E 59) = w + ne_n0 cx) by (unfold E; rewrite ne_E59; apply unsigned_lit_small; lia).
  split; [exact HEI|].
  split.
  - rewrite restrict_mkst_fx. unfold ne_ss. apply pa_entry_st_ok_full.
    + (* the registers *)
      apply regs_ok_sets_keep; [unfold E, ne_E; apply regs_ok_Eimg_Ereg|].
      apply Forall_app. split; [|exact HU].
      unfold ne_upd_common.
      repeat apply Forall_cons; try apply Forall_nil; (split; [reflexivity|]); cbn [fst snd].
      * rewrite R2. unfold E. symmetry. apply (sv_off0 _ _ _ (ne_E40 cx pos regs3 n f)).
      * rewrite R8. unfold E. symmetry. apply (sv_off0 _ _ _ (ne_E39 cx pos regs3 n f)).
      * rewrite R9. unfold E. symmetry. apply (sv_off0 _ _ _ (ne_E40 cx pos regs3 n f)).
      * rewrite R26. unfold E. symmetry. apply (sv_off0 _ _ _ (ne_E32 cx pos regs3 n f)).
    + destruct HX as [->|[[-> _]|[[-> _]|[-> _]]]]; destruct wsh; vm_compute; reflexivity.
    + (* the regions *)
      apply Forall_app. split.
      { unfold ne_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        * rewrite U35. split; [lia|]. split; [lia|]. split.
          { intros o' Ho'. apply (Hpres (o')). unfold NW_SIZE. lia. }
          apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
          -- apply (chunk_ok_val SEGS E _ w 4096 8%N (SOff 33 0) n);
               [apply (sv_off0 _ _ _ (ne_E33 cx pos regs3 n f)) | cbn; lia | cbn; lia | exact Hnv].
          -- apply (chunk_ok_val SEGS E _ w 4104 4%N (SOff 34 0) f);
               [apply (sv_off0 _ _ _ (ne_E34 cx pos regs3 n f)) | cbn; lia | cbn; lia | exact Hfv].
        * rewrite U36. split; [lia|]. split; [lia|]. split.
          { intros o' Ho'. apply (apresent_writable SEGS). apply HFp. lia. }
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E _ F 120 8%N (SOff 37 0) (ne_FL cx pos));
            [apply (sv_off0 _ _ _ (ne_E37 cx pos regs3 n f)) | cbn; lia | cbn; lia | exact HFLv].
        * rewrite U38. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF; lia|]. split.
          { intros o' Ho'. apply (apresent_writable SEGS). rewrite <- HFsh. apply HFsp. destruct wsh; lia. }
          apply ne_sh_chunks_ok. rewrite <- HFsh. exact Hsh.
        * rewrite U40. split; [lia|]. split; [lia|].
          split; [intros o' Ho'; apply (apresent_writable SEGS);
                  apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJX); lia|].
          apply Forall_cons; [|apply Forall_nil].
          apply (chunk_ok_val SEGS E _ sp1 24 8%N (SOff 57 0) (ne_cut cx));
            [apply (sv_off0 _ _ _ (ne_E57 cx pos regs3 n f)) | cbn; lia | cbn; lia | exact HSL].
        * rewrite U39. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
          unfold ne_save_chunks, ne_saves in *. cbn [map combine seq fst].
          repeat (apply Forall_cons; [|]); try apply Forall_nil;
          lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal 8 (SOff ?k 0))) =>
            let i := eval vm_compute in (k - 44)%nat in
            pose proof (ne_Esave cx pos regs3 n f i ltac:(lia)) as Ei; cbn [nth snd ne_saves Nat.add] in Ei;
            lazymatch type of Ei with _ = getr (n_regs cx) ?r =>
            pose proof (proj1 (Forall_forall _ _) HSV (o, r)
              ltac:(cbn [In]; repeat (first [left; reflexivity | right]))) as V0;
            cbn [fst snd] in V0;
            apply (chunk_ok_val SEGS E _ sp o 8%N (SOff k 0) (bv_unsigned (getr (n_regs cx) r)));
              [ apply sv_off0; unfold E; rewrite Ei; symmetry; apply w64_bv_unsigned
              | cbn [Z.of_N]; change (2 ^ (8 * 8)) with (bv_modulus 64); apply bv_unsigned_in_range
              | cbn; lia | exact V0 ] end end. }
      destruct HX as [->|[[-> Hk]|[[-> Hk]|[-> Hk]]]]; [apply Forall_nil| | |];
        (apply Forall_cons; [|apply Forall_nil]); unfold region_ok, ne_put_region, ne_end_region;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
        rewrite ?U58, ?U59; (split; [lia|]); (split; [lia|]);
        (split; [|apply Forall_nil]); intros o' Ho'; rewrite <- Z.add_assoc; apply (Hpres _); unfold NW_SIZE; lia.
    + (* disjointness *)
      destruct HX as [->|[[-> Hk]|[[-> Hk]|[-> Hk]]]];
      unfold ne_regions, ne_put_region, ne_end_region; cbn [app pairwise_disjoint all_disjoint]; unfold extent_disjoint;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U35, ?U36, ?U38, ?U39, ?U40, ?U58, ?U59;
      unfold NW_SIZE, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *;
      repeat split; lia.
    + (* the facts *)
      split; [|split; [exact HC|]].
      * unfold ne_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        unfold E. rewrite ne_E32, ne_E33, ne_E34, ne_E35, ne_E36, ne_E37, ne_E38, ne_E39, ne_E40, ne_E41, ne_E43,
          ne_E58, ne_E59.
        unfold w64. rewrite !unsigned_lit_small by (unfold NW_SIZE, SHADOW_OFF in *; lia).
        change (2 ^ 0) with 1. change (2 ^ 6) with 64. change (2 ^ 3) with 8. change (2 ^ 4) with 16.
        change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
        unfold NE_SB, SHADOW_OFF, NW_SIZE in *.
        repeat match goal with |- _ /\ _ => split end; try lia.
      * unfold ne_facts. cbn [f_alias alias_ok shadow_decl]. split.
        { unfold E. apply (shadow_decl_ok _ 36 32 38 F SHADOW_OFF (ne_E36 cx pos regs3 n f) ltac:(lia)
            (ne_E32 cx pos regs3 n f)). rewrite ne_E38. reflexivity. }
        unfold E.
        rewrite (sv_off0 _ 58 _ (ne_E58 cx pos regs3 n f)), (sv_off0 _ 59 _ (ne_E59 cx pos regs3 n f)).
        rewrite !denot_lit_U, !U_SAlu. cbn [zalu_raw].
        rewrite (U_atom _ 35 w (ne_E35 cx pos regs3 n f)), (U_atom _ 33 n (ne_E33 cx pos regs3 n f)),
          (U_atom _ 41 (ne_n0 cx) (ne_E41 cx pos regs3 n f)) by lia.
        rewrite !zcanon_id by (rewrite M64_val; lia).
        repeat match goal with
               | |- _ /\ _ => split
               | |- True => exact I
               | |- Z_to_bv 64 _ = Z_to_bv 64 _ => f_equal; lia
               end.
  - (* the shadow entries *)
    unfold sh_ok, ne_SH. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold ne_Bx.
      rewrite (U_atom E 32 SHADOW_OFF (ne_E32 cx pos regs3 n f)) by (unfold SHADOW_OFF; lia).
      rewrite (U_atom E 35 w (ne_E35 cx pos regs3 n f)) by lia. split.
      * rewrite <- (aview_rd_of SEGS). apply (range_addressable_sub _ _ w NW_SIZE); [exact HSW | lia | unfold NW_SIZE; lia].
      * intros a Ha. unfold NW_SIZE, SHADOW_OFF, kHighMemBeg in *. lia.
    + apply (shent_app_of_app SEGS (* segs *) E ne_Bx 36 F 0 128).
      * unfold ne_Bx. exact (U_atom E 32 SHADOW_OFF (ne_E32 cx pos regs3 n f) ltac:(unfold SHADOW_OFF; lia)).
      * exact (U_atom E 36 F (ne_E36 cx pos regs3 n f) ltac:(lia)).
      * lia.
      * lia.
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold ne_Bx.
      rewrite (U_atom E 32 SHADOW_OFF (ne_E32 cx pos regs3 n f)) by (unfold SHADOW_OFF; lia).
      rewrite (U_atom E 58 (w + n) (ne_E58 cx pos regs3 n f)) by (unfold NW_SIZE in *; lia). split.
      * rewrite <- (aview_rd_of SEGS). apply (range_addressable_sub _ _ w NW_SIZE); [exact HSW | lia | unfold NW_SIZE; lia].
      * intros a Ha. unfold NW_SIZE, SHADOW_OFF, kHighMemBeg in *. lia.
    + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold ne_Bx.
      rewrite (U_atom E 32 SHADOW_OFF (ne_E32 cx pos regs3 n f)) by (unfold SHADOW_OFF; lia).
      rewrite (U_atom E 59 (w + ne_n0 cx) (ne_E59 cx pos regs3 n f)) by (unfold NW_SIZE in *; lia). split.
      * rewrite <- (aview_rd_of SEGS). apply (range_addressable_sub _ _ w NW_SIZE); [exact HSW | lia | unfold NW_SIZE; lia].
      * intros a Ha. unfold NW_SIZE, SHADOW_OFF, kHighMemBeg in *. lia.
Qed.

(* ==========================================================================
   4. THE STEP: a join after a step that wrote only ne_X
   ========================================================================== *)

Definition ne_common_regs : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 26%bv].

Lemma ne_X_Z : forall cx pos a, ne_base SK B cx -> ne_X cx pos a -> ne_Z cx pos a.
Proof.
  intros cx pos a HB HX. pose proof (ne_base_facts cx HB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & _).
  unfold ne_X, ne_Z, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
Qed.

Lemma mbyte_some_grows : forall (m m' : word -> option byte) a b,
  mem_grows m m' -> mbyte SEGS m a = Some b -> exists b', mbyte SEGS m' a = Some b'.
Proof.
  intros m m' a b HG Hb. unfold mbyte in *. destruct (m (Z_to_bv 64 a)) as [b0|] eqn:E0.
  - assert (Hn : m' (Z_to_bv 64 a) <> None) by (apply HG; rewrite E0; discriminate).
    destruct (m' (Z_to_bv 64 a)) as [b1|]; [exists b1; reflexivity | congruence].
  - destruct (m' (Z_to_bv 64 a)) as [b1|]; [exists b1; reflexivity | exists b; exact Hb].
Qed.

Lemma ne_j_step : forall cx pos S3 memA regs3 mem3 md3 n f sh regs4 mem4 md4 n' f' sh',
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> ne_j SK B cx pos S3 memA regs3 mem3 md3 n f sh ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((1, pos) :: n_own cx) (n_lyc cx) S3 (n_W cx) mem4 md4 (n_k cx) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ne_X cx pos a ->
     aview SEGS (w_H (n_W cx)) mem4 a = aview SEGS (w_H (n_W cx)) mem3 a) ->
  mem_grows (rdW (n_W cx) mem3) (rdW (n_W cx) mem4) ->
  Forall (fun r => getr regs4 r = getr regs3 r) ne_common_regs ->
  val_mem SEGS (rdW (n_W cx) mem4) (ne_w cx + NW_N) 8 n' -> val_mem SEGS (rdW (n_W cx) mem4) (ne_w cx + NW_FULL) 4 f' ->
  n <= n' <= NL_CHUNK_MAX -> 0 <= f' <= 1 ->
  val_mem SEGS (rdW (n_W cx) mem4) (ne_F cx pos + 120) 8 (ne_FL cx pos) ->
  length sh' = 16%nat ->
  (forall i, (i < 16)%nat -> aview SEGS (w_H (n_W cx)) mem4 (ne_Fsh cx pos + Z.of_nat i) = Some (nth i sh' 0)) ->
  ne_j SK B cx pos S3 memA regs4 mem4 md4 n' f' sh'.
Proof.
  intros cx pos S3 memA regs3 mem3 md3 n f sh regs4 mem4 md4 n' f' sh' HB HF HJ HJ4 Hfds Hfs UN4 HG4 HR Hn' Hf'
    Hnr Hfr HFL' Hl' Hsh'.
  pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & Hwapp & Hal16 & Hceil & Hsp47 & Hwin0 & Hwin1 & Hap &
    Hn0 & Hcut' & Hcut64 & Hs1r & Hs1a).
  pose proof HF as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  destruct HJ as (HJX & Hfds3 & Hfs3 & R2 & R3 & R4 & R8 & R9 & R26 & HSV & HSL & HNW &
    Hn0n & HSW & HHV & HFLv & HFp & Hshl & Hsh & HFsp & UN & HG).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold NW_SIZE in Hw47, Hwapp, Hap. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in Hceil, Hwin0, Hap.
  set (W := n_W cx) in *. set (w := ne_w cx) in *. set (F := ne_F cx pos) in *.
  set (sp := ne_sp cx) in *. set (sp1 := ne_sp1 cx) in *.
  assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + F / 8) by reflexivity.
  assert (HF8 : F / 8 * 8 = F) by (pose proof (Z_div_mod_eq_full F 64); pose proof (Z_div_mod_eq_full F 8); lia).
  (* a byte outside ne_X keeps its view and its mbyte *)
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ ne_X cx pos a ->
     mbyte SEGS (rdW W mem4) a = mbyte SEGS (rdW W mem3) a).
  { intros a Ha Hx. apply (mbyte_of_aview SEGS). exact (UN4 a Ha Hx). }
  (* the stack words below the realigned sp and above it are outside ne_X *)
  assert (Hstk : forall a, sp1 + 24 <= a < sp1 + 32 \/ sp - 104 <= a < sp -> ~ ne_X cx pos a).
  { intros a Ha Hx. unfold ne_X, NW_SIZE, ESTACK in Hx. fold sp1 w F in Hx. rewrite HFsh in Hx.
    unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK, SHADOW_OFF in *. lia. }
  (* the shadow bytes of w are outside ne_X *)
  assert (Hwsh1 : forall x, w <= x < w + NW_SIZE -> ~ ne_X cx pos (shadow_addr x)).
  { intros x Hx HX. unfold ne_X in HX. fold sp1 w F in HX. rewrite HFsh in HX.
    unfold shadow_addr, NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK, SHADOW_OFF, kLowShadowBeg in *.
    rewrite C3 in *. lia. }
  unfold ne_j. fold W w F sp sp1.
  inversion HR as [|? ? E2 HR1]; subst; inversion HR1 as [|? ? E3 HR2]; subst; inversion HR2 as [|? ? E4 HR3]; subst;
  inversion HR3 as [|? ? E8 HR4]; subst; inversion HR4 as [|? ? E9 HR5]; subst; inversion HR5 as [|? ? E26 _]; subst.
  split; [exact HJ4|]. split; [rewrite Hfds; exact Hfds3|]. split; [rewrite Hfs; exact Hfs3|].
  rewrite E2, E3, E4, E8, E9, E26.
  do 6 (split; [assumption|]).
  split.
  { (* the saved words *)
    apply Forall_forall. intros [o r] Hin. pose proof (proj1 (Forall_forall _ _) HSV (o, r) Hin) as V.
    assert (Ho : -104 <= o <= -8) by (unfold ne_saves in Hin; cbn in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
    cbn [fst snd] in V |- *. intros kk Hkk. rewrite KV; [exact (V kk Hkk) | lia | apply Hstk; lia]. }
  split.
  { intros kk Hkk. rewrite KV; [exact (HSL kk Hkk) | lia | apply Hstk; lia]. }
  split.
  { destruct HNW as (Hw0' & Hwl & Hpres & _). split; [exact Hw0'|]. split; [exact Hwl|]. split.
    - intros i Hi. destruct (Hpres i Hi) as ((b & Hb) & Hwr). split.
      + exact (mbyte_some_grows _ _ _ b HG4 Hb).
      + exact (writable_at_grows SEGS _ _ _ HG4 Hwr).
    - split; [exact Hn'|]. split; [exact Hf'|]. split; [lia | exact Hfr]. }
  split; [lia|].
  split.
  { apply (ra_shadow_eq (aview SEGS (w_H W) mem3)); [exact HSW|]. intros x Hx.
    apply UN4; [unfold shadow_addr, SHADOW_OFF, NW_SIZE in *; pose proof (Z.div_pos x 8); lia | exact (Hwsh1 x Hx)]. }
  split.
  { intros s Hs. specialize (HHV s Hs). unfold aview in HHV |- *.
    destruct (mbyte SEGS (rdW W mem3) s) as [b|] eqn:Eb; [|exfalso; apply HHV; reflexivity].
    destruct (mbyte_some_grows _ _ _ b HG4 Eb) as [b' Eb']. rewrite Eb'. discriminate. }
  split; [exact HFL'|].
  split; [intros i Hi; eapply apresent_grows; [exact HG4 | exact (HFp i Hi)]|].
  split; [exact Hl'|]. split; [exact Hsh'|].
  split; [intros i Hi; eapply apresent_grows; [exact HG4 | exact (HFsp i Hi)]|].
  split.
  { intros a Ha HZ. rewrite UN4; [exact (UN a Ha HZ) | exact Ha |]. intros HX. exact (HZ (ne_X_Z cx pos a HB HX)). }
  intros a Ha. eapply apresent_grows; [exact HG4 | exact (HG a Ha)].
Qed.

(* ==========================================================================
   5. WHAT A SEATED RUN MAY WRITE
   ========================================================================== *)

(* The writable windows of a seated state: w's fields, a put's or nl_end's bytes (all inside w), F, F's shadow
   (when wsh), and F's spill slot at sp1 + 48. *)
Lemma ne_windows : forall cx pos S3 memA regs3 n f wsh sh xr b wlo whi a,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> 0 <= n <= 4096 -> ne_xr_ok cx n xr ->
  In (b, wlo, whi) (windows (ne_regions wsh sh ++ xr)) ->
  base_val (ne_E cx pos regs3 n f) b + wlo <= a < base_val (ne_E cx pos regs3 n f) b + whi ->
  (ne_w cx <= a < ne_w cx + NW_SIZE) \/ (ne_F cx pos <= a < ne_F cx pos + 128) \/
  (wsh = true /\ ne_Fsh cx pos <= a < ne_Fsh cx pos + 16) \/ (ne_sp1 cx + 48 <= a < ne_sp1 cx + 56).
Proof.
  intros cx pos S3 memA regs3 n f wsh sh xr b wlo whi a HB HF Hn HX Hin Ha.
  pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & _ & _ & Hceil & Hsp47 & _ & _ & _ & Hn0 & _ & _ & Hs1r & _).
  destruct HF as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *.
  set (E := ne_E cx pos regs3 n f) in *.
  assert (HF8 : 0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + ne_F cx pos / 8) by reflexivity.
  assert (U35 : bv_unsigned (ew E 35) = ne_w cx) by (unfold E; rewrite ne_E35; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = ne_F cx pos) by (unfold E; rewrite ne_E36; apply unsigned_lit_small; lia).
  assert (U38 : bv_unsigned (ew E 38) = ne_Fsh cx pos)
    by (unfold E; rewrite ne_E38, HFsh; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U39 : bv_unsigned (ew E 39) = ne_sp cx) by (unfold E; rewrite ne_E39; apply unsigned_lit_small; lia).
  assert (U40 : bv_unsigned (ew E 40) = ne_sp1 cx) by (unfold E; rewrite ne_E40; apply unsigned_lit_small; lia).
  assert (U58 : bv_unsigned (ew E 58) = ne_w cx + n) by (unfold E; rewrite ne_E58; apply unsigned_lit_small; lia).
  assert (U59 : bv_unsigned (ew E 59) = ne_w cx + ne_n0 cx) by (unfold E; rewrite ne_E59; apply unsigned_lit_small; lia).
  destruct HX as [->|[[-> Hk]|[[-> Hk]|[-> Hk]]]];
  unfold ne_regions, ne_put_region, ne_end_region, windows in Hin; cbn [app map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin;
  repeat (destruct Hin as [Hq|Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Ha; rewrite ?U35, ?U36, ?U38, ?U39, ?U40, ?U58, ?U59 in Ha;
     destruct wsh;
     first [left; lia | right; left; lia | right; right; left; split; [reflexivity | lia]
           | right; right; right; lia | exfalso; lia] |]);
  destruct Hin.
Qed.

Lemma ne_windows_X : forall cx pos S3 memA regs3 n f wsh sh xr b wlo whi a,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> 0 <= n <= 4096 -> ne_xr_ok cx n xr ->
  In (b, wlo, whi) (windows (ne_regions wsh sh ++ xr)) ->
  base_val (ne_E cx pos regs3 n f) b + wlo <= a < base_val (ne_E cx pos regs3 n f) b + whi ->
  ne_X cx pos a /\ (wsh = false -> ~ (ne_Fsh cx pos <= a < ne_Fsh cx pos + 16)).
Proof.
  intros cx pos S3 memA regs3 n f wsh sh xr b wlo whi a HB HF Hn HX Hin Ha.
  pose proof (ne_windows cx pos S3 memA regs3 n f wsh sh xr b wlo whi a HB HF Hn HX Hin Ha) as HW.
  pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & Hwapp & _ & Hceil & Hsp47 & _ & _ & _ & _ & _ & _ & Hs1r & _).
  pose proof HF as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + ne_F cx pos / 8) by reflexivity.
  assert (HF8 : 0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  unfold ne_X, NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. rewrite HFsh in *.
  unfold SHADOW_OFF, kLowShadowBeg in *. rewrite C3 in *.
  split; [lia|]. intros Hw Hs. subst wsh. lia.
Qed.

(* a byte of w is the caller's to write, by the contract's ajw on its write set, at the state after
   frame_alloc_1 *)
Lemma ne_w_ajw : forall cx pos S3 memA a,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> ne_w cx <= a < ne_w cx + NW_SIZE ->
  (awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B (n_lyc cx) S3) (n_lyc cx)
     ((1, pos) :: n_own cx) a /\ ~ (n_sp0 cx <= a < n_sp0 cx + n_XO cx)) \/
  inG (n_G cx) a \/ (inFP (n_OUT cx) a /\ n_sp0 cx <= a < n_sp0 cx + n_XO cx).
Proof.
  intros cx pos S3 memA a HB HF Hw.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _).
  pose proof HF as (_ & _ & (f0 & HS3) & _).
  assert (HBL : ablocks B (n_lyc cx) S3 = ablocks B (n_lyc cx) (n_Sc cx)) by (rewrite HS3; apply ablocks_set_fs).
  rewrite HBL.
  assert (Hin' : inFP (ne_Wr cx) a).
  { exists (ne_w cx, ne_w cx + NW_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. }
  destruct (Hajw a Hin') as [[Haw Hxo]|Hrest]; [left|right; exact Hrest].
  split; [|exact Hxo].
  destruct Haw as [H1|[H1|[H1|(c & q & Hq & Hr)]]]; [left; exact H1 | right; left; exact H1 | right; right; left; exact H1 |].
  right; right; right. exists c, q. split; [right; exact Hq | exact Hr].
Qed.

(* the write obligation of a seated run: every writable byte is the caller's (w, by the contract's ajw), the
   side frame's (F and its shadow) or the call's own stack *)
Lemma ne_awr : forall cx pos S3 memA regs3 mem3 md3 n f sh wsh xr,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> ne_j SK B cx pos S3 memA regs3 mem3 md3 n f sh ->
  ne_xr_ok cx n xr ->
  awr_ok_x (ne_E cx pos regs3 n f) (ne_regions wsh sh ++ xr) (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx)
    (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B (n_lyc cx) S3) (n_lyc cx) ((1, pos) :: n_own cx).
Proof.
  intros cx pos S3 memA regs3 mem3 md3 n f sh wsh xr HB HF HJ HX a Ha.
  pose proof HJ as (HJX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & _). unfold NL_CHUNK_MAX in Hnr.
  destruct (in_wrange_windows _ _ _ Ha) as (b & wlo & whi & Hin & Hab).
  pose proof (ne_windows cx pos S3 memA regs3 n f wsh sh xr b wlo whi a HB HF Hnr HX Hin Hab) as HW.
  pose proof HB as (HPRE & _). pose proof HPRE as (HJ0 & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _ & _ & Hajw & _).
  pose proof HF as (_ & _ & (f0 & HS3) & _).
  assert (HBL : ablocks B (n_lyc cx) S3 = ablocks B (n_lyc cx) (n_Sc cx)) by (rewrite HS3; apply ablocks_set_fs).
  destruct HW as [Hw|[HFr|[[_ HFs]|Hsl]]].
  - (* w: the contract's ajw on its write set *)
    rewrite HBL.
    assert (Hin' : inFP (ne_Wr cx) a).
    { exists (ne_w cx, ne_w cx + NW_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. }
    destruct (Hajw a Hin') as [[Haw Hxo]|Hrest]; [left|right; exact Hrest].
    split; [|exact Hxo].
    destruct Haw as [H1|[H1|[H1|(c & q & Hq & Hr)]]]; [left; exact H1 | right; left; exact H1 | right; right; left; exact H1 |].
    right; right; right. exists c, q. split; [right; exact Hq | exact Hr].
  - left. eapply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low); [exact HJX | left; reflexivity |].
    left. unfold in_zr, frame_rng. cbn [fst snd]. exact HFr.
  - left. eapply (aj_gx_awr_frame SK SEGS B LAWS pa_segs_low); [exact HJX | left; reflexivity |].
    right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. exact HFs.
  - (* F's spill slot, in the call's own stack *)
    pose proof (ne_base_facts cx HB) as (_ & _ & _ & _ & _ & _ & Hwin0 & Hwin1 & _ & _ & _ & _ & Hs1r & _).
    unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *.
    left. split; [left; lia | lia].
Qed.

(* ==========================================================================
   6. READING A JOIN BACK FROM A RUN'S END STATE
   ========================================================================== *)

(* the registers every join carries are the seated state's, in the end state ss' *)
Definition ne_regs_same (s0 s1 : sstate) : bool :=
  forallb (fun r => sv_eqb (sr_get (ss_regs s1) r) (sr_get (ss_regs s0) r) && sv_atoms_lt 512 (sr_get (ss_regs s0) r))
    ne_common_regs.

Lemma ne_regs_after : forall (H : word -> bool) E E' s0 s1 ms0 ms1,
  st_ok_pi SEGS pa_val E s0 (restrict H ms0) -> st_ok SEGS E' s1 (restrict H ms1) ->
  YP06.env_agree 512 E E' -> ne_regs_same s0 s1 = true ->
  Forall (fun r => getr (ms_regs ms1) r = getr (ms_regs ms0) r) ne_common_regs.
Proof.
  intros H E E' s0 s1 ms0 ms1 HS0 HS1 HA HR. apply Forall_forall. intros r Hr.
  unfold ne_regs_same in HR. pose proof (proj1 (forallb_forall _ _) HR r Hr) as Hb.
  apply andb_prop in Hb as [Heq Hlt].
  rewrite (st_ok_restrict_reg SEGS H E' s1 ms1 r HS1), (st_ok_pi_restrict_reg H E s0 ms0 r HS0).
  rewrite (sv_eqb_denot E' _ _ Heq). exact (sv_denot_agree 512 E E' _ HA Hlt).
Qed.

(* a register of the end state, by its symbolic value *)
Lemma ne_reg_after : forall (H : word -> bool) E E' s1 ms1 (r : bv 5) e v,
  st_ok SEGS E' s1 (restrict H ms1) -> YP06.env_agree 512 E E' ->
  sr_get (ss_regs s1) r = e -> sv_atoms_lt 512 e = true -> sv_denot E e = v ->
  getr (ms_regs ms1) r = v.
Proof.
  intros H E E' s1 ms1 r e v HS HA He Hlt Hv.
  rewrite (st_ok_restrict_reg SEGS H E' s1 ms1 r HS), He. rewrite (sv_denot_agree 512 E E' _ HA Hlt). exact Hv.
Qed.

(* a value chunk of a region of the end state *)
Definition ne_chunk_of (rs : smem) (p : nat) (off : Z) : option (N * sv) :=
  match find (fun r => match YP09.r_base r with Some q => Nat.eqb q p | None => false end) rs with
  | Some r =>
      match find (fun c => Z.eqb (YP09.c_off c) off) (YP09.r_chunks r) with
      | Some (YP09.mkChunk _ (CVal sz e)) => Some (sz, e)
      | _ => None
      end
  | None => None
  end.

Lemma ne_chunk_of_val : forall (H : word -> bool) E' s1 ms1 p off sz e b v,
  st_ok SEGS E' s1 (restrict H ms1) -> ne_chunk_of (ss_mem s1) p off = Some (sz, e) ->
  bv_unsigned (ew E' p) = b -> sv_denot E' e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N sz) -> Z.of_N sz <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms1)) (b + off) (N.to_nat sz) v.
Proof.
  intros H E' s1 ms1 p off sz e b v HS Hc Hb He Hv Hsz. unfold ne_chunk_of in Hc.
  destruct (find _ (ss_mem s1)) as [r|] eqn:Hr; [|discriminate].
  destruct (find_some _ _ Hr) as [Hin Hbase].
  destruct (YP09.r_base r) as [q|] eqn:Hq; [|discriminate]. apply Nat.eqb_eq in Hbase. subst q.
  destruct (find _ (YP09.r_chunks r)) as [[off' cv]|] eqn:Hcf; [|discriminate].
  destruct (find_some _ _ Hcf) as [Hcin Hoff]. cbn [YP09.c_off] in Hoff. apply Z.eqb_eq in Hoff. subst off'.
  destruct cv as [sz' e'| | |]; try discriminate. injection Hc as -> ->.
  destruct (In_nth_error _ _ Hin) as [i Hi].
  pose proof (st_ok_region_nth (segs := SEGS) E' s1 (restrict H ms1) i r HS Hi) as HR.
  destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck.
  rewrite Hq in Hck. cbn [base_val] in Hck. rewrite Hb in Hck.
  exact (val_of_chunk_ok SEGS E' _ b off sz e v Hck He Hv Hsz).
Qed.

(* F's 16 shadow bytes of the end state, by ne_sh_check *)
(* a one-byte literal chunk of a region of the end state: the byte is the literal's low byte *)
Lemma ne_chunk_byte : forall (H : word -> bool) E' s1 ms1 p off v b,
  st_ok SEGS E' s1 (restrict H ms1) -> ne_chunk_of (ss_mem s1) p off = Some (1%N, SLit v) ->
  bv_unsigned (ew E' p) = b -> aview SEGS H (ms_mem ms1) (b + off) = Some (v mod 256).
Proof.
  intros H E' s1 ms1 p off v b HS Hc Hb. unfold ne_chunk_of in Hc.
  destruct (find _ (ss_mem s1)) as [r|] eqn:Hr; [|discriminate].
  destruct (find_some _ _ Hr) as [Hin Hbase].
  destruct (YP09.r_base r) as [q|] eqn:Hq; [|discriminate]. apply Nat.eqb_eq in Hbase. subst q.
  destruct (find _ (YP09.r_chunks r)) as [[off' cv]|] eqn:Hcf; [|discriminate].
  destruct (find_some _ _ Hcf) as [Hcin Hoff]. cbn [YP09.c_off] in Hoff. apply Z.eqb_eq in Hoff. subst off'.
  destruct cv as [sz' e'| | |]; try discriminate. injection Hc as -> ->.
  destruct (In_nth_error _ _ Hin) as [i Hi].
  pose proof (st_ok_region_nth (segs := SEGS) E' s1 (restrict H ms1) i r HS Hi) as HR.
  destruct HR as (_ & _ & _ & Hcs). pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck.
  rewrite Hq in Hck. cbn [base_val] in Hck. rewrite Hb in Hck.
  destruct (Hck 0 ltac:(cbn; lia)) as (bt & Hcb & Hmb). cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hcb, Hmb.
  injection Hcb as <-. rewrite Z.add_0_r in Hmb.
  unfold aview. cbn [ms_mem restrict] in Hmb. rewrite Hmb. cbn [option_map]. f_equal.
  unfold YP09.byte_of_word. cbn [sv_denot]. rewrite Z.shiftr_0_r, Z_to_bv_unsigned, Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_mod_divide; try reflexivity; try (exists (2 ^ 56); reflexivity); try lia.
Qed.

Lemma ne_sh_after : forall (H : word -> bool) E' s1 ms1 b sh',
  st_ok SEGS E' s1 (restrict H ms1) -> ne_sh_check (ss_mem s1) sh' = true -> bv_unsigned (ew E' 38) = b ->
  length sh' = 16%nat /\
  forall i, (i < 16)%nat -> aview SEGS H (ms_mem ms1) (b + Z.of_nat i) = Some (nth i sh' 0).
Proof.
  intros H E' s1 ms1 b sh' HS Hc Hb. unfold ne_sh_check in Hc.
  apply andb_prop in Hc as [Hc Hall]. apply andb_prop in Hc as [Hlen Hrng].
  apply Nat.eqb_eq in Hlen. split; [exact Hlen|]. intros i Hi.
  pose proof (proj1 (forallb_forall _ _) Hall i ltac:(apply in_seq; lia)) as Hci.
  assert (Hco : exists v, ne_chunk_of (ss_mem s1) 38 (Z.of_nat i) = Some (1%N, SLit v) /\ v mod 256 = nth i sh' 0).
  { unfold ne_chunk_of. revert Hci.
    destruct (find _ (ss_mem s1)) as [r|]; [|intros Hf; discriminate Hf].
    destruct (find _ (YP09.r_chunks r)) as [[off' cv]|]; [|intros Hf; discriminate Hf].
    destruct cv as [sz' e'| | |]; try (intros Hf; discriminate Hf).
    destruct sz' as [|[sz'|sz'|]]; try (intros Hf; discriminate Hf).
    destruct e'; try (intros Hf; discriminate Hf).
    intros Hci. apply Z.eqb_eq in Hci. eexists. split; [reflexivity | exact Hci]. }
  destruct Hco as (v & Hco & Hv). rewrite <- Hv.
  exact (ne_chunk_byte H E' s1 ms1 38 (Z.of_nat i) v b HS Hco Hb).
Qed.

(* THE READ-BACK: a join after a seated run (or a callee) that wrote only its windows. *)
Lemma ne_after : forall cx pos S3 memA regs3 mem3 md3 n f sh o upd wsh xr xc E' s1 ms1 md4 n' f' sh',
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> ne_j SK B cx pos S3 memA regs3 mem3 md3 n f sh -> ne_xr_ok cx n xr ->
  st_ok_pi SEGS pa_val (ne_E cx pos regs3 n f) (ne_ss o upd wsh sh xr xc)
    (restrict (w_H (n_W cx)) (mkst regs3 (Z_to_bv 64 (BASE + (AF_nl_error + o))) mem3 (seg_rom SEGS))) ->
  YP06.env_agree 512 (ne_E cx pos regs3 n f) E' ->
  st_ok SEGS E' s1 (restrict (w_H (n_W cx)) ms1) ->
  ne_regs_same (ne_ss o upd wsh sh xr xc) s1 = true ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((1, pos) :: n_own cx) (n_lyc cx) S3 (n_W cx) (ms_mem ms1) md4 (n_k cx) ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  frame_of (ne_E cx pos regs3 n f) (ne_regions wsh sh ++ xr) (mrestrict (w_H (n_W cx)) mem3)
    (mrestrict (w_H (n_W cx)) (ms_mem ms1)) ->
  mem_grows (mrestrict (w_H (n_W cx)) mem3) (mrestrict (w_H (n_W cx)) (ms_mem ms1)) ->
  forall en ef,
  ne_chunk_of (ss_mem s1) 35 4096 = Some (8%N, en) -> sv_denot E' en = w64 n' ->
  ne_chunk_of (ss_mem s1) 35 4104 = Some (4%N, ef) -> sv_denot E' ef = w64 f' ->
  ne_chunk_of (ss_mem s1) 36 120 = Some (8%N, SOff 37 0) ->
  n <= n' <= NL_CHUNK_MAX -> 0 <= f' <= 1 ->
  (wsh = false -> sh' = sh) ->
  (wsh = true -> length sh' = 16%nat /\
     forall i, (i < 16)%nat -> aview SEGS (w_H (n_W cx)) (ms_mem ms1) (ne_Fsh cx pos + Z.of_nat i) = Some (nth i sh' 0)) ->
  ne_j SK B cx pos S3 memA (ms_regs ms1) (ms_mem ms1) md4 n' f' sh'.
Proof.
  intros cx pos S3 memA regs3 mem3 md3 n f sh o upd wsh xr xc E' s1 ms1 md4 n' f' sh'
    HB HF HJ HX HS0 HA HS1 HRS HJ4 Hfds Hfs HFr HG4 en ef Hcn Hen Hcf Hef Hcl Hn' Hf' Hsh0 Hsh1.
  pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof HF as (_ & _ & _ & HF4096 & HF64 & HFceil & _ & HFL & _ & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNW & _ & _ & _ & _ & _ & Hshl & Hsh & _).
  pose proof HNW as (_ & _ & _ & _ & _ & Hnr & Hfr). unfold NL_CHUNK_MAX in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (EA : forall k, (k < 512)%nat -> ew E' k = ew (ne_E cx pos regs3 n f) k)
    by (intros k Hk; apply (proj1 HA); exact Hk).
  assert (U35 : bv_unsigned (ew E' 35) = ne_w cx)
    by (rewrite EA by lia; rewrite ne_E35; apply unsigned_lit_small; unfold NW_SIZE in *; lia).
  assert (U36 : bv_unsigned (ew E' 36) = ne_F cx pos)
    by (rewrite EA by lia; rewrite ne_E36; apply unsigned_lit_small; pose proof asan_consts; lia).
  (* the windows: only ne_X changes, and F's shadow only when wsh *)
  assert (KV : forall a, 0 <= a < 2 ^ 64 ->
            ~ (ne_X cx pos a /\ (wsh = false -> ~ (ne_Fsh cx pos <= a < ne_Fsh cx pos + 16))) ->
            aview SEGS (w_H (n_W cx)) (ms_mem ms1) a = aview SEGS (w_H (n_W cx)) mem3 a).
  { apply (kept_of_frame (segs := SEGS) _ _ _ _ _ _ HFr).
    intros b wlo whi a Hin Hab.
    exact (ne_windows_X cx pos S3 memA regs3 n f wsh sh xr b wlo whi a HB HF Hnr HX Hin Hab). }
  apply (ne_j_step cx pos S3 memA regs3 mem3 md3 n f sh (ms_regs ms1) (ms_mem ms1) md4 n' f' sh' HB HF HJ HJ4).
  - exact Hfds.
  - exact Hfs.
  - intros a Ha HXa. apply KV; [exact Ha|]. intros [HX' _]. exact (HXa HX').
  - exact HG4.
  - exact (ne_regs_after (w_H (n_W cx)) _ _ _ _ _ _ HS0 HS1 HA HRS).
  - pose proof (ne_chunk_of_val (w_H (n_W cx)) E' s1 _ 35 4096 8%N en (ne_w cx) n' HS1 Hcn U35 Hen
      ltac:(cbn; lia) ltac:(cbn; lia)) as V. exact V.
  - pose proof (ne_chunk_of_val (w_H (n_W cx)) E' s1 _ 35 4104 4%N ef (ne_w cx) f' HS1 Hcf U35 Hef
      ltac:(cbn; lia) ltac:(cbn; lia)) as V. exact V.
  - unfold NL_CHUNK_MAX; lia.
  - exact Hf'.
  - pose proof (ne_chunk_of_val (w_H (n_W cx)) E' s1 _ 36 120 8%N (SOff 37 0) (ne_F cx pos) (ne_FL cx pos) HS1 Hcl U36
      ltac:(cbn [sv_denot]; rewrite EA by lia; rewrite ne_E37; rewrite Z.add_0_r;
            unfold w64; rewrite unsigned_lit_small by lia; reflexivity)
      ltac:(cbn; lia) ltac:(cbn; lia)) as V. exact V.
  - destruct wsh; [exact (proj1 (Hsh1 eq_refl)) | rewrite (Hsh0 eq_refl); exact Hshl].
  - destruct wsh; [exact (proj2 (Hsh1 eq_refl))|].
    rewrite (Hsh0 eq_refl). intros i Hi. rewrite KV.
    + exact (Hsh i Hi).
    + assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + ne_F cx pos / 8) by reflexivity.
      assert (0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; pose proof asan_consts; lia]).
      unfold SHADOW_OFF in HFsh. lia.
    + intros [_ Hn]. apply (Hn eq_refl). lia.
Qed.

(* a callee-saved register survives a call *)
Definition ne_saved_regs : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma ne_preserved_r : forall regs regs2, aregs_preserved regs regs2 ->
  forall r, In r ne_saved_regs -> getr regs2 r = getr regs r.
Proof.
  intros regs regs2 HAP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HAP. unfold acallee_saved.
  unfold ne_saved_regs in Hr; cbn [In] in Hr.
  repeat (destruct Hr as [<-|Hr];
    [match goal with |- context [bv_unsigned ?q] =>
       let x := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with x end; lia |]).
  destruct Hr.
Qed.

(* presence growth as the restricted memories' growth *)
Lemma ne_grows_of_present : forall (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
  intros H m m' HP x Hx. unfold mrestrict in *. destruct (H x) eqn:Hh; [exact Hx|].
  destruct (m x) as [b|] eqn:Hm; [|exfalso; apply Hx; reflexivity].
  assert (Hp : apresent H m (bv_unsigned x)).
  { unfold apresent. rewrite Z_to_bv_bv_unsigned, Hh. split; [reflexivity | exists b; exact Hm]. }
  destruct (HP _ Hp) as [_ (b' & Hb')]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

(* THE CALL STEP: a join after a checked call (checked_memset / checked_memcpy at the realigned sp) whose
   destination [d, d + len) is in w's buffer b or in F's body: everything the join holds stays. *)
Lemma ne_call_after : forall cx pos S3 memA regsT memT mdT n f sh regs2 mem2 md2 d len,
  ne_base SK B cx -> ne_fctx B cx pos S3 memA -> ne_j SK B cx pos S3 memA regsT memT mdT n f sh ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((1, pos) :: n_own cx) (n_lyc cx) S3 (n_W cx) mem2 md2 (n_k cx) ->
  same_but_materialized mdT md2 -> aregs_preserved regsT regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + len) -> ~ (spZ regsT - ESTACK <= a < spZ regsT) ->
     aview SEGS (w_H (n_W cx)) mem2 a = aview SEGS (w_H (n_W cx)) memT a) ->
  (forall a, apresent (w_H (n_W cx)) memT a -> apresent (w_H (n_W cx)) mem2 a) ->
  ((ne_w cx <= d /\ d + len <= ne_w cx + 4096) \/ (ne_F cx pos + 32 <= d /\ d + len <= ne_F cx pos + 120)) ->
  ne_j SK B cx pos S3 memA regs2 mem2 md2 n f sh.
Proof.
  intros cx pos S3 memA regsT memT mdT n f sh regs2 mem2 md2 d len HB HF HJ HJ2 Hsbm HAP UN2 HP2 Hd.
  pose proof (ne_base_facts cx HB) as (Hw0 & Hw47 & Hwapp & _ & Hceil & Hsp47 & _ & _ & Hap & _ & _ & _ & Hs1r & _).
  pose proof HF as (_ & _ & _ & HF4096 & HF64 & HFceil & HFapp & HFL & HwF & _).
  pose proof HJ as (_ & _ & _ & R2 & _ & _ & _ & _ & _ & _ & _ & HNW & _ & _ & _ & _ & _ & Hshl & Hsh & _).
  pose proof HNW as (_ & _ & _ & Hnv & Hfv & Hnr & Hfr). unfold NL_CHUNK_MAX in *.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (Hsp : spZ regsT = ne_sp1 cx).
  { unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. unfold NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia. }
  destruct (same_but_materialized_fs _ _ Hsbm) as [Hfds Hfs].
  (* a byte outside the destination and the window keeps its view and its mbyte *)
  assert (HFsh : ne_Fsh cx pos = SHADOW_OFF + ne_F cx pos / 8) by reflexivity.
  assert (HF8 : 0 <= ne_F cx pos / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (UNX : forall a, 0 <= a < 2 ^ 64 -> ~ ne_X cx pos a ->
            aview SEGS (w_H (n_W cx)) mem2 a = aview SEGS (w_H (n_W cx)) memT a).
  { intros a Ha HX. apply UN2; [exact Ha | | rewrite Hsp]; intros Hin; apply HX; unfold ne_X;
      rewrite HFsh; unfold NW_SIZE, ESTACK in *; lia. }
  (* bytes outside the destination (but maybe in ne_X) that the join reads *)
  assert (UNd : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + len) -> ~ (ne_sp1 cx - ESTACK <= a < ne_sp1 cx) ->
            mbyte SEGS (rdW (n_W cx) mem2) a = mbyte SEGS (rdW (n_W cx) memT) a).
  { intros a Ha H1 H2. apply (mbyte_of_aview SEGS). apply UN2; [exact Ha | exact H1 | rewrite Hsp; exact H2]. }
  apply (ne_j_step cx pos S3 memA regsT memT mdT n f sh regs2 mem2 md2 n f sh HB HF HJ HJ2).
  - exact Hfds.
  - exact Hfs.
  - exact UNX.
  - exact (ne_grows_of_present _ _ _ HP2).
  - apply Forall_forall. intros r Hr.
    rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HAP. unfold acallee_saved.
    unfold ne_common_regs in Hr; cbn [In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [match goal with |- context [bv_unsigned ?q] =>
         let x := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with x end; lia |]).
    destruct Hr.
  - intros k Hk. rewrite UNd; [exact (Hnv k Hk) | | |]; unfold NW_SIZE, NW_N, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *;
      lia.
  - intros k Hk. rewrite UNd; [exact (Hfv k Hk) | | |]; unfold NW_SIZE, NW_FULL, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia.
  - unfold NL_CHUNK_MAX; lia.
  - exact Hfr.
  - pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFLv & _).
    intros k Hk. rewrite UNd; [exact (HFLv k Hk) | | |]; unfold NW_SIZE, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *; lia.
  - exact Hshl.
  - intros i Hi. rewrite UN2; [exact (Hsh i Hi) | | |].
    + unfold SHADOW_OFF in HFsh. lia.
    + intros Hin. rewrite HFsh in Hin. unfold NW_SIZE, ESTACK, SHADOW_OFF, kLowShadowBeg in *.
      rewrite C3 in *. lia.
    + rewrite Hsp. intros Hin. rewrite HFsh in Hin.
      unfold SHADOW_OFF, NL_ERROR_AK, NL_ERROR_AFRAME, ESTACK in *. lia.
Qed.
End b.
End a.

(* ==========================================================================
   7. TACTICS for the phases (every computation on a closed term: vm_compute never meets an evar)
   ========================================================================== *)

(* a register of a run's end state, read through ne_reg_after: leaves the goal `sv_denot E e = v` *)
Ltac ne_reg HS r :=
  let T := type of HS in
  let T' := eval unfold st_ok_pi in T in
  lazymatch T' with
  | st_ok _ _ ?s1 _ =>
      let e := eval vm_compute in (sr_get (ss_regs s1) r) in
      eapply (ne_reg_after _ _ _ _ _ r e _ HS (YP06.env_agree_refl _ _));
        [vm_compute; reflexivity | vm_compute; reflexivity | ]
  end.

(* the join after a run: ne_after at the run's end state, its four computed checks closed by vm_compute;
   leaves the two shadow goals (wsh = false -> sh' = sh, wsh = true -> ...) *)
Ltac ne_after_run SK B cx pos S3 memA regs3 mem3 md3 n f o upd wsh xr xc HB HFc HJ HX HS0 HS HJX HFr HG
    n' f' en ef Hen Hef Hn' Hf' :=
  let T := type of HS in
  let T' := eval unfold st_ok_pi in T in
  lazymatch T' with
  | st_ok _ ?E' ?s1 (restrict _ ?ms1) =>
  lazymatch type of HJX with
  | ajournal_gx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?md4 _ =>
      refine (ne_after SK B cx pos S3 memA regs3 mem3 md3 n f _ o upd wsh xr xc E' s1 ms1 md4 n' f' _ HB HFc HJ HX HS0
        (YP06.env_agree_refl _ _) HS ltac:(vm_compute; reflexivity) HJX (proj1 (wvb_fds_fs _ _ _))
        (proj2 (wvb_fds_fs _ _ _)) HFr HG en ef ltac:(vm_compute; reflexivity) Hen ltac:(vm_compute; reflexivity) Hef
        ltac:(vm_compute; reflexivity) Hn' Hf' _ _)
  end end.
