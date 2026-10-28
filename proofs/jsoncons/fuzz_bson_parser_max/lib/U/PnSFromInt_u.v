(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     AxSymExec3 PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnDigitFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSFromIntP_u Bs0_code_38684_38688_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSFI.
Import PMS.
Local Ltac lia := PMK.alia.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Definition CSR : list nat := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma sub_in (KS l : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) l = true -> forall k, In k l -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
Lemma csr_cs : forall k, In k CSR -> In k PMK.cs_all. Proof. apply sub_in. vm_compute. reflexivity. Qed.

Lemma to_bv_neg a : Z_to_bv 64 (- a) = Z_to_bv 64 (2 ^ 64 - a).
Proof.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  replace (2 ^ 64 - a) with (- a + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma wrap1 a : 2 ^ 64 <= a < 2 ^ 65 -> a mod 2 ^ 64 = a - 2 ^ 64.
Proof. intros Ha. replace a with ((a - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. Qed.

Lemma to_bv_mod a : Z_to_bv 64 (a mod 2 ^ 64) = Z_to_bv 64 a.
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Lemma callee_ag LBc sp' scr' W' M M' : L5C.hpres L LBc sp' scr' W' M M' -> L5C.stk (hl_sptop L) M sp' scr' -> 0 <= scr' ->
  forall a, sp' <= a < 2 ^ 64 -> ~ PMK.inW W' a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Proof.
  intros HP STK S0 a Ha N. apply (L5C.hpres_kept L LBc sp' scr' W' M M' a HP).
  apply (PMKP.kept_stack RSEGS L KL LBc M sp' scr' W' a STK S0 Ha). apply PMFR.outside_of_not_inW. exact N.
Qed.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model : Model) (K : TSet) (LB : list (Z * Z)) (cr : credit) (o v S r n0 : Z).
Hypothesis MOK : PMSP.model_ok model.
Hypothesis K0 : K [].
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).
Hypothesis STK0 : L5C.stk (hl_sptop L) M0 S 16384.
Hypothesis A10 : getr R0 (reg 10) = Z_to_bv 64 v.
Hypothesis Hv : - 2 ^ 31 <= v < 2 ^ 31.
Hypothesis A11 : getr R0 (reg 11) = Z_to_bv 64 o.
Hypothesis Ho1 : S <= o.
Hypothesis Ho2 : o + 24 <= hl_sptop L.
Hypothesis Ho3 : o mod 8 = 0.
Hypothesis Hn0 : 0 <= n0 <= 11.
Hypothesis BRLB : PMFR.brange L LB.
Hypothesis PBS : PNRS.str_push_back_short_spec L HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (n' : Z),
  regs_preserved R0 R' -> PM.vstr_at RSEGS PMSP.T3 M' o (PM.VShort n') -> n0 + 1 <= n' <= n0 + 11 ->
  L5C.hpres L LB S (PMSP.pm_scr 2) [(o, 24)] M0 M' -> hi_heap HI LB cr M' (m_vmmaps model) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model) K.

Let u8 := bv_unsigned (getr R0 (reg 8)).
Let u9 := bv_unsigned (getr R0 (reg 9)).
Let u18 := bv_unsigned (getr R0 (reg 18)).
Let u19 := bv_unsigned (getr R0 (reg 19)).
(* [comment removed for export] *)
Definition saves (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) r /\ L5.u64_at RSEGS M (S - 16) u8 /\ L5.u64_at RSEGS M (S - 24) u9 /\ L5.u64_at RSEGS M (S - 32) u18 /\ L5.u64_at RSEGS M (S - 40) u19.
(* [comment removed for export] *)
Definition KD : list nat := [2; 3; 4; 8; 10; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
(* [comment removed for export] *)
Definition VV (k x t j : Z) (i : nat) : Z :=
  match i with 2%nat => S | 8%nat => u8 | 9%nat => u9 | 18%nat => u18 | 19%nat => u19 | 33%nat => o | 34%nat => v mod 2 ^ 64 | 35%nat => k | 36%nat => x
  | 39%nat => t | 40%nat => j | 44%nat => r | 45%nat => u8 | 46%nat => u9 | 47%nat => u18 | 48%nat => u19 | _ => 0 end.

Lemma facts0 : 0 <= r < 2 ^ 47 /\ 0 <= u8 < 2 ^ 64 /\ 0 <= u9 < 2 ^ 64 /\ 0 <= u18 < 2 ^ 64 /\ 0 <= u19 < 2 ^ 64 /\ S mod 16 = 0
  /\ 0x7fff7f800000 + 16384 <= S /\ S <= hl_sptop L /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof.
  pose proof RAok as (Hr1 & Hr2). pose proof STK0 as (A16 & SLO & SHI & STOP & SDEF). pose proof (L5C.stk_floor _ M0 S 16384 STK0) as FL.
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 8))) as X8. pose proof (bv_unsigned_in_range _ (getr R0 (reg 9))) as X9.
  pose proof (bv_unsigned_in_range _ (getr R0 (reg 18))) as X18. pose proof (bv_unsigned_in_range _ (getr R0 (reg 19))) as X19.
  unfold bv_modulus in X8, X9, X18, X19. subst u8 u9 u18 u19. unfold L5.ra_ok in *.
  repeat split; clear KONT PBS BRLB; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_loop (m : nat) : forall (fx : FPState) R M x k,
  getr R (reg 2) = Z_to_bv 64 (S - 320) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 18) = Z_to_bv 64 k ->
  getr R (reg 11) = Z_to_bv 64 (S - 295) -> getr R (reg 12) = Z_to_bv 64 10 -> getr R (reg 13) = Z_to_bv 64 14757395259826634752 ->
  getr R (reg 14) = Z_to_bv 64 254 -> getr R (reg 16) = Z_to_bv 64 x ->
  L5.writable RSEGS M (S - 320) 320 -> saves M ->
  0 <= x < 10 ^ Z.of_nat m -> x < 2 ^ 31 -> 0 <= k -> k + Z.of_nat m <= 10 -> (1 <= m)%nat ->
  exists (fx' : FPState) R' M' d, msteps RSEGS (st fx R 0x39a70 M) (st fx' R' 0x39afc M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 320 <= a < S - 320 + 320) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ k + 1 <= d <= k + Z.of_nat m /\ getr R' (reg 18) = Z_to_bv 64 d
    /\ (forall i, In i KD -> getr R' (reg i) = getr R (reg i)) /\ saves M'.
Proof.
  induction m as [|m IH]; intros fx R M x k G2 G8 G18 G11 G12 G13 G14 G16 WR SV Hx Hx31 Hk Hkm Hm; [exfalso; clear -Hm; lia|].
  pose proof facts0 as (Fr & F8 & F9 & F18 & F19 & F16 & Flo & Fhi & Ftop).
  destruct SV as (S1 & S2 & S3 & S4 & S5).
  (let T := type of (PNSFIP.fgPL_conc fx R M (VV k x 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgPL_conc fx R M (VV k x 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & _ & _ & B15 & B16 & B17 & B18 & _ & T1 & T2 & T3 & T4 & T5)); PMK.pvz_clrT.
  rewrite (PNDG.quot_pos x) in B16 by (clear -Hx Hx31; lia).
  assert (A16 : getr R1 (reg 16) = Z_to_bv 64 (x / 10)).
  { rewrite <- B16. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (WR1 : L5.writable RSEGS M1 (S - 320) 320) by (apply (L5.writable_grows RSEGS M M1 _ _ MG1 WR)).
  assert (Hq : 0 <= x / 10 < 2 ^ 64) by (split; [apply Z.div_pos| apply Z.div_lt_upper_bound]; clear -Hx Hx31; lia).
  (let T := type of (PNSFIP.fgPM_conc fx1 R1 M1 (fun i => match i with 41%nat => x / 10 | _ => VV k x 0 0 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgPM_conc fx1 R1 M1 (fun i => match i with 41%nat => x / 10 | _ => VV k x 0 0 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx2 & R2 & M2 & MG2 & FR2 & _ & EX).
  assert (EM : M2 = M1) by (apply functional_extensionality; exact FR2). subst M2.
  destruct EX as [(MS2 & KS2 & GE10)|(MS2 & KS2 & LT10)].
  - (* [comment removed for export] *)
    assert (Hm2 : (2 <= m)%nat -> True) by (intros; exact I).
    assert (Hx' : 0 <= x / 10 < 10 ^ Z.of_nat m).
    { split; [apply Z.div_pos; clear -Hx; lia|]. apply Z.div_lt_upper_bound; [clear; lia|].
      replace (10 * 10 ^ Z.of_nat m) with (10 ^ Z.of_nat (Datatypes.S m)); [clear -Hx; lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; lia). reflexivity. }
    assert (Hm1 : (1 <= m)%nat).
    { destruct m; [|clear; lia]. exfalso. cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Hx'. clear -Hx' GE10 Hx. 
      assert (x < 10) by (apply (Z.div_lt_upper_bound x 10 1) in GE10 || idtac; pose proof (Z.div_mod x 10 ltac:(lia)); pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia). lia. }
    destruct (IH fx2 R2 M1 (x / 10) (k + 1)) as (fx3 & R3 & M3 & d & MS3 & MG3 & FRZ3 & Hd & D9 & KS3 & SV3).
    { rewrite (KS2 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact G2. }
    { rewrite (KS2 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact G8. }
    { rewrite (KS2 18%nat) by PMK.inl. exact B18. }
    { rewrite (KS2 11%nat) by PMK.inl. rewrite (KS1 11%nat) by PMK.inl. exact G11. }
    { rewrite (KS2 12%nat) by PMK.inl. rewrite (KS1 12%nat) by PMK.inl. exact G12. }
    { rewrite (KS2 13%nat) by PMK.inl. rewrite (KS1 13%nat) by PMK.inl. exact G13. }
    { rewrite (KS2 14%nat) by PMK.inl. rewrite (KS1 14%nat) by PMK.inl. exact G14. }
    { rewrite (KS2 16%nat) by PMK.inl. exact A16. }
    { exact WR1. }
    { split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4| exact T5]. }
    { exact Hx'. }
    { clear -Hq Hx31 Hx. apply Z.div_lt_upper_bound; lia. }
    { clear -Hk; lia. }
    { rewrite Nat2Z.inj_succ in Hkm. clear -Hkm. lia. }
    { exact Hm1. }
    exists fx3, R3, M3, d. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    split; [intros a Ha; apply MG3; apply MG1; exact Ha|].
    split; [intros a Ha Na; rewrite (FRZ3 a Ha Na); apply (FRZ1 a Ha Na)|].
    split; [rewrite Nat2Z.inj_succ; clear -Hd; lia|]. split; [exact D9|].
    split; [|exact SV3]. intros i Hi. rewrite (KS3 i Hi). rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
  - (* [comment removed for export] *)
    exists fx2, R2, M1, (k + 1). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FRZ1|].
    split; [rewrite Nat2Z.inj_succ; clear; lia|]. split; [rewrite (KS2 18%nat) by PMK.inl; exact B18|].
    split; [| split; [exact T1|]; split; [exact T2|]; split; [exact T3|]; split; [exact T4| exact T5]].
    intros i Hi. rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma neg_loop (m : nat) : forall (fx : FPState) R M a k,
  getr R (reg 2) = Z_to_bv 64 (S - 320) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 18) = Z_to_bv 64 k ->
  getr R (reg 11) = Z_to_bv 64 (S - 295) -> getr R (reg 12) = Z_to_bv 64 10 -> getr R (reg 13) = Z_to_bv 64 (-20) ->
  getr R (reg 14) = Z_to_bv 64 1717986919 -> getr R (reg 15) = Z_to_bv 64 254 -> getr R (reg 17) = Z_to_bv 64 (2 ^ 64 - a) ->
  L5.writable RSEGS M (S - 320) 320 -> saves M ->
  1 <= a < 10 ^ Z.of_nat m -> a <= 2 ^ 31 -> 0 <= k -> k + Z.of_nat m <= 10 -> (1 <= m)%nat ->
  exists (fx' : FPState) R' M' d, msteps RSEGS (st fx R 0x39ac0 M) (st fx' R' 0x39afc M') /\ mem_grows M M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 320 <= a < S - 320 + 320) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))
    /\ k + 1 <= d <= k + Z.of_nat m /\ getr R' (reg 18) = Z_to_bv 64 d
    /\ (forall i, In i KD -> getr R' (reg i) = getr R (reg i)) /\ saves M'.
Proof.
  induction m as [|m IH]; intros fx R M a k G2 G8 G18 G11 G12 G13 G14 G15 G17 WR SV Ha Ha31 Hk Hkm Hm; [exfalso; clear -Hm; lia|].
  pose proof facts0 as (Fr & F8 & F9 & F18 & F19 & F16 & Flo & Fhi & Ftop).
  destruct SV as (S1 & S2 & S3 & S4 & S5).
  (let T := type of (PNSFIP.fgNL_conc fx R M (VV k (2 ^ 64 - a) 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgNL_conc fx R M (VV k (2 ^ 64 - a) 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP;
    destruct pvzP as (MG1 & _ & FRZ1 & MS1 & KS1 & B5 & B6 & _ & B16 & B17 & B18 & T1 & T2 & T3 & T4 & T5)); PMK.pvz_clrT.
  cbn [AX2.edenot AX2.ev alu64 alu32 alu mul_div] in B5, B17.
  rewrite (PNDG.quot_neg (Z_to_bv 64 (2 ^ 64 - a)) a ltac:(clear -Ha Ha31; lia) eq_refl) in B17.
  set (t0 := bv_unsigned (getr R1 (reg 5))).
  pose proof (PNDG.t0_neg (Z_to_bv 64 (2 ^ 64 - a)) a ltac:(clear -Ha Ha31; lia) eq_refl) as T0. rewrite <- B5 in T0. fold t0 in T0.
  assert (Ht0 : 0 <= t0 < 2 ^ 64) by (subst t0; apply bv_unsigned_in_range).
  assert (A5 : getr R1 (reg 5) = Z_to_bv 64 t0).
  { subst t0. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (WR1 : L5.writable RSEGS M1 (S - 320) 320) by (apply (L5.writable_grows RSEGS M M1 _ _ MG1 WR)).
  assert (Hq : 0 <= a / 10 /\ a / 10 < 214748365).
  { split; [apply Z.div_pos| apply Z.div_lt_upper_bound]; clear -Ha Ha31; lia. }
  (* [comment removed for export] *)
  idtac.
  pose proof (bv_unsigned_in_range _ (getr R1 (reg 7))) as U7. unfold bv_modulus in U7.
  pose proof (Z.mod_pos_bound (- (a / 10)) (2 ^ 64) ltac:(clear; lia)) as U41.
  (let T := type of (PNSFIP.fgNM_conc fx1 R1 M1 (fun i => match i with 41%nat => (- (a / 10)) mod 2 ^ 64 | 42%nat => bv_unsigned (getr R1 (reg 7)) | 43%nat => S + k - 295
                                                  | _ => VV k 0 t0 0 i end)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgNM_conc fx1 R1 M1 (fun i => match i with 41%nat => (- (a / 10)) mod 2 ^ 64 | 42%nat => bv_unsigned (getr R1 (reg 7)) | 43%nat => S + k - 295
                                                  | _ => VV k 0 t0 0 i end)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite B17, to_bv_mod; reflexivity
                         | symmetry; apply Z_to_bv_bv_unsigned | clear -U41; lia | clear -U7; lia | clear -Hk Hkm Flo Fhi Ftop; lia])).
  destruct P as (fx2 & R2 & M2 & MG2 & FR2 & _ & EX).
  assert (EM : M2 = M1) by (apply functional_extensionality; exact FR2). subst M2.
  destruct EX as [(MS2 & KS2 & LE)|(MS2 & KS2 & GT)].
  - (* [comment removed for export] *)
    assert (Ha10 : 10 <= a) by (destruct (Z_lt_le_dec a 10); [exfalso; clear -T0 LE l; apply proj1 in T0; specialize (T0 ltac:(lia)); lia| assumption]).
    assert (Ha' : 1 <= a / 10 < 10 ^ Z.of_nat m).
    { split; [apply Z.div_le_lower_bound; clear -Ha10; lia|]. apply Z.div_lt_upper_bound; [clear; lia|].
      replace (10 * 10 ^ Z.of_nat m) with (10 ^ Z.of_nat (Datatypes.S m)); [clear -Ha; lia|].
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by (clear; lia). reflexivity. }
    assert (Hm1 : (1 <= m)%nat).
    { destruct m; [|clear; lia]. exfalso. cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter Z.mul] in Ha'. clear -Ha' Ha10.
      pose proof (Z.div_le_lower_bound 10 10 1 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono 10 a 10 ltac:(lia) Ha10). lia. }
    destruct (IH fx2 R2 M1 (a / 10) (k + 1)) as (fx3 & R3 & M3 & d & MS3 & MG3 & FRZ3 & Hd & D9 & KS3 & SV3).
    { rewrite (KS2 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact G2. }
    { rewrite (KS2 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact G8. }
    { rewrite (KS2 18%nat) by PMK.inl. exact B18. }
    { rewrite (KS2 11%nat) by PMK.inl. rewrite (KS1 11%nat) by PMK.inl. exact G11. }
    { rewrite (KS2 12%nat) by PMK.inl. rewrite (KS1 12%nat) by PMK.inl. exact G12. }
    { rewrite (KS2 13%nat) by PMK.inl. rewrite (KS1 13%nat) by PMK.inl. exact G13. }
    { rewrite (KS2 14%nat) by PMK.inl. rewrite (KS1 14%nat) by PMK.inl. exact G14. }
    { rewrite (KS2 15%nat) by PMK.inl. rewrite (KS1 15%nat) by PMK.inl. exact G15. }
    { rewrite (KS2 17%nat) by PMK.inl. rewrite B17. apply to_bv_neg. }
    { exact WR1. }
    { split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4| exact T5]. }
    { exact Ha'. }
    { clear -Hq. lia. }
    { clear -Hk; lia. }
    { rewrite Nat2Z.inj_succ in Hkm. clear -Hkm. lia. }
    { exact Hm1. }
    exists fx3, R3, M3, d. split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MS2| exact MS3]]|].
    split; [intros b Hb; apply MG3; apply MG1; exact Hb|].
    split; [intros b Hb Nb; rewrite (FRZ3 b Hb Nb); apply (FRZ1 b Hb Nb)|].
    split; [rewrite Nat2Z.inj_succ; clear -Hd; lia|]. split; [exact D9|].
    split; [|exact SV3]. intros i Hi. rewrite (KS3 i Hi). rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
  - (* [comment removed for export] *)
    exists fx2, R2, M1, (k + 1). split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [exact MG1|]. split; [exact FRZ1|].
    split; [rewrite Nat2Z.inj_succ; clear; lia|]. split; [rewrite (KS2 18%nat) by PMK.inl; exact B18|].
    split; [| split; [exact T1|]; split; [exact T2|]; split; [exact T3|]; split; [exact T4| exact T5]].
    intros i Hi. rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma digits (fx : FPState) :
  exists (fx' : FPState) R' M' d, msteps RSEGS (st fx R0 0x39a24 M0) (st fx' R' 0x39afc M') /\ mem_grows M0 M'
    /\ (forall a, 0 <= a < 2 ^ 64 -> ~ (S - 320 <= a < S - 320 + 320) -> M' (Z_to_bv 64 a) = M0 (Z_to_bv 64 a))
    /\ 1 <= d <= 10 /\ getr R' (reg 18) = Z_to_bv 64 d /\ getr R' (reg 2) = Z_to_bv 64 (S - 320) /\ getr R' (reg 8) = Z_to_bv 64 o
    /\ getr R' (reg 10) = Z_to_bv 64 v /\ (forall i, In i CSR -> getr R' (reg i) = getr R0 (reg i)) /\ saves M'.
Proof.
  pose proof facts0 as (Fr & F8 & F9 & F18 & F19 & F16 & Flo & Fhi & Ftop).
  pose proof (L5C.stk_writable RSEGS _ M0 S 16384 STK0) as WR.
  assert (WR0 : L5.writable RSEGS M0 (S - 320) 320) by (apply (L5.writable_sub RSEGS M0 (S - 16384) 16384 (S - 320) 320 WR); clear; lia).
  assert (A10m : getr R0 (reg 10) = Z_to_bv 64 (v mod 2 ^ 64)) by (rewrite to_bv_mod; exact A10).
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(clear; lia)) as U34.
  assert (Ur : bv_unsigned (getr R0 (reg 1)) = r) by (rewrite Rra0; apply L5.unsigned_lit; clear -Fr; lia).
  (let T := type of (PNSFIP.fgA_conc fx R0 M0 (VV 0 0 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgA_conc fx R0 M0 (VV 0 0 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & EX).
  pose proof (PNDG.slt0 v ltac:(clear -Hv; lia)) as SLT.
  destruct EX as [(MS1 & KS1 & B2 & B8 & B11 & B12 & B13 & B14 & B16 & B18 & SGN & T5 & T4 & T3 & T2 & T1)
                 |(MS1 & KS1 & B2 & B8 & B11 & B12 & B13 & B14 & B15 & B17 & B18 & SGN & T5 & T4 & T3 & T2 & T1)];
    cbn [AX2.edenot AX2.ev] in SGN; rewrite to_bv_mod, SLT in SGN; rewrite Ur in T1; fold u8 in T2; fold u9 in T3; fold u18 in T4; fold u19 in T5.
  - (* [comment removed for export] *)
    assert (Hv0 : 0 <= v) by (destruct (Z.ltb_spec v 0); [exfalso; clear -SGN; lia| assumption]).
    rewrite (Z.mod_small v (2 ^ 64)) in B16 by (clear -Hv0 Hv; lia).
    destruct (pos_loop 10 fx1 R1 M1 v 0 B2 B8 B18 B11 B12 B13 B14 B16) as (fx2 & R2 & M2 & d & MS2 & MG2 & FRZ2 & Hd & D9 & KS2 & SV2).
    { apply (L5.writable_grows RSEGS M0 M1 _ _ MG1 WR0). }
    { split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4| exact T5]. }
    { change (10 ^ Z.of_nat 10) with (10 ^ 10). clear -Hv0 Hv. lia. } { clear -Hv; lia. } { clear; lia. } { clear; cbn; lia. } { clear; lia. }
    exists fx2, R2, M2, d. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
    split; [intros a Ha Na; rewrite (FRZ2 a Ha Na); apply (FRZ1 a Ha Na)|]. split; [clear -Hd; cbn in Hd; lia|]. split; [exact D9|].
    split; [rewrite (KS2 2%nat) by PMK.inl; exact B2|]. split; [rewrite (KS2 8%nat) by PMK.inl; exact B8|].
    split; [rewrite (KS2 10%nat) by PMK.inl; rewrite (KS1 10%nat) by PMK.inl; exact A10|].
    split; [|exact SV2]. intros i Hi. rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
  - (* [comment removed for export] *)
    assert (Hvn : v < 0) by (destruct (Z.ltb_spec v 0); [assumption| exfalso; clear -SGN; lia]).
    assert (E34 : v mod 2 ^ 64 = 2 ^ 64 - (- v)).
    { replace v with ((2 ^ 64 - - v) + (-1) * 2 ^ 64) at 1 by (clear; lia). rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -Hvn Hv. lia. }
    rewrite E34 in B17.
    destruct (neg_loop 10 fx1 R1 M1 (- v) 0 B2 B8 B18 B11 B12) as (fx2 & R2 & M2 & d & MS2 & MG2 & FRZ2 & Hd & D9 & KS2 & SV2).
    { rewrite B13. change 18446744073709551596 with ((-20) mod 2 ^ 64). apply to_bv_mod. } { exact B14. } { exact B15. } { exact B17. }
    { apply (L5.writable_grows RSEGS M0 M1 _ _ MG1 WR0). }
    { split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact T4| exact T5]. }
    { change (10 ^ Z.of_nat 10) with (10 ^ 10). clear -Hvn Hv. lia. } { clear -Hv; lia. } { clear; lia. } { clear; cbn; lia. } { clear; lia. }
    exists fx2, R2, M2, d. split; [eapply msteps_trans; [exact MS1| exact MS2]|]. split; [intros a Ha; apply MG2; apply MG1; exact Ha|].
    split; [intros a Ha Na; rewrite (FRZ2 a Ha Na); apply (FRZ1 a Ha Na)|]. split; [clear -Hd; cbn in Hd; lia|]. split; [exact D9|].
    split; [rewrite (KS2 2%nat) by PMK.inl; exact B2|]. split; [rewrite (KS2 8%nat) by PMK.inl; exact B8|].
    split; [rewrite (KS2 10%nat) by PMK.inl; rewrite (KS1 10%nat) by PMK.inl; exact A10|].
    split; [|exact SV2]. intros i Hi. rewrite (KS2 i); [apply KS1|]; revert i Hi; apply sub_in; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma push_round (fx : FPState) R M (j cnt n : Z) :
  hi_heap HI LB cr M (m_vmmaps model) ->
  getr R (reg 2) = Z_to_bv 64 (S - 320) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 cnt ->
  getr R (reg 18) = Z_to_bv 64 (S - 295 + j) -> getr R (reg 19) = Z_to_bv 64 (S - 295) ->
  (forall i, In i CSR -> getr R (reg i) = getr R0 (reg i)) ->
  PMK.ek L LB S 16384 [(o, 24)] M0 M -> PMK.dk L LB S 16384 M0 M -> L5C.stk (hl_sptop L) M S 16384 -> saves M ->
  PM.vstr_at RSEGS PMSP.T3 M o (PM.VShort n) -> n <= 21 -> 0 <= j <= 10 -> 0 <= cnt < 2 ^ 64 ->
  (forall (fx2 : FPState) R2 M2, hi_heap HI LB cr M2 (m_vmmaps model) ->
     getr R2 (reg 2) = Z_to_bv 64 (S - 320) -> getr R2 (reg 8) = Z_to_bv 64 o -> getr R2 (reg 9) = Z_to_bv 64 cnt ->
     getr R2 (reg 18) = Z_to_bv 64 (S - 295 + j) -> getr R2 (reg 19) = Z_to_bv 64 (S - 295) ->
     (forall i, In i CSR -> getr R2 (reg i) = getr R0 (reg i)) ->
     PMK.ek L LB S 16384 [(o, 24)] M0 M2 -> PMK.dk L LB S 16384 M0 M2 -> L5C.stk (hl_sptop L) M2 S 16384 -> saves M2 ->
     PM.vstr_at RSEGS PMSP.T3 M2 o (PM.VShort (n + 1)) ->
     srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx2 R2 0x39b48 M2 model) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39b3c M model) K.
Proof.
  intros HH G2 G8 G9 G18 G19 CS EK DK STK SV VS Hn Hj Hcnt Q.
  pose proof facts0 as (Fr & F8 & F9 & F18 & F19 & F16 & Flo & Fhi & Ftop). pose proof MOK as (Mh & Ml & Mm).
  destruct SV as (S1 & S2 & S3 & S4 & S5).
  pose proof (L5C.stk_writable RSEGS _ M S 16384 STK) as WR.
  assert (WRf : L5.writable RSEGS M (S - 320) 320) by (apply (L5.writable_sub RSEGS M (S - 16384) 16384 (S - 320) 320 WR); clear; lia).
  (let T := type of (PNSFIP.fgQB_conc fx R M (VV 0 0 0 j)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgQB_conc fx R M (VV 0 0 0 j)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & KS1 & B1 & B10).
  assert (EM : M1 = M) by (apply functional_extensionality; exact FR1). subst M1.
  unfold PMSP.cfg. apply (PMK.spiece_ro RSEGS model fx fx1 R 0x39b3c R1 0x58938 M K Mh Ml MS1).
  assert (STKc : L5C.stk (hl_sptop L) M (S - 320) 14336).
  { apply (PMK.stk_call L M S 16384 (S - 320) 14336 STK); clear -F16; lia. }
  unfold PNRS.str_push_back_short_spec, PNR.str_push_back_short_spec in PBS. cbn [PNL.pn_str_push_back PnLayoutS_u.NADDR_S] in PBS.
  apply (PBS fx1 R1 M model K LB cr o (S - 320) 0x39b48 n HH MOK K0).
  { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [clear; unfold L5.ra_ok; lia|].
    split; [rewrite (KS1 2%nat) by PMK.inl; exact G2|]. split; [rewrite (KS1 3%nat) by PMK.inl; rewrite (CS 3%nat) by PMK.inl; exact Rgp0|].
    split; [rewrite (KS1 4%nat) by PMK.inl; rewrite (CS 4%nat) by PMK.inl; exact Rtp0|]. exact STKc. }
  { rewrite L5K.rl10. exact B10. } { clear -Ho1; lia. } { exact Ho2. } { exact Ho3. } { exact VS. } { exact Hn. }
  intros fx2 R2 M2 RP2 VS2 HP2 HH2. change (PMSP.pm_scr 1) with 14336 in HP2.
  pose proof (callee_ag LB (S - 320) 14336 [(o, 24)] M M2 HP2 STKc ltac:(clear; lia)) as AG2.
  assert (NW : forall a, a < S -> ~ PMK.inW [(o, 24)] a).
  { intros a Ha (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear -Ha Hr Ho1. lia. }
  assert (R12 : forall i, In i PMK.cs_all -> getr R2 (reg i) = getr R1 (reg i)) by (intros i Hi; apply (PMK.cs_of_preserved R1 R2 i RP2 Hi)).
  apply (Q fx2 R2 M2 HH2).
  - rewrite (R12 2%nat) by PMK.inl. rewrite (KS1 2%nat) by PMK.inl. exact G2.
  - rewrite (R12 8%nat) by PMK.inl. rewrite (KS1 8%nat) by PMK.inl. exact G8.
  - rewrite (R12 9%nat) by PMK.inl. rewrite (KS1 9%nat) by PMK.inl. exact G9.
  - rewrite (R12 18%nat) by PMK.inl. rewrite (KS1 18%nat) by PMK.inl. exact G18.
  - rewrite (R12 19%nat) by PMK.inl. rewrite (KS1 19%nat) by PMK.inl. exact G19.
  - intros i Hi. rewrite (R12 i) by (apply csr_cs; exact Hi). rewrite (KS1 i); [apply CS; exact Hi|]. revert i Hi. apply sub_in. vm_compute. reflexivity.
  - apply (PMK.ek_trans L LB S 16384 [(o, 24)] M0 M M2 EK).
    apply (PMK.ek_callee_in RSEGS L KL LB LB S 16384 (S - 320) 14336 [(o, 24)] [(o, 24)] M M M2 HP2 (incl_refl _)); [clear; lia| clear; lia| exact STK| exact (PMFR.brange_hi L LB BRLB)|].
    intros a Ha. right. exact Ha.
  - apply (PMK.dk_trans L LB S 16384 M0 M M2 DK). apply (PMK.dk_callee L LB LB S 16384 (S - 320) 14336 [(o, 24)] M M2 HP2 (incl_refl _)); clear; lia.
  - apply (PMK.stk_after RSEGS L KL LB M M2 S 16384 (S - 320) 14336 [(o, 24)] STK HP2); clear; lia.
  - split; [|split; [|split; [|split]]];
      (apply (L5C.u64_at_agree RSEGS M); [intros i Hi; apply AG2; [clear -Hi Fhi Ftop; lia| apply NW; clear -Hi; lia] | clear -Flo; lia | clear -Fhi Ftop; lia | assumption]).
  - exact VS2.
Qed.

(* [comment removed for export] *)
Lemma push_loop (jn : nat) : forall (fx : FPState) R M (j cnt n : Z),
  j = Z.of_nat jn -> hi_heap HI LB cr M (m_vmmaps model) ->
  getr R (reg 2) = Z_to_bv 64 (S - 320) -> getr R (reg 8) = Z_to_bv 64 o -> getr R (reg 9) = Z_to_bv 64 cnt ->
  getr R (reg 18) = Z_to_bv 64 (S - 295 + j) -> getr R (reg 19) = Z_to_bv 64 (S - 295) ->
  (forall i, In i CSR -> getr R (reg i) = getr R0 (reg i)) ->
  PMK.ek L LB S 16384 [(o, 24)] M0 M -> PMK.dk L LB S 16384 M0 M -> L5C.stk (hl_sptop L) M S 16384 -> saves M ->
  PM.vstr_at RSEGS PMSP.T3 M o (PM.VShort n) -> 0 <= n -> n + j + 1 <= 22 -> j <= 10 -> n0 <= n -> n + j + 1 <= n0 + 11 -> 0 <= cnt < 2 ^ 64 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x39b3c M model) K.
Proof.
  induction jn as [|jn IH]; intros fx R M j cnt n Ej HH G2 G8 G9 G18 G19 CS EK DK STK SV VS Hn Hnj Hj Hn0n Hnj2 Hcnt;
    pose proof facts0 as (Fr & F8 & F9 & F18 & F19 & F16 & Flo & Fhi & Ftop); pose proof MOK as (Mh & Ml & Mm);
    apply (push_round fx R M j cnt n HH G2 G8 G9 G18 G19 CS EK DK STK SV VS ltac:(clear -Hnj Ej; lia) ltac:(clear -Ej Hj; lia) Hcnt);
    intros fx2 R2 M2 HH2 E2 E8 E9 E18 E19 CS2 EK2 DK2 STK2 SV2 VS2;
    pose proof SV2 as (S1 & S2 & S3 & S4 & S5);
    pose proof (L5C.stk_writable RSEGS _ M2 S 16384 STK2) as WR2;
    assert (WRf : L5.writable RSEGS M2 (S - 320) 320) by (apply (L5.writable_sub RSEGS M2 (S - 16384) 16384 (S - 320) 320 WR2); clear; lia);
    pose proof (PNSFIP.fgQR_conc fx2 R2 M2 (VV cnt 0 0 j)) as P; cbn beta iota delta [VV] in P;
    PMK.feed P ltac:(first [PMK.sc]);
    destruct P as (fx3 & R3 & M3 & MG3 & FR3 & _ & EX);
    (assert (EM : M3 = M2) by (apply functional_extensionality; exact FR3)); subst M3; unfold PMSP.cfg.
  - (* [comment removed for export] *)
    destruct EX as [(MS3 & KS3 & _ & CT)|(MS3 & KS3 & B1 & B2 & B8 & B9 & B10 & B18 & B19 & _)].
    { exfalso. subst j. rewrite Z.add_0_r, (Z.mod_small S) in CT by (clear -Flo Fhi Ftop; lia). clear -CT Flo Fhi Ftop. rewrite !wrap1 in CT by lia. lia. }
    assert (Ur : 0 <= r < 2 ^ 64) by (clear -Fr; lia).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { eapply msteps_trans; [exact MS3|]. pose proof RAok as (Hr1 & Hr2). apply (PMK.ret_to RSEGS fx3 R3 M2 0x39b70 W_38728 r F_38728 ltac:(reflexivity) D_38728 B1 Hr1 Hr2). }
    apply (KONT fx3 R3 M2 (n + 1)).
    + apply PMK.preserved_by_index. intros i Hi. unfold PMK.cs_all in Hi.
      destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|Hc]]]]]]].
      * rewrite B2. symmetry. exact Rsp0.
      * rewrite (KS3 3%nat) by PMK.inl. apply CS2. PMK.inl.
      * rewrite (KS3 4%nat) by PMK.inl. apply CS2. PMK.inl.
      * rewrite B8. unfold u8. apply Z_to_bv_bv_unsigned.
      * rewrite B9. unfold u9. apply Z_to_bv_bv_unsigned.
      * rewrite B18. unfold u18. apply Z_to_bv_bv_unsigned.
      * rewrite B19. unfold u19. apply Z_to_bv_bv_unsigned.
      * assert (Hc' : In i CSR) by (revert Hc; apply (sub_in CSR); vm_compute; reflexivity).
        rewrite (KS3 i); [apply CS2; exact Hc'|]. revert Hc'. apply (sub_in PNSFIP.KS_fgQR_1 CSR). vm_compute. reflexivity.
    + exact VS2.
    + subst j. clear -Hn0n Hnj2. lia.
    + change (PMSP.pm_scr 2) with 16384. apply (PMK.hpres_of L LB S 16384 [(o, 24)] M0 M2 EK2); [|exact DK2]. destruct STK2 as (_ & _ & _ & _ & D). exact D.
    + exact HH2.
  - (* [comment removed for export] *)
    destruct EX as [(MS3 & KS3 & B18 & _)|(MS3 & KS3 & _ & _ & _ & _ & _ & _ & _ & CT)].
    2: { exfalso. rewrite (Z.mod_small (S + j)) in CT by (clear -Flo Fhi Ftop Ej Hj; lia). clear -CT Flo Fhi Ftop Ej Hj. rewrite !wrap1 in CT by lia. lia. }
    apply (PMK.spiece_ro RSEGS model fx3 fx3 R3 0x39b3c R3 0x39b3c M2 K Mh Ml ltac:(apply msteps_refl)) || idtac.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS3|].
    apply (IH fx3 R3 M2 (Z.of_nat jn) cnt (n + 1) eq_refl HH2).
    * rewrite (KS3 2%nat) by PMK.inl. exact E2.
    * rewrite (KS3 8%nat) by PMK.inl. exact E8.
    * rewrite (KS3 9%nat) by PMK.inl. exact E9.
    * rewrite B18. f_equal. clear -Ej. lia.
    * rewrite (KS3 19%nat) by PMK.inl. exact E19.
    * intros i Hi. rewrite (KS3 i); [apply CS2; exact Hi|]. revert i Hi. apply sub_in. vm_compute. reflexivity.
    * exact EK2. * exact DK2. * exact STK2. * exact SV2. * exact VS2.
    * clear -Hn; lia. * clear -Hnj Ej; lia. * clear -Hj Ej; lia. * clear -Hn0n; lia. * clear -Hnj2 Ej; lia. * exact Hcnt.
Qed.

(* [comment removed for export] *)
Lemma call (fx : FPState) :
  hi_heap HI LB cr M0 (m_vmmaps model) -> PM.vstr_at RSEGS PMSP.T3 M0 o (PM.VShort n0) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0x39a24 M0 model) K.
Proof.
  intros HH VS0. pose proof facts0 as (Fr & F8 & F9 & F18 & F19 & F16 & Flo & Fhi & Ftop). pose proof MOK as (Mh & Ml & Mm).
  destruct (digits fx) as (fx1 & R1 & M1 & d & MS1 & MG1 & FRZ1 & Hd & D18 & B2 & B8 & B10 & CS1 & SV1).
  pose proof SV1 as (S1 & S2 & S3 & S4 & S5).
  assert (WRf : L5.writable RSEGS M1 (S - 320) 320).
  { apply (L5.writable_grows RSEGS M0 M1 _ _ MG1). apply (L5.writable_sub RSEGS M0 (S - 16384) 16384 (S - 320) 320 (L5C.stk_writable RSEGS _ M0 S 16384 STK0)); clear; lia. }
  assert (A10m : getr R1 (reg 10) = Z_to_bv 64 (v mod 2 ^ 64)) by (rewrite to_bv_mod; exact B10).
  pose proof (Z.mod_pos_bound v (2 ^ 64) ltac:(clear; lia)) as U34.
  (let T := type of (PNSFIP.fgD_conc fx1 R1 M1 (VV d 0 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at P (PNSFIP.fgD_conc fx1 R1 M1 (VV d 0 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc])).
  destruct P as (fx2 & R2 & M2 & MG2 & FR2 & _ & EX).
  assert (EM : M2 = M1) by (apply functional_extensionality; exact FR2). subst M2.
  pose proof (PNDG.slt0 v ltac:(clear -Hv; lia)) as SLT.
  (* [comment removed for export] *)
  set (P := fun a => S - 320 <= a < S - 320 + 320).
  assert (CW : forall a, P a -> PMK.cwr L LB a) by (intros a Pa; unfold P in Pa; apply (PMK.cwr_stack L LB M0 S 16384 a STK0); clear -Pa Fhi; lia).
  assert (DEC : forall a, {P a} + {~ P a}) by (intros a; unfold P; apply PMK.rng_dec).
  assert (STK1 : L5C.stk (hl_sptop L) M1 S 16384) by (apply (PMK.stk_grows L M0 M1 S 16384 MG1 STK0)).
  assert (EK1 : PMK.ek L LB S 16384 [(o, 24)] M0 M1).
  { apply (PMK.ek_piece_in RSEGS L KL LB S 16384 [(o, 24)] M0 M1 P FRZ1 STK0 (PMFR.brange_hi L LB BRLB)). intros a Pa. left. unfold P in Pa. clear -Pa. lia. }
  assert (DK1 : PMK.dk L LB S 16384 M0 M1) by (apply PMK.dk_grows; exact MG1).
  assert (VS1 : PM.vstr_at RSEGS PMSP.T3 M1 o (PM.VShort n0)).
  { apply (PMF.vstr_at_agree RSEGS M0 M1 o (PM.VShort n0)); [clear -Ho1 Flo; lia| clear -Ho2 Ftop; lia| | intros c n p E; discriminate E| exact VS0].
    intros i Hi. apply FRZ1; [clear -Hi Ho1 Ho2 Flo Ftop; lia| unfold P; clear -Hi Ho1; lia]. }
  destruct EX as [(MS2 & KS2 & B9 & _ & _ & B18 & B19 & SGN)|(MS2 & KS2 & B1 & B9 & B10' & B11 & B19 & SGN)];
    cbn [AX2.edenot AX2.ev] in SGN; rewrite to_bv_mod, SLT in SGN.
  - (* [comment removed for export] *)
    assert (Hv0 : 0 <= v) by (destruct (Z.ltb_spec v 0); [exfalso; clear -SGN; lia| assumption]).
    unfold PMSP.cfg. apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model fx fx2 R0 0x39a24 R2 0x39b3c M1 P K HH Mh Ml ltac:(clear -Ftop; lia)
             ltac:(eapply msteps_trans; [exact MS1| exact MS2]) MG1 FRZ1 CW DEC).
    intros HH1.
    apply (push_loop (Z.to_nat (d - 1)) fx2 R2 M1 (d - 1) d n0); [clear -Hd; lia| exact HH1| ..].
    + rewrite (KS2 2%nat) by PMK.inl. exact B2.
    + rewrite (KS2 8%nat) by PMK.inl. exact B8.
    + exact B9.
    + rewrite B18. f_equal. clear. lia.
    + exact B19.
    + intros i Hi. rewrite (KS2 i); [apply CS1; exact Hi|]. revert i Hi. apply sub_in. vm_compute. reflexivity.
    + exact EK1. + exact DK1. + exact STK1. + exact SV1. + exact VS1.
    + clear -Hn0; lia. + destruct VS1 as (_ & _ & Hn & _). clear -Hn0 Hd; lia. + clear -Hd; lia. + clear; lia. + clear -Hd; lia. + clear -Hd; lia.
  - (* [comment removed for export] *)
    unfold PMSP.cfg. apply (PMK.spiece RSEGS L HI KL HIok LB cr M0 model fx fx2 R0 0x39a24 R2 0x58938 M1 P K HH Mh Ml ltac:(clear -Ftop; lia)
             ltac:(eapply msteps_trans; [exact MS1| exact MS2]) MG1 FRZ1 CW DEC).
    intros HH1.
    assert (STKc : L5C.stk (hl_sptop L) M1 (S - 320) 14336) by (apply (PMK.stk_call L M1 S 16384 (S - 320) 14336 STK1); clear -F16; lia).
    unfold PNRS.str_push_back_short_spec, PNR.str_push_back_short_spec in PBS. cbn [PNL.pn_str_push_back PnLayoutS_u.NADDR_S] in PBS.
    apply (PBS fx2 R2 M1 model K LB cr o (S - 320) 0x39b20 n0 HH1 MOK K0).
    { unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact B1|]. split; [clear; unfold L5.ra_ok; lia|].
      split; [rewrite (KS2 2%nat) by PMK.inl; exact B2|]. split; [rewrite (KS2 3%nat) by PMK.inl; rewrite (CS1 3%nat) by PMK.inl; exact Rgp0|].
      split; [rewrite (KS2 4%nat) by PMK.inl; rewrite (CS1 4%nat) by PMK.inl; exact Rtp0|]. exact STKc. }
    { rewrite L5K.rl10. exact B10'. } { clear -Ho1; lia. } { exact Ho2. } { exact Ho3. } { exact VS1. } { clear -Hn0; lia. }
    intros fx3 R3 M3 RP3 VS3 HP3 HH3. change (PMSP.pm_scr 1) with 14336 in HP3.
    pose proof (callee_ag LB (S - 320) 14336 [(o, 24)] M1 M3 HP3 STKc ltac:(clear; lia)) as AG3.
    assert (NW : forall a, a < S -> ~ PMK.inW [(o, 24)] a).
    { intros a Ha (rg & [<-|[]] & Hr). unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear -Ha Hr Ho1. lia. }
    assert (R23 : forall i, In i PMK.cs_all -> getr R3 (reg i) = getr R2 (reg i)) by (intros i Hi; apply (PMK.cs_of_preserved R2 R3 i RP3 Hi)).
    assert (STK3 : L5C.stk (hl_sptop L) M3 S 16384) by (apply (PMK.stk_after RSEGS L KL LB M1 M3 S 16384 (S - 320) 14336 [(o, 24)] STK1 HP3); clear; lia).
    assert (SV3 : saves M3).
    { split; [|split; [|split; [|split]]];
        (apply (L5C.u64_at_agree RSEGS M1); [intros i Hi; apply AG3; [clear -Hi Fhi Ftop; lia| apply NW; clear -Hi; lia] | clear -Flo; lia | clear -Fhi Ftop; lia | assumption]). }
    pose proof SV3 as (T1 & T2 & T3 & T4 & T5).
    pose proof (L5C.stk_writable RSEGS _ M3 S 16384 STK3) as WR3.
    assert (WRf3 : L5.writable RSEGS M3 (S - 320) 320) by (apply (L5.writable_sub RSEGS M3 (S - 16384) 16384 (S - 320) 320 WR3); clear; lia).
    (let T := type of (PNSFIP.fgR1_conc fx3 R3 M3 (VV d 0 0 0)) in let T := eval cbn beta iota delta [VV] in T in LeanFeed.pfeed_at PR (PNSFIP.fgR1_conc fx3 R3 M3 (VV d 0 0 0)) T ltac:(cbn beta iota delta [VV]) ltac:(first [PMK.sc | rewrite (R23 19%nat) by PMK.inl; rewrite B19; f_equal; clear; lia])).
    destruct PR as (fx4 & R4 & M4 & MG4 & FR4 & _ & MS4 & KS4 & C9 & _ & C18 & C19).
    assert (EM : M4 = M3) by (apply functional_extensionality; exact FR4). subst M4.
    apply (PMK.spiece_ro RSEGS model fx3 fx4 R3 0x39b20 R4 0x39b3c M3 K Mh Ml MS4).
    apply (push_loop (Z.to_nat (d - 1)) fx4 R4 M3 (d - 1) (d + 1) (n0 + 1)); [clear -Hd; lia| exact HH3| ..].
    + rewrite (KS4 2%nat) by PMK.inl. rewrite (R23 2%nat) by PMK.inl. rewrite (KS2 2%nat) by PMK.inl. exact B2.
    + rewrite (KS4 8%nat) by PMK.inl. rewrite (R23 8%nat) by PMK.inl. rewrite (KS2 8%nat) by PMK.inl. exact B8.
    + exact C9.
    + rewrite C18. f_equal. clear. lia.
    + exact C19.
    + intros i Hi. rewrite (KS4 i); [| revert i Hi; apply sub_in; vm_compute; reflexivity]. rewrite (R23 i) by (apply csr_cs; exact Hi).
      rewrite (KS2 i); [apply CS1; exact Hi|]. revert i Hi. apply sub_in. vm_compute. reflexivity.
    + apply (PMK.ek_trans L LB S 16384 [(o, 24)] M0 M1 M3 EK1).
      apply (PMK.ek_callee_in RSEGS L KL LB LB S 16384 (S - 320) 14336 [(o, 24)] [(o, 24)] M1 M1 M3 HP3 (incl_refl _)); [clear; lia| clear; lia| exact STK1| exact (PMFR.brange_hi L LB BRLB)|].
      intros a Ha. right. exact Ha.
    + apply (PMK.dk_trans L LB S 16384 M0 M1 M3 DK1). apply (PMK.dk_callee L LB LB S 16384 (S - 320) 14336 [(o, 24)] M1 M3 HP3 (incl_refl _)); clear; lia.
    + exact STK3. + exact SV3. + exact VS3.
    + clear -Hn0; lia. + clear -Hn0 Hd; lia. + clear -Hd; lia. + clear; lia. + clear -Hd; lia. + clear -Hd; lia.
Qed.

End Call.

(* [comment removed for export] *)
Theorem from_int_ok : PNRS.str_push_back_short_spec L HI -> PNRS.from_int_spec L HI.
Proof.
  intros PBS. unfold PNRS.from_int_spec, PNR.from_int_spec.
  intros fx R M model K LB cr o v sp r n HH MOK K0 ENT A10 Hv A11 Ho1 Ho2 Ho3 VS Hn KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  change (PMSP.pm_scr 2) with 16384 in STK.
  assert (BRLB : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok _ LB cr M _ HH); intros y Hy; exact Hy).
  cbn [PNL.pn_from_int PnLayoutS_u.NADDR_S].
  exact (call R M model K LB cr o v sp r n MOK K0 Rra RAok Rsp Rgp Rtp STK A10 Hv A11 Ho1 Ho2 Ho3 Hn BRLB PBS KONT fx HH VS).
Qed.

End WithHeap.
End PNSFI.
