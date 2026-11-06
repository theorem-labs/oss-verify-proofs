(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac Mem Cells Step Frame Exec MState Arr. 
From OSSVerify.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord FastWordSem.
From OSSVerify.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout.
From OSSVerify.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery HxLearn HxSym.
From OSSVerify.Proofs.openssl.bignum.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit HxsSym.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BgWords.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_normal.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit AsLoop.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXB Require Import HxbImage HxbInv HxbHooks HxbSqr8Init.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnW2 Require Import HxPoly2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition CSQ : Z := 352.

Definition ASZ : Z := 64.
Definition RSZ : Z := 128.
Lemma ASZ_eq : to_Z ASZI = ASZ. Proof. reflexivity. Qed.
Lemma RSZ_eq : to_Z RSZI = RSZ. Proof. reflexivity. Qed.

Definition aptrs2 (rp ap n lo : Z) : Prop :=
  rp mod 8 = 0 /\ ap mod 8 = 0 /\ (rp + 8 * n <= SHLO \/ SHHI <= rp) /\ SHHI <= lo.

Definition sqr_comba8_aspec (CS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z),
    limbs a -> length a = 8%nat ->
    limbs_at bgbsegs m (bv_unsigned a1) a ->
    wr_at bgbsegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    stk bgbsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgbsegs m ->
    shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bgbsegs m (bv_unsigned a0) 128 -> acc bgbsegs m (bv_unsigned a1) 64 ->
    aptrs2 (bv_unsigned a0) (bv_unsigned a1) 16 lo ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a1)%Z ->
    (bv_unsigned a0 + 128 <= 65536 \/ 12554240 <= bv_unsigned a0)%Z ->
    evt bgbsegs (vl_post bgbsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS (sqr_comba8 a) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x22ec0c) fc None m (seg_rom bgbsegs)).

Definition stopq (pc : w64) : bool := w_eqb pc PC_CQ_RET.

Definition FUELQ : nat := 3500.
Definition cq_run : option (list snode * sstate) := sxs_run SHBW bgbsegs stopq FUELQ [] SQ.

Definition TAQ : list int := [40; 41; 42; 43; 44; 45; 46; 47]%uint63.
Definition st0q : ubmap * nmap := fold_left ainput (TAQ ++ TAQ) (PositiveMap.empty Z, PositiveMap.empty ninfo).

Definition final_regsq : list (rix * hval) :=
  [(X1, VP TQ_RA w_zero); (X2, VP TQ_STK (W false CSQI)); (X3, VP TQ_GP w_zero); (X4, VP TQ_TP w_zero);
   (X8, VP TQ_S0 w_zero); (X9, VP (TQ_S0 + 1)%uint63 w_zero); (X18, VP (TQ_S0 + 2)%uint63 w_zero); (X19, VP (TQ_S0 + 3)%uint63 w_zero);
   (X20, VP (TQ_S0 + 4)%uint63 w_zero); (X21, VP (TQ_S0 + 5)%uint63 w_zero); (X22, VP (TQ_S0 + 6)%uint63 w_zero); (X23, VP (TQ_S0 + 7)%uint63 w_zero);
   (X24, VP (TQ_S0 + 8)%uint63 w_zero); (X25, VP (TQ_S0 + 9)%uint63 w_zero); (X26, VP (TQ_S0 + 10)%uint63 w_zero); (X27, VP (TQ_S0 + 11)%uint63 w_zero)].

Definition final_regs_okq (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) final_regsq.

Definition OUTIX : list int := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%uint63.
Definition outs_of (rg : region) : list int :=
  map (fun k => match rd_cell bgbsegs rg k with CP t _ => t | CW _ _ => 0%uint63 end) OUTIX.

Definition kbs_ptrs (tags : list int) : list kb := concat (map kbs_ptr tags).

Definition cq_ok (r : option (list snode * sstate)) : bool :=
  match r with
  | Some (log, X) =>
      w_eqb (s_pc X) PC_CQ_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_okq X
      && match mget (s_mem X) TQ_R with
         | Some rg =>
             (match rg_abs rg with None => true | Some _ => false end) && (to_Z (rg_size rg) =? RSZ)
             && kb_check bgbsegs rg 0 (kbs_ptrs (outs_of rg))
             && incr_chk (to_Z NEXTQ) (rev log)
             && match arun st0q (rev log) with
                | Some st => mul_check st TAQ TAQ (outs_of rg) (MW ^ 16)
                | None => false
                end
         | None => false
         end
  | None => false
  end.

Lemma cq_ok_inv (r : option (list snode * sstate)) : cq_ok r = true ->
  exists log X rg st, r = Some (log, X) /\ s_pc X = PC_CQ_RET /\ s_resv X = RNone /\ final_regs_okq X = true
    /\ mget (s_mem X) TQ_R = Some rg /\ rg_abs rg = None /\ to_Z (rg_size rg) = RSZ
    /\ kb_check bgbsegs rg 0 (kbs_ptrs (outs_of rg)) = true /\ incr_chk (to_Z NEXTQ) (rev log) = true
    /\ arun st0q (rev log) = Some st /\ mul_check st TAQ TAQ (outs_of rg) (MW ^ 16) = true.
Proof.
  destruct r as [[log X]|]; cbn [cq_ok]; [|discriminate]. intros H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (mget (s_mem X) TQ_R) as [rg|] eqn:Eg; [|discriminate].
  apply andb_prop in H4 as [H4 H9]. apply andb_prop in H4 as [H4 H8]. apply andb_prop in H4 as [H4 H7]. apply andb_prop in H4 as [H5 H6].
  destruct (arun st0q (rev log)) as [st|] eqn:Ea; [|discriminate].
  exists log, X, rg, st. split; [reflexivity|]. split; [apply w_eqb_true_iff; exact H1|].
  split; [destruct (s_resv X); [reflexivity | discriminate | discriminate]|]. split; [exact H3|]. split; [exact Eg|].
  split; [destruct (rg_abs rg); [discriminate | reflexivity]|]. split; [apply Z.eqb_eq; exact H6|]. auto.
Qed.

Lemma cq_run_unfold : cq_run = sxs_run SHBW bgbsegs stopq FUELQ [] SQ.
Proof. reflexivity. Qed.

Lemma cq_checked : cq_ok cq_run = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_finalq : exists ic', hx_fetch bgbsegs IEmpty PC_CQ_RET = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.

Definition dir_bq (k : Z) (rg : region) : bool :=
  (k <? 10) &&
  match rg_abs rg with
  | Some _ => negb (rg_wr rg) && ((k =? 1) || (k =? 9))
  | None => ((k =? 2) && negb (rg_wr rg)) || ((k =? 3) && negb (rg_wr rg))
            || ((k =? 6) && (to_Z (rg_size rg) =? RSZ)) || ((k =? 7) && negb (rg_wr rg)) || ((k =? 8) && (to_Z (rg_size rg) =? CSQ))
  end.

Lemma MQ_checked : mem_check dir_bq MQ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma MQ_get8 : mget MQ TQ_STK = Some cq_stk.
Proof. vm_compute. reflexivity. Qed.

Lemma MQ_class (t : int) (rg : region) : mget MQ t = Some rg ->
  match rg_abs rg with
  | Some _ => rg_wr rg = false
  | None => (rg_wr rg = true -> (t = TQ_R /\ to_Z (rg_size rg) = RSZ) \/ (t = TQ_STK /\ to_Z (rg_size rg) = CSQ))
            /\ (tag_even t = false -> t = 3%uint63 \/ t = 7%uint63)
  end.
Proof.
  intros G. pose proof (mem_check_ok dir_bq MQ MQ_checked t rg G) as H. unfold dir_bq in H. apply andb_prop in H as [_ H].
  destruct (rg_abs rg) as [x|].
  - apply andb_prop in H as [H _]. apply negb_true_iff in H. exact H.
  - repeat (apply orb_prop in H as [H|H]); apply andb_prop in H as [E1 E2]; apply Z.eqb_eq in E1;
      lazymatch type of E1 with to_Z t = ?c =>
        let ci := eval vm_compute in (of_Z c) in
        assert (Et : t = ci) by (apply to_Z_inj; exact E1); subst t
      end;
      first [ apply negb_true_iff in E2; split; [intros X; rewrite E2 in X; discriminate X | intros X; first [discriminate X | auto]]
            | apply Z.eqb_eq in E2; split; [intros _; first [left; split; [reflexivity | exact E2] | right; split; [reflexivity | exact E2]] | intros X; discriminate X] ].
Qed.

Lemma hsum_lval (l : list Z) : hsum l = lval l.
Proof. induction l as [|x l IH]; cbn [hsum lval]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma kbs_ptrs_intro (rho : valuation) : forall tags : list int, Forall (fun t => 0 <= rho t < 2 ^ 64) tags ->
  Forall2 (kb_ok rho) (kbs_ptrs tags) (lbytes (map rho tags)).
Proof.
  induction 1 as [|t tags Ht _ IH]; [constructor|]. unfold kbs_ptrs. cbn [map concat]. rewrite lbytes_cons.
  apply Forall2_app; [exact (kbs_ptr_intro rho t (rho t) eq_refl Ht) | exact IH].
Qed.

Lemma kbs_ptrs_bytes (rho : valuation) : forall (tags : list int) (bs : list byte), Forall (fun t => 0 <= rho t < 2 ^ 64) tags ->
  Forall2 (kb_ok rho) (kbs_ptrs tags) bs -> bs = lbytes (map rho tags).
Proof.
  induction tags as [|t tags IH]; intros bs Ht H.
  - inversion H. reflexivity.
  - unfold kbs_ptrs in H. cbn [map concat] in H. destruct (Forall2_app_split _ _ _ _ H) as (b1 & b2 & -> & H1 & H2).
    inversion Ht as [|? ? Ht1 Ht2]; subst. cbn [map]. rewrite lbytes_cons. f_equal; [exact (kbs_ptr_bytes rho t b1 Ht1 H1) | exact (IH b2 Ht2 H2)].
Qed.

Lemma mapped_below (m : word -> option byte) (A n : Z) : mem_inv bgbsegs m -> 0 <= A -> A + n <= 2 ^ 64 -> 0 < n ->
  (forall i, 0 <= i < n -> exists b, mrd bgbsegs m (wa (A + i)) = Some b) -> A + n <= UTOP.
Proof.
  intros MI HA Hn Hpos H. destruct (H (n - 1) ltac:(lia)) as [b Hb]. pose proof (mrd_below bgbsegs m _ _ MI Hb) as X.
  rewrite wa_unsigned in X by lia. lia.
Qed.

Lemma acc_zero_bytes (m : word -> option byte) (p n : Z) : p mod 8 = 0 -> acc bgbsegs m p n -> 0 < n -> n mod 8 = 0 ->
  bytes_at bgbsegs m (shad p) (repeat z8 (Z.to_nat (n / 8))).
Proof.
  intros Hp Hacc Hn Hn8.
  assert (G : forall i, 0 <= i < n / 8 -> bytes_at bgbsegs m (shad p + i) [z8]).
  { intros i Hi. rewrite <- (shad_add8 p i). apply (acc_gran0 bgbsegs m p n (p + 8 * i) Hacc); Z.div_mod_to_equations; lia. }
  split; [|split].
  - destruct (G 0 ltac:(Z.div_mod_to_equations; lia)) as (B0 & _ & _). lia.
  - rewrite repeat_length, Z2Nat.id by (Z.div_mod_to_equations; lia).
    destruct (G (n / 8 - 1) ltac:(Z.div_mod_to_equations; lia)) as (_ & B1 & _). cbn [length Z.of_nat Pos.of_succ_nat] in B1. lia.
  - intros k Hk. rewrite repeat_length in Hk. rewrite nth_error_repeat by exact Hk.
    destruct (G (Z.of_nat k) ltac:(lia)) as (_ & _ & B). specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B.
    rewrite Z.add_0_r in B. exact B.
Qed.

Lemma final_regs_denq (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_okq S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho TQ_RA w_zero /\ x2 = pword rho TQ_STK (W false CSQI) /\ x3 = pword rho TQ_GP w_zero /\ x4 = pword rho TQ_TP w_zero
  /\ x8 = pword rho TQ_S0 w_zero /\ x9 = pword rho (TQ_S0 + 1)%uint63 w_zero /\ x18 = pword rho (TQ_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (TQ_S0 + 3)%uint63 w_zero /\ x20 = pword rho (TQ_S0 + 4)%uint63 w_zero /\ x21 = pword rho (TQ_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (TQ_S0 + 6)%uint63 w_zero /\ x23 = pword rho (TQ_S0 + 7)%uint63 w_zero /\ x24 = pword rho (TQ_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (TQ_S0 + 9)%uint63 w_zero /\ x26 = pword rho (TQ_S0 + 10)%uint63 w_zero /\ x27 = pword rho (TQ_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_okq, final_regsq in Hok. cbn [forallb fst snd] in Hok.
  repeat (apply andb_prop in Hok as [?E Hok]). clear Hok.
  repeat match goal with E : hval_eqb (rget S ?X) ?v = true |- _ => apply hval_eqb_eq in E end.
  pose proof (HR (Z_to_bv 5 1)) as D1. pose proof (HR (Z_to_bv 5 2)) as D2. pose proof (HR (Z_to_bv 5 3)) as D3. pose proof (HR (Z_to_bv 5 4)) as D4.
  pose proof (HR (Z_to_bv 5 8)) as D8. pose proof (HR (Z_to_bv 5 9)) as D9. pose proof (HR (Z_to_bv 5 18)) as D18. pose proof (HR (Z_to_bv 5 19)) as D19.
  pose proof (HR (Z_to_bv 5 20)) as D20. pose proof (HR (Z_to_bv 5 21)) as D21. pose proof (HR (Z_to_bv 5 22)) as D22. pose proof (HR (Z_to_bv 5 23)) as D23.
  pose proof (HR (Z_to_bv 5 24)) as D24. pose proof (HR (Z_to_bv 5 25)) as D25. pose proof (HR (Z_to_bv 5 26)) as D26. pose proof (HR (Z_to_bv 5 27)) as D27.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 1))) with (rget S X1) in D1. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 2))) with (rget S X2) in D2.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 3))) with (rget S X3) in D3. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 4))) with (rget S X4) in D4.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 8))) with (rget S X8) in D8. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 9))) with (rget S X9) in D9.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 18))) with (rget S X18) in D18. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 19))) with (rget S X19) in D19.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 20))) with (rget S X20) in D20. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 21))) with (rget S X21) in D21.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 22))) with (rget S X22) in D22. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 23))) with (rget S X23) in D23.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 24))) with (rget S X24) in D24. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 25))) with (rget S X25) in D25.
  change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 26))) with (rget S X26) in D26. change (rf_get vzero (s_regs S) (rix_of_reg (Z_to_bv 5 27))) with (rget S X27) in D27.
  repeat match goal with E : rget S ?X = _, D : den rho (rget S ?X) _ |- _ => rewrite E in D; clear E end.
  cbn [den] in *. repeat split; assumption.
Qed.

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

Lemma cq_le8 (m : word -> option byte) (A : Z) (w : word) : ro_cells bgbsegs m A [C8 w] -> bytes_at bgbsegs m A (le8 w).
Proof. intros [_ B1]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1. Qed.

Section HandoffQ.
Variables (rho : valuation) (m : word -> option byte) (a : list Z) (AP RP lo sp0 : Z).
Hypothesis MI : mem_inv bgbsegs m.
Hypothesis LA : limbs a.
Hypothesis HLA : length a = 8%nat.
Hypothesis RA : limbs_at bgbsegs m AP a.
Hypothesis WR : wr_at bgbsegs m RP RSZ.
Hypothesis Hr8 : rho TQ_STK = sp0 - CSQ.
Hypothesis Hr2 : rho TQ_A = AP.
Hypothesis Hr3 : rho 3%uint63 = shad AP.
Hypothesis Hr6 : rho TQ_R = RP.
Hypothesis Hr7 : rho 7%uint63 = shad RP.
Hypothesis HrA : map rho TAQ = a.
Hypothesis SHBC : shb_cells bgbsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
Hypothesis ACR : acc bgbsegs m RP RSZ.
Hypothesis ACA : acc bgbsegs m AP ASZ.

Definition ptr_okq (p : Z) : Prop := 0 < p /\ p mod 2 ^ to_Z ALQ = 0.

Lemma tags_range (tags : list int) (l : list Z) : map rho tags = l -> limbs l -> Forall (fun t => 0 <= rho t < 2 ^ 64) tags.
Proof.
  intros E HL. subst l. unfold limbs in HL. rewrite Forall_map in HL. eapply Forall_impl; [|exact HL].
  intros t Ht. cbn in Ht. unfold limb, BW in Ht. change (2 ^ 64) with 18446744073709551616. exact Ht.
Qed.

Lemma cq_got_ok : region_ok bgbsegs rho TQ_GOT cq_got m.
Proof.
  destruct SHBC as [C1 _].
  apply (static_region_ok bgbsegs rho TQ_GOT cq_got m GOT_SHB_CELL (kbs_Z 8 (to_Z SHB_CELL)) (le8 (Z_to_bv 64 g_shadow_memory_dynamic_address)) eq_refl eq_refl);
    [closed_side | apply kbs_Z_intro; closed_side | exact (cq_le8 m _ _ C1) | closed_side | closed_side].
Qed.

Lemma cq_shb_ok : region_ok bgbsegs rho TQ_SHB cq_shb m.
Proof.
  destruct SHBC as [_ C2].
  apply (static_region_ok bgbsegs rho TQ_SHB cq_shb m SHB_CELL (kbs_Z 8 SHB) (le8 (Z_to_bv 64 SHB)) eq_refl eq_refl);
    [closed_side | apply kbs_Z_intro; closed_side | exact (cq_le8 m _ _ C2) | closed_side | closed_side].
Qed.

Lemma limb_region_ok (t t0 : int) (tags : list int) (A : Z) (l : list Z) :
  rho t = A -> map rho tags = l -> limbs l -> length l = 8%nat -> limbs_at bgbsegs m A l -> ptr_okq A ->
  learn_check bgbsegs (RG None ASZI ALQ false DUnk 3%nat (limb_cellsq t0)) [(0, kbs_ptrs tags)] 0 64 = true ->
  region_ok bgbsegs rho t (RG None ASZI ALQ false DUnk 3%nat (limb_cellsq t0)) m.
Proof.
  intros Er El HL Hlen Hat [Hp Hal] Hck. pose proof (limbs_at_bound bgbsegs m A l Hat) as [B0 B1]. rewrite Hlen in B1.
  assert (Hmap : forall i, 0 <= i < ASZ -> exists x, mrd bgbsegs m (wa (A + i)) = Some x).
  { intros i Hi. apply (bytes_at_mapped bgbsegs m A (lbytes l) Hat). rewrite lbytes_lengthZ, Hlen. unfold ASZ in Hi. lia. }
  pose proof (mapped_below m A ASZ MI B0 ltac:(unfold ASZ; lia) ltac:(unfold ASZ; lia) Hmap) as HU. unfold UTOP in HU.
  apply (region_ok_learn_gen bgbsegs rho t _ m [(0, kbs_ptrs tags)]); unfold rbase; cbn [rg_abs rg_size rg_d rg_al rg_wr]; rewrite ?Er;
    rewrite ?ASZ_eq; unfold ASZ in *.
  - split; [exact B0 | left; exact Hp].
  - unfold two63. lia.
  - lia.
  - cbn. lia.
  - cbn. lia.
  - vm_compute. reflexivity.
  - exact Hal.
  - exact Hmap.
  - discriminate.
  - constructor; [|constructor]. exists (lbytes l). cbn [fst snd]. rewrite Z.add_0_r. split; [|exact Hat].
    rewrite <- El. apply kbs_ptrs_intro. exact (tags_range tags l El HL).
  - exact Hck.
Qed.

Hypothesis PA : ptr_okq AP.
Hypothesis PR : ptr_okq RP.

Lemma cq_a_ok : region_ok bgbsegs rho TQ_A cq_a m.
Proof. apply (limb_region_ok TQ_A TQ_LA TAQ AP a Hr2 HrA LA HLA RA PA). vm_compute. reflexivity. Qed.

Lemma AP_hi : AP + ASZ <= UTOP.
Proof.
  pose proof (limbs_at_bound bgbsegs m AP a RA) as [B0 B1]. rewrite HLA in B1. unfold ASZ.
  apply (mapped_below m AP 64 MI B0 ltac:(lia) ltac:(lia)). intros i Hi. apply (bytes_at_mapped bgbsegs m AP (lbytes a) RA). rewrite lbytes_lengthZ, HLA. lia.
Qed.
Lemma RP_hi : RP + RSZ <= UTOP.
Proof.
  destruct WR as (W0 & W1 & Hw). apply (mapped_below m RP RSZ MI W0 W1 ltac:(unfold RSZ; lia)).
  intros i Hi. apply (wview_mrd bgbsegs m _ asegs_wr_rd). apply Hw. exact Hi.
Qed.

Lemma cq_r_ok : region_ok bgbsegs rho TQ_R cq_r m.
Proof.
  pose proof RP_hi as HU. unfold UTOP, RSZ in HU. destruct PR as [Hp Hal]. unfold cq_r.
  pose proof WR as WR'. unfold RSZ in WR'.
  apply (fresh_region_ok rho TQ_R RSZI ALQ true m RP Hr6 Hp); rewrite ?RSZ_eq; unfold RSZ; [unfold two63; lia | lia | closed_side | exact Hal | exact WR'].
Qed.

Lemma cq_ash_ok : region_ok bgbsegs rho 3%uint63 cq_ash m.
Proof.
  pose proof AP_hi as HU. unfold UTOP, ASZ in HU. destruct PA as [Hp Hal]. change (2 ^ to_Z ALQ) with 8 in Hal.
  pose proof ACA as ACA'. unfold ASZ in ACA'.
  pose proof (AsKit.shad_range AP ltac:(lia)) as SR. unfold SHLO, SHHI in SR. unfold cq_ash.
  apply (zero_region_ok rho 3%uint63 ASHI m (shad AP) Hr3); change (to_Z ASHI) with 8; [lia | unfold two63; lia | lia |].
  change (Z.to_nat 8) with (Z.to_nat (64 / 8)). exact (acc_zero_bytes m AP 64 Hal ACA' ltac:(lia) eq_refl).
Qed.
Lemma cq_rsh_ok : region_ok bgbsegs rho 7%uint63 cq_rsh m.
Proof.
  pose proof RP_hi as HU. unfold UTOP, RSZ in HU. destruct PR as [Hp Hal]. change (2 ^ to_Z ALQ) with 8 in Hal.
  pose proof ACR as ACR'. unfold RSZ in ACR'.
  pose proof (AsKit.shad_range RP ltac:(lia)) as SR. unfold SHLO, SHHI in SR. unfold cq_rsh.
  apply (zero_region_ok rho 7%uint63 RSHI m (shad RP) Hr7); change (to_Z RSHI) with 16; [lia | unfold two63; lia | lia |].
  change (Z.to_nat 16) with (Z.to_nat (128 / 8)). exact (acc_zero_bytes m RP 128 Hal ACR' ltac:(lia) eq_refl).
Qed.

Hypothesis STKH : stk bgbsegs m lo sp0.
Hypothesis Hlo : lo <= sp0 - CSQ.
Hypothesis LOHI : SHHI <= lo.

Lemma cq_stk_ok : region_ok bgbsegs rho TQ_STK cq_stk m.
Proof.
  destruct STKH as (S0 & S1 & Hs). unfold SHHI in LOHI.
  assert (Hmap : forall i, 0 <= i < CSQ -> exists x, mrd bgbsegs m (wa (sp0 - CSQ + i)) = Some x).
  { intros i Hi. exact (proj2 (Hs (sp0 - CSQ + i) ltac:(unfold CSQ in *; lia))). }
  pose proof (mapped_below m (sp0 - CSQ) CSQ MI ltac:(unfold CSQ in *; lia) ltac:(unfold CSQ in *; lia) ltac:(unfold CSQ; lia) Hmap) as HU. unfold UTOP in HU.
  assert (W : wr_at bgbsegs m (sp0 - CSQ) (to_Z CSQI)).
  { change (to_Z CSQI) with CSQ. split; [unfold CSQ in *; lia|]. split; [unfold CSQ in *; lia|]. intros i Hi. exact (proj1 (Hs (sp0 - CSQ + i) ltac:(unfold CSQ in *; lia))). }
  unfold cq_stk. apply (fresh_region_ok rho TQ_STK CSQI 0 true m (sp0 - CSQ) Hr8); change (to_Z CSQI) with CSQ; unfold CSQ in *;
    [lia | unfold two63; lia | lia | closed_side | apply Z.mod_1_r | exact W].
Qed.

Hypothesis DRA : RP + RSZ <= AP \/ AP + ASZ <= RP.
Hypothesis SEPR : RP + RSZ <= sp0 - CSQ \/ sp0 <= RP.
Hypothesis SEPA : AP + ASZ <= sp0 - CSQ \/ sp0 <= AP.
Hypothesis OFFR : RP + 8 * 16 <= SHLO \/ SHHI <= RP.
Hypothesis RIMG : RP + RSZ <= 65536 \/ 12554240 <= RP.

Local Ltac sepq :=
  unfold rbase; cbn [rg_abs rg_size rg_wr cq_got cq_shb cq_a cq_ash cq_r cq_rsh cq_stk shadow_region]; rewrite ?Hr8, ?Hr2, ?Hr3, ?Hr6, ?Hr7;
  change (to_Z ASZI) with 64; change (to_Z RSZI) with 128; change (to_Z ASHI) with 8; change (to_Z RSHI) with 16; change (to_Z 8%uint63) with 8;
  change (to_Z CSQI) with CSQ; change (to_Z GOT_SHB_CELL) with 6147864; change (to_Z SHB_CELL) with 6945336; unfold CSQ, ASZ, RSZ in *;
  repeat (constructor; [cbn [fst snd]; intros Hw; first [lia | unfold shad, SHB in *; Z.div_mod_to_equations; lia | destruct Hw as [X|X]; discriminate X]|]); constructor.

Lemma rmemq : Rmem bgbsegs rho MQ m.
Proof.
  pose proof AP_hi as HUA. pose proof RP_hi as HUR. unfold UTOP in HUA, HUR.
  pose proof PA as [PA0 _]. pose proof PR as [PR0 _].
  unfold SHLO, SHHI in OFFR, LOHI.
  pose proof (Rmem_empty bgbsegs rho m) as R0. pose proof (dir_inw_empty rho) as I0.
  destruct (Rmem_add_sepw bgbsegs rho IEmpty TQ_GOT cq_got m [] R0 I0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_got_ok ltac:(constructor)) as [R1 I1].
  destruct (Rmem_add_sepw bgbsegs rho _ TQ_SHB cq_shb m _ R1 I1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_shb_ok ltac:(sepq)) as [R2 I2].
  destruct (Rmem_add_sepw bgbsegs rho _ TQ_A cq_a m _ R2 I2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_a_ok ltac:(sepq)) as [R3 I3].
  destruct (Rmem_add_sepw bgbsegs rho _ 3%uint63 cq_ash m _ R3 I3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_ash_ok ltac:(sepq)) as [R4 I4].
  destruct (Rmem_add_sepw bgbsegs rho _ 7%uint63 cq_rsh m _ R4 I4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_rsh_ok ltac:(sepq)) as [R7 I7].
  destruct (Rmem_add_sepw bgbsegs rho _ TQ_R cq_r m _ R7 I7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_r_ok ltac:(sepq)) as [R8 I8].
  exact (proj1 (Rmem_add_sepw bgbsegs rho _ TQ_STK cq_stk m _ R8 I8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_stk_ok ltac:(sepq))).
Qed.

End HandoffQ.

Definition rhoq (sp0 AP RP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (a : list Z) : valuation := fun t =>
  if (t =? TQ_STK)%uint63 then sp0 - CSQ
  else if (t =? TQ_A)%uint63 then AP else if (t =? 3)%uint63 then shad AP
  else if (t =? TQ_R)%uint63 then RP else if (t =? 7)%uint63 then shad RP
  else if (t =? TQ_RA)%uint63 then bv_unsigned ra else if (t =? TQ_GP)%uint63 then bv_unsigned gp else if (t =? TQ_TP)%uint63 then bv_unsigned tp
  else if (t =? TQ_S0)%uint63 then bv_unsigned s0 else if (t =? TQ_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? TQ_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? TQ_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? TQ_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? TQ_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? TQ_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? TQ_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? TQ_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? TQ_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? TQ_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? TQ_S0 + 11)%uint63 then bv_unsigned s11
  else if ((TQ_LA <=? t) && (t <? NEXTQ))%uint63 then nth (Z.to_nat (to_Z t - 40)) a 0
  else 0.

Lemma Rregs_initq (rho : valuation) (a : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXTQ -> rho t = rhoq (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a0) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a t) ->
  CSQ <= bv_unsigned sp ->
  Rregs rho regsq (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho Hsp r.
  assert (Esp : pword rho TQ_STK (W false CSQI) = sp).
  { unfold pword. rewrite (Hrho TQ_STK) by (vm_compute; reflexivity).
    change (rhoq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TQ_STK) with (bv_unsigned sp - CSQ).
    change (wZ (W false CSQI)) with CSQ. replace (bv_unsigned sp - CSQ + CSQ) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma tags_small : forallb (fun t => (to_Z t <? to_Z NEXTQ)) (TAQ ++ TAQ) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SHBW_Z8 : wZ SHBW = SHB. Proof. reflexivity. Qed.

Theorem sqr_comba8_okA : sqr_comba8_aspec CSQ.
Proof.
  unfold sqr_comba8_aspec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a lo
         LA HLA RA WR DRA Hstk Hlo SEPR SEPA Hmi SHBC ACR ACA (AL_R & AL_A & OFFR & LOHI) P0R P0A RIMG.
  set (SPz := bv_unsigned sp) in *. set (RP := bv_unsigned a0) in *. set (AP := bv_unsigned a1) in *.
  set (rho0 := rhoq SPz AP RP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a).
  set (WIV := [(RP, RP + 8 * 16); (SPz - CSQ, SPz)]).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x22ec0c) fc None m (seg_rom bgbsegs)).
  assert (HspC : CSQ <= SPz) by (destruct Hstk as (S0 & _); lia).
  assert (PA : ptr_okq AP) by (split; [exact P0A | exact AL_A]).
  assert (PR : ptr_okq RP) by (split; [exact P0R | exact AL_R]).

  assert (HA0 : map rho0 TAQ = a).
  { destruct a as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate HLA. reflexivity. }

  destruct (cq_ok_inv cq_run cq_checked) as (logE & SE & rgE & stE & Erun & Epc & Erv & Hregs & EgR & EaR & EsR & Hkb & Hincr & Harun & Hchk).
  rewrite cq_run_unfold in Erun.
  assert (Hmaps : forall rho2, (forall t, to_Z t < to_Z NEXTQ -> rho2 t = rho0 t) -> map rho2 TAQ = a).
  { intros rho2 Hr. rewrite <- HA0. unfold TAQ. cbn [map]. rewrite !Hr by (vm_compute; reflexivity). reflexivity. }

  assert (HRS0 : RSn bgbsegs SHBW rho0 SQ ms0).
  { split.
    - intros rho2 Hag. cbn [SQ s_next] in Hag.
      assert (Hrho : forall t, to_Z t < to_Z NEXTQ -> rho2 t = rho0 t) by exact Hag.
      pose proof (Hmaps rho2 Hrho) as HA2.
      unfold R, ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS SQ s_pc s_regs s_resv s_mem].
      split; [reflexivity|]. split; [reflexivity|]. split.
      { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply Rregs_initq; [exact Hrho | exact HspC]. }
      split; [reflexivity|].
      apply (rmemq rho2 m a AP RP lo SPz Hmi LA HLA RA); try assumption;
        first [ exact (Hrho TQ_STK ltac:(vm_compute; reflexivity)) | exact (Hrho TQ_A ltac:(vm_compute; reflexivity))
              | exact (Hrho 3%uint63 ltac:(vm_compute; reflexivity)) | exact (Hrho TQ_R ltac:(vm_compute; reflexivity))
              | exact (Hrho 7%uint63 ltac:(vm_compute; reflexivity)) ].
    -
      cbn [SQ s_next s_mem]. intros rho2 Hag s rg G Ea Hodd. rewrite SHBW_Z8.
      pose proof (MQ_class s rg G) as C. rewrite Ea in C. destruct C as [_ C].
      destruct (C Hodd) as [-> | ->].
      + rewrite (Hag 3%uint63) by (vm_compute; reflexivity). change ((3 - 1)%uint63) with TQ_A. rewrite (Hag TQ_A) by (vm_compute; reflexivity). reflexivity.
      + rewrite (Hag 7%uint63) by (vm_compute; reflexivity). change ((7 - 1)%uint63) with TQ_R. rewrite (Hag TQ_R) by (vm_compute; reflexivity). reflexivity. }

  assert (HC0 : CInv bgbsegs MQ WIV m F fc SQ ms0).
  { unfold CInv, ms0. cbn [SQ s_mem ms_mem ms_fregs ms_fcsr ms_rom ms_regs MS].
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hmi|].
    repeat (split; [reflexivity|]). do 31 eexists. reflexivity. }
  assert (HP : forall rho, agree_below NEXTQ rho0 rho -> sx_pres bgbsegs rho (CInv bgbsegs MQ WIV m F fc)).
  { intros rho Hag. apply CInv_sx. intros t rg G Hw. pose proof (MQ_class t rg G) as C. unfold rbase.
    destruct (rg_abs rg) as [x|]; [rewrite Hw in C; discriminate C|]. destruct C as [C _].
    destruct (C Hw) as [[-> Es]|[-> Es]]; rewrite Es.
    - rewrite (Hag TQ_R) by (vm_compute; reflexivity). change (rho0 TQ_R) with RP. unfold WIV, RSZ. cbn [inside]. left. lia.
    - rewrite (Hag TQ_STK) by (vm_compute; reflexivity). change (rho0 TQ_STK) with (SPz - CSQ). unfold WIV, CSQ. cbn [inside]. right. left. lia. }
  destruct (sxs_run_sound SHBW bgbsegs stopq (CInv bgbsegs MQ WIV m F fc) NEXTQ rho0 HP FUELQ rho0 [] logE SQ SE ms0
              (agree_below_refl _ _) ltac:(cbn [SQ s_next]; lia) HRS0 HC0 (Forall_nil _) (Forall_nil _) Erun)
    as (rho1 & ms1 & Hag1 & Hms & HRS1 & HC1 & Hlog1 & _).
  cbn [SQ s_next] in Hag1.
  assert (Hv : forall t, to_Z t < to_Z NEXTQ -> rho1 t = rho0 t) by exact Hag1.

  pose proof (Rn_R bgbsegs rho1 SE ms1 (proj1 HRS1)) as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_finalq as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step bgbsegs rho1 IEmpty ic' SE ms1 (ic_ok_empty bgbsegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_trans bgbsegs _ _ _ Hms (msteps_one bgbsegs _ _ Hstep))|].
  destruct HC1 as (Hd1 & MU & WM & MI1 & Hfr & Hfc & Hro & Hnf).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                   & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hfr, Hfc, Hro, Hrv in Ems2.
  destruct (final_regs_denq rho1 SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  rewrite (pword_scalar rho1 TQ_RA ra) in E1 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 TQ_GP gp) in E3 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 TQ_TP tp) in E4 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 TQ_S0 s0) in E8 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 1)%uint63 s1) in E9 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 2)%uint63 s2) in E18 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 3)%uint63 s3) in E19 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 4)%uint63 s4) in E20 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 5)%uint63 s5) in E21 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 6)%uint63 s6) in E22 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 7)%uint63 s7) in E23 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 8)%uint63 s8) in E24 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 9)%uint63 s9) in E25 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 10)%uint63 s10) in E26 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (TQ_S0 + 11)%uint63 s11) in E27 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. rewrite Hv by (vm_compute; reflexivity). change (rho0 TQ_STK) with (SPz - CSQ). change (wZ (W false CSQI)) with CSQ.
    replace (SPz - CSQ + CSQ) with SPz by lia. apply Z_to_bv_bv_unsigned. }
  subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2. rewrite E2' in Ems2.

  set (m' := ms_mem ms1) in *.
  unfold vl_post. exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
  split; [exact Ems2|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
  split.
  -
    pose proof (Hmaps rho1 Hv) as HA1.
    assert (Hin : forall t, In t (TAQ ++ TAQ) -> 0 <= rho1 t < MW /\ to_Z t < to_Z NEXTQ).
    { intros t Ht. split; [|apply Z.ltb_lt; exact (proj1 (forallb_forall _ _) tags_small t Ht)].
      change MW with (2 ^ 64). assert (Ht' : In t TAQ) by (apply in_app_or in Ht; destruct Ht as [Ht|Ht]; exact Ht).
      exact (proj1 (Forall_forall _ _) (tags_range rho1 TAQ a HA1 LA) t Ht'). }
    assert (Hlt : hsum (map rho1 TAQ) * hsum (map rho1 TAQ) < (MW ^ 16)).
    { rewrite HA1, !hsum_lval. pose proof (lval_bound a LA) as H1. rewrite HLA in H1.
      change (MW ^ 16) with (Bp 8 * Bp 8). clear -H1. nia. }
    destruct (mul_cert rho1 (rev logE) TAQ TAQ (outs_of rgE) (to_Z NEXTQ) (MW ^ 16) stE (Forall_rev Hlog1) Hin Hincr Harun Hchk ltac:(vm_compute; reflexivity) Hlt) as [Hsum Hrange].
    rewrite HA1, !hsum_lval in Hsum.
    set (L := map rho1 (outs_of rgE)) in *.
    assert (HLl : limbs L).
    { unfold L, limbs. rewrite Forall_map. eapply Forall_impl; [|exact Hrange]. intros t Ht. cbn in Ht. unfold limb, BW. unfold MW in Ht. exact Ht. }
    assert (EL : L = sqr_comba8 a).
    { unfold sqr_comba8. rewrite <- (to_limbs_unique L (lval a * lval a) HLl Hsum). reflexivity. }
    rewrite <- EL.
    pose proof (proj1 HRm _ _ EgR) as HokR.
    destruct (kb_check_sound bgbsegs rho1 TQ_R rgE m' (kbs_ptrs (outs_of rgE)) 0 HokR Hkb ltac:(lia)) as (bs & HF & Hb & _).
    { rewrite EsR. unfold kbs_ptrs, outs_of, OUTIX, RSZ. cbn [map concat length app kbs_ptr seq]. lia. }
    unfold rbase in Hb. rewrite EaR, Hv, Z.add_0_r in Hb by (vm_compute; reflexivity). change (rho0 TQ_R) with RP in Hb.
    unfold limbs_at, L. rewrite <- (kbs_ptrs_bytes rho1 (outs_of rgE) bs); [exact Hb | | exact HF].
    eapply Forall_impl; [|exact Hrange]. intros t Ht. cbn in Ht. unfold MW in Ht. change (2 ^ 64) with 18446744073709551616. exact Ht.
  -
    destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros x Hx. destruct (S3 x Hx) as [Hwv (bb & Hbb)].
    split; [apply WM; exact Hwv|].
    destruct (Z_lt_le_dec x (SPz - CSQ)) as [Lt|Ge]; [destruct (Z_lt_le_dec x RP) as [L1|G1]; [|destruct (Z_lt_le_dec x (RP + RSZ)) as [L2|G2]]|].
    + exists bb. unfold mrd in *. rewrite MU; [exact Hbb|]. rewrite wa_unsigned by lia. unfold WIV, CSQ in *. cbn [outside]. lia.
    +
      pose proof (region_mapped bgbsegs rho1 TQ_R rgE m' (proj1 HRm _ _ EgR)) as Hmp. unfold rbase in Hmp. rewrite EaR, EsR, Hv in Hmp by (vm_compute; reflexivity).
      change (rho0 TQ_R) with RP in Hmp. destruct (Hmp (x - RP) ltac:(lia)) as [Hm' _]. replace (RP + (x - RP)) with x in Hm' by lia. exact Hm'.
    + exists bb. unfold mrd in *. rewrite MU; [exact Hbb|]. rewrite wa_unsigned by lia. unfold WIV, CSQ, RSZ in *. cbn [outside]. lia.
    + specialize (Hd1 TQ_STK). rewrite MQ_get8 in Hd1.
      destruct (mget (s_mem SE) TQ_STK) as [rg1|] eqn:Eg1; [|contradiction].
      pose proof (region_mapped bgbsegs rho1 TQ_STK rg1 m' (proj1 HRm _ _ Eg1)) as Hmp.
      rewrite (rbase_same_dir rho1 TQ_STK cq_stk rg1 Hd1) in Hmp. destruct Hd1 as (_ & Es1 & _). rewrite Es1 in Hmp.
      unfold rbase in Hmp. cbn [rg_abs rg_size cq_stk] in Hmp. rewrite Hv in Hmp by (vm_compute; reflexivity).
      change (rho0 TQ_STK) with (SPz - CSQ) in Hmp. change (to_Z CSQI) with CSQ in Hmp.
      destruct (Hmp (x - (SPz - CSQ)) ltac:(lia)) as [Hm' _].
      replace (SPz - CSQ + (x - (SPz - CSQ))) with x in Hm' by lia. exact Hm'.
Qed.

