(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Image Mem Cells Step Frame Exec MState Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common Require Import PropExec FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery HxLearn HxSym.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BgWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnWU2 Require Import SqrCalls HxSqr4Init.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW2 Require Import HxPoly2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Notation bgusegs := ImageBg.bgusegs.

Definition CSQ : Z := 96.

Definition ASZ : Z := 32.
Definition RSZ : Z := 64.
Lemma ASZ_eq : to_Z ASZI = ASZ. Proof. reflexivity. Qed.
Lemma RSZ_eq : to_Z RSZI = RSZ. Proof. reflexivity. Qed.
Lemma CSQ_eq : to_Z CSQI = CSQ. Proof. reflexivity. Qed.

Definition stopq (pc : w64) : bool := w_eqb pc PC_CQ_RET.
Definition cq_run : option (list snode * sstate) := sx_run bgusegs stopq 2500 [] SQ.

Definition TAQ : list int := [19; 20; 21; 22]%uint63.
Definition st0q : ubmap * nmap := fold_left ainput (TAQ ++ TAQ) (PositiveMap.empty Z, PositiveMap.empty ninfo).

Definition hval_eqb (a b : hval) : bool :=
  match a, b with
  | VC x, VC y => w_eqb x y
  | VP t o, VP t' o' => (t =? t')%uint63 && w_eqb o o'
  | VU, VU => true
  | _, _ => false
  end.

Lemma hval_eqb_eq (a b : hval) : hval_eqb a b = true -> a = b.
Proof.
  destruct a as [x|t o| |], b as [y|t' o'| |]; cbn; intros H; try discriminate; try reflexivity.
  - apply w_eqb_true_iff in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Uint63.eqb_spec in H1. apply w_eqb_true_iff in H2. subst. reflexivity.
Qed.

Definition final_regsq : list (rix * hval) :=
  [(X1, VP TQ_RA w_zero); (X2, VP 1%uint63 (W false CSQI)); (X3, VP TQ_GP w_zero); (X4, VP TQ_TP w_zero);
   (X8, VP TQ_S0 w_zero); (X9, VP (TQ_S0 + 1)%uint63 w_zero); (X18, VP (TQ_S0 + 2)%uint63 w_zero); (X19, VP (TQ_S0 + 3)%uint63 w_zero);
   (X20, VP (TQ_S0 + 4)%uint63 w_zero); (X21, VP (TQ_S0 + 5)%uint63 w_zero); (X22, VP (TQ_S0 + 6)%uint63 w_zero); (X23, VP (TQ_S0 + 7)%uint63 w_zero);
   (X24, VP (TQ_S0 + 8)%uint63 w_zero); (X25, VP (TQ_S0 + 9)%uint63 w_zero); (X26, VP (TQ_S0 + 10)%uint63 w_zero); (X27, VP (TQ_S0 + 11)%uint63 w_zero)].

Definition final_regs_okq (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) final_regsq.

Definition OUTIX : list int := [0; 1; 2; 3; 4; 5; 6; 7]%uint63.
Definition outs_of (rg : region) : list int :=
  map (fun k => match rd_cell bgusegs rg k with CP t _ => t | CW _ _ => 0%uint63 end) OUTIX.

Definition kbs_ptrs (tags : list int) : list kb := concat (map kbs_ptr tags).

Definition cq_ok (r : option (list snode * sstate)) : bool :=
  match r with
  | Some (log, X) =>
      w_eqb (s_pc X) PC_CQ_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_okq X
      && match mget (s_mem X) TQ_R with
         | Some rg =>
             (match rg_abs rg with None => true | Some _ => false end) && (to_Z (rg_size rg) =? RSZ)
             && kb_check bgusegs rg 0 (kbs_ptrs (outs_of rg))
             && incr_chk (to_Z NEXTQ) (rev log)
             && match arun st0q (rev log) with
                | Some st => mul_check st TAQ TAQ (outs_of rg) (MW ^ 8)
                | None => false
                end
         | None => false
         end
  | None => false
  end.

Lemma cq_ok_inv (r : option (list snode * sstate)) : cq_ok r = true ->
  exists log X rg st, r = Some (log, X) /\ s_pc X = PC_CQ_RET /\ s_resv X = RNone /\ final_regs_okq X = true
    /\ mget (s_mem X) TQ_R = Some rg /\ rg_abs rg = None /\ to_Z (rg_size rg) = RSZ
    /\ kb_check bgusegs rg 0 (kbs_ptrs (outs_of rg)) = true /\ incr_chk (to_Z NEXTQ) (rev log) = true
    /\ arun st0q (rev log) = Some st /\ mul_check st TAQ TAQ (outs_of rg) (MW ^ 8) = true.
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

Lemma cq_run_unfold : cq_run = sx_run bgusegs stopq 2500 [] SQ.
Proof. reflexivity. Qed.

Lemma cq_checked : cq_ok cq_run = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_finalq : exists ic', hx_fetch bgusegs IEmpty PC_CQ_RET = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.

Definition wr_bq (k : Z) (rg : region) : bool :=
  (k <? to_Z NEXTQ) &&
  (negb (rg_wr rg)
   || match rg_abs rg with
      | Some _ => false
      | None => ((k =? to_Z TQ_R) && (to_Z (rg_size rg) =? RSZ)) || ((k =? 1) && (to_Z (rg_size rg) =? CSQ))
      end).

Lemma MQ_checked : mem_check wr_bq MQ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma MQ_get1 : mget MQ 1%uint63 = Some cq_1.
Proof. vm_compute. reflexivity. Qed.

Lemma pword_scalar (rho : valuation) (t : int) (x : word) : rho t = bv_unsigned x -> pword rho t w_zero = x.
Proof. intros E. unfold pword. rewrite E. change (wZ w_zero) with 0. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

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

Lemma psegs_wr_rd : forall sg, In sg bgusegs -> seg_writable sg = true -> seg_readable sg = true.
Proof.
  intros sg H. unfold bgusegs, Ubsan.M.loaded_segments, Ubsan.Ubsan_loaded_segments in H.
  cbn [In] in H. repeat (destruct H as [<-|H]; [vm_compute; auto|]). destruct H.
Qed.

Lemma mapped_below (m : word -> option byte) (A n : Z) : mem_inv bgusegs m -> 0 <= A -> A + n <= 2 ^ 64 -> 0 < n ->
  (forall i, 0 <= i < n -> exists b, mrd bgusegs m (wa (A + i)) = Some b) -> A + n <= UTOP.
Proof.
  intros MI HA Hn Hpos H. destruct (H (n - 1) ltac:(lia)) as [b Hb]. pose proof (mrd_below bgusegs m _ _ MI Hb) as X.
  rewrite wa_unsigned in X by lia. lia.
Qed.

Lemma final_regs_denq (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_okq S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho TQ_RA w_zero /\ x2 = pword rho 1%uint63 (W false CSQI) /\ x3 = pword rho TQ_GP w_zero /\ x4 = pword rho TQ_TP w_zero
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

Section HandoffQ.
Variables (rho : valuation) (m : word -> option byte) (a : list Z) (AP RP lo sp0 : Z).
Hypothesis MI : mem_inv bgusegs m.
Hypothesis LA : limbs a.
Hypothesis HLA : length a = 4%nat.
Hypothesis RA : limbs_at bgusegs m AP a.
Hypothesis WR : wr_at bgusegs m RP RSZ.
Hypothesis Hr1 : rho 1%uint63 = sp0 - CSQ.
Hypothesis Hr2 : rho TQ_A = AP.
Hypothesis Hr3 : rho TQ_R = RP.
Hypothesis HrA : map rho TAQ = a.

Definition ptr_okq (p : Z) : Prop := (0 < p \/ to_Z ALQ = 0) /\ p mod 2 ^ to_Z ALQ = 0.

Lemma tags_range (tags : list int) (l : list Z) : map rho tags = l -> limbs l -> Forall (fun t => 0 <= rho t < 2 ^ 64) tags.
Proof.
  intros E HL. subst l. unfold limbs in HL. rewrite Forall_map in HL. eapply Forall_impl; [|exact HL].
  intros t Ht. cbn in Ht. unfold limb, BW in Ht. change (2 ^ 64) with 18446744073709551616. exact Ht.
Qed.

Lemma limb_region_ok (t t0 : int) (tags : list int) (A : Z) (l : list Z) :
  rho t = A -> map rho tags = l -> limbs l -> length l = 4%nat -> limbs_at bgusegs m A l -> ptr_okq A ->
  learn_check bgusegs (RG None ASZI ALQ false DUnk 3%nat (limb_cellsq t0)) [(0, kbs_ptrs tags)] 0 (Z.to_nat ASZ) = true ->
  region_ok bgusegs rho t (RG None ASZI ALQ false DUnk 3%nat (limb_cellsq t0)) m.
Proof.
  intros Er El HL Hlen Hat [Hp Hal] Hck. pose proof (limbs_at_bound bgusegs m A l Hat) as [B0 B1]. rewrite Hlen in B1.
  assert (Hmap : forall i, 0 <= i < ASZ -> exists x, mrd bgusegs m (wa (A + i)) = Some x).
  { intros i Hi. apply (bytes_at_mapped bgusegs m A (lbytes l) Hat). rewrite lbytes_lengthZ, Hlen. unfold ASZ in Hi. lia. }
  pose proof (mapped_below m A ASZ MI B0 ltac:(unfold ASZ; lia) ltac:(unfold ASZ; lia) Hmap) as HU. unfold UTOP in HU.
  apply (region_ok_learn_gen bgusegs rho t _ m [(0, kbs_ptrs tags)]); unfold rbase; cbn [rg_abs rg_size rg_d rg_al rg_wr]; rewrite ?Er, ?ASZ_eq.
  - split; [exact B0 | exact Hp].
  - unfold two63, ASZ in *. lia.
  - unfold ASZ. lia.
  - unfold ASZ. cbn. lia.
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

Lemma cq_2_ok : region_ok bgusegs rho TQ_A cq_2 m.
Proof. apply (limb_region_ok TQ_A TQ_LA TAQ AP a Hr2 HrA LA HLA RA PA). vm_compute. reflexivity. Qed.

Lemma cq_3_ok : region_ok bgusegs rho TQ_R cq_3 m.
Proof.
  pose proof WR as (W0 & W1 & Hw).
  assert (Hmap : forall i, 0 <= i < RSZ -> exists x, mrd bgusegs m (wa (RP + i)) = Some x).
  { intros i Hi. apply (wview_mrd bgusegs m _ psegs_wr_rd). apply Hw. exact Hi. }
  pose proof (mapped_below m RP RSZ MI W0 W1 ltac:(unfold RSZ; lia) Hmap) as HU. unfold UTOP in HU.
  destruct PR as [Hp Hal].
  unfold cq_3. apply region_ok_fresh_gen; unfold rbase; cbn [rg_abs rg_size]; rewrite ?Hr3, ?RSZ_eq.
  - split; [exact W0 | exact Hp].
  - unfold two63, RSZ in *. lia.
  - unfold RSZ. lia.
  - unfold RSZ. cbn. lia.
  - cbn. lia.
  - vm_compute. reflexivity.
  - exact Hal.
  - intros i Hi. split; [exact (Hmap i Hi) | intros _; exact (Hw i Hi)].
Qed.

Hypothesis STKH : stk bgusegs m lo sp0.
Hypothesis Hlo : lo <= sp0 - CSQ.

Lemma cq_1_ok : region_ok bgusegs rho 1%uint63 cq_1 m.
Proof.
  destruct STKH as (S0 & S1 & Hs). assert (HC : 0 < CSQ) by (unfold CSQ; lia). assert (HC' : CSQ < 2 ^ 20) by (unfold CSQ; lia).
  assert (Hmap : forall i, 0 <= i < CSQ -> exists x, mrd bgusegs m (wa (sp0 - CSQ + i)) = Some x).
  { intros i Hi. exact (proj2 (Hs (sp0 - CSQ + i) ltac:(lia))). }
  pose proof (mapped_below m (sp0 - CSQ) CSQ MI ltac:(lia) ltac:(lia) ltac:(lia) Hmap) as HU. unfold UTOP in HU.
  unfold cq_1. apply region_ok_fresh_gen; unfold rbase; cbn [rg_abs]; rewrite ?Hr1; change (to_Z CSQI) with CSQ; change (to_Z 0%uint63) with 0.
  - split; [lia | right; reflexivity].
  - unfold two63. lia.
  - lia.
  - unfold CSQ. cbn. lia.
  - cbn. lia.
  - lia.
  - apply Z.mod_1_r.
  - intros i Hi. split; [exact (Hmap i Hi) | intros _; exact (proj1 (Hs (sp0 - CSQ + i) ltac:(lia)))].
Qed.

Hypothesis DRA : RP + RSZ <= AP \/ AP + ASZ <= RP.
Hypothesis SEPR : RP + RSZ <= sp0 - CSQ \/ sp0 <= RP.
Hypothesis SEPA : AP + ASZ <= sp0 - CSQ \/ sp0 <= AP.

Local Ltac sepq :=
  unfold rbase; cbn [rg_abs rg_size rg_wr cq_1 cq_2 cq_3]; rewrite ?Hr1, ?Hr2, ?Hr3, ?ASZ_eq, ?RSZ_eq, ?CSQ_eq; unfold CSQ, ASZ, RSZ in *;
  repeat (constructor; [cbn [fst snd]; intros Hw; first [lia | destruct Hw as [X|X]; discriminate X]|]); constructor.

Lemma rmemq : Rmem bgusegs rho MQ m.
Proof.
  pose proof (Rmem_empty bgusegs rho m) as R0. pose proof (dir_inw_empty rho) as I0.
  destruct (Rmem_add_sepw bgusegs rho IEmpty TQ_A cq_2 m [] R0 I0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_2_ok ltac:(constructor)) as [R2 I2].
  destruct (Rmem_add_sepw bgusegs rho _ TQ_R cq_3 m _ R2 I2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_3_ok ltac:(sepq)) as [R3 I3].
  exact (proj1 (Rmem_add_sepw bgusegs rho _ 1%uint63 cq_1 m _ R3 I3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) cq_1_ok ltac:(sepq))).
Qed.

End HandoffQ.

Definition rhoq (sp0 AP RP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (a : list Z) : valuation := fun t =>
  if (t =? 1)%uint63 then sp0 - CSQ
  else if (t =? TQ_A)%uint63 then AP else if (t =? TQ_R)%uint63 then RP
  else if (t =? TQ_RA)%uint63 then bv_unsigned ra else if (t =? TQ_GP)%uint63 then bv_unsigned gp else if (t =? TQ_TP)%uint63 then bv_unsigned tp
  else if (t =? TQ_S0)%uint63 then bv_unsigned s0 else if (t =? TQ_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? TQ_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? TQ_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? TQ_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? TQ_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? TQ_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? TQ_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? TQ_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? TQ_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? TQ_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? TQ_S0 + 11)%uint63 then bv_unsigned s11
  else if ((TQ_LA <=? t) && (t <? NEXTQ))%uint63 then nth (Z.to_nat (to_Z t - to_Z TQ_LA)) a 0
  else 0.

Lemma Rregs_initq (rho : valuation) (a : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXTQ -> rho t = rhoq (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a0) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a t) ->
  CSQ <= bv_unsigned sp ->
  Rregs rho regsq (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho Hsp r.
  assert (Esp : pword rho 1%uint63 (W false CSQI) = sp).
  { unfold pword. rewrite (Hrho 1%uint63) by (vm_compute; reflexivity).
    change (rhoq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1%uint63) with (bv_unsigned sp - CSQ).
    change (wZ (W false CSQI)) with CSQ. replace (bv_unsigned sp - CSQ + CSQ) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

Lemma tags_small : forallb (fun t => (to_Z t <? to_Z NEXTQ)) (TAQ ++ TAQ) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sqr_comba4_ok : sqr_comba4_spec CSQ.
Proof.
  unfold sqr_comba4_spec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a lo
         LA HLA RA WR DRA Hstk Hlo SEPR SEPA Hmi UR UA.
  set (SPz := bv_unsigned sp) in *. set (RP := bv_unsigned a0) in *. set (AP := bv_unsigned a1) in *.
  set (rho0 := rhoq SPz AP RP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a).
  set (WIV := [(RP, RP + 8 * 8); (SPz - CSQ, SPz)]).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x106eac) fc None m (seg_rom bgusegs)).
  assert (HspC : CSQ <= SPz) by (destruct Hstk as (S0 & _); lia).

  assert (PA : ptr_okq AP) by (first [ split; [right; reflexivity | apply Z.mod_1_r] | destruct (UA ltac:(lia)) as [? ?]; split; [left; assumption | assumption] ]).
  assert (PR : ptr_okq RP) by (first [ split; [right; reflexivity | apply Z.mod_1_r] | destruct (UR ltac:(lia)) as [? ?]; split; [left; assumption | assumption] ]).

  assert (HA0 : map rho0 TAQ = a).
  { destruct a as [|x0 [|x1 [|x2 [|x3 [|]]]]]; try discriminate HLA. reflexivity. }

  destruct (cq_ok_inv cq_run cq_checked) as (logE & SE & rgE & stE & Erun & Epc & Erv & Hregs & EgR & EaR & EsR & Hkb & Hincr & Harun & Hchk).
  rewrite cq_run_unfold in Erun.
  assert (Hmaps : forall rho2, (forall t, to_Z t < to_Z NEXTQ -> rho2 t = rho0 t) -> map rho2 TAQ = a).
  { intros rho2 Hr. rewrite <- HA0. unfold TAQ. cbn [map]. rewrite !Hr by (vm_compute; reflexivity). reflexivity. }

  assert (HRn0 : Rn bgusegs rho0 SQ ms0).
  { intros rho2 Hag. cbn [SQ s_next] in Hag.
    assert (Hrho : forall t, to_Z t < to_Z NEXTQ -> rho2 t = rho0 t) by exact Hag.
    pose proof (Hmaps rho2 Hrho) as HA2.
    unfold R, ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS SQ s_pc s_regs s_resv s_mem].
    split; [reflexivity|]. split; [reflexivity|]. split.
    { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply Rregs_initq; [exact Hrho | exact HspC]. }
    split; [reflexivity|].
    apply (rmemq rho2 m a AP RP lo SPz Hmi LA HLA RA WR); try assumption;
      first [ exact (Hrho 1%uint63 ltac:(vm_compute; reflexivity)) | exact (Hrho TQ_A ltac:(vm_compute; reflexivity))
            | exact (Hrho TQ_R ltac:(vm_compute; reflexivity)) ]. }

  assert (HC0 : CInv bgusegs MQ WIV m F fc SQ ms0).
  { unfold CInv, ms0. cbn [SQ s_mem ms_mem ms_fregs ms_fcsr ms_rom ms_regs MS].
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hmi|].
    repeat (split; [reflexivity|]). do 31 eexists. reflexivity. }
  assert (HP : forall rho, agree_below NEXTQ rho0 rho -> sx_pres bgusegs rho (CInv bgusegs MQ WIV m F fc)).
  { intros rho Hag. apply CInv_sx. intros t rg G Hw. pose proof (mem_check_ok wr_bq MQ MQ_checked t rg G) as H. unfold wr_bq in H.
    rewrite Hw in H. cbn [negb orb] in H. apply andb_prop in H as [_ H]. unfold rbase. destruct (rg_abs rg) as [x|]; [discriminate|].
    apply orb_prop in H as [H|H]; apply andb_prop in H as [E1 E2]; apply Z.eqb_eq in E1, E2; rewrite E2.
    - assert (t = TQ_R) by (apply to_Z_inj; exact E1). subst t. rewrite (Hag TQ_R) by (vm_compute; reflexivity).
      change (rho0 TQ_R) with RP. unfold WIV, RSZ. cbn [inside]. left. lia.
    - assert (t = 1%uint63) by (apply to_Z_inj; exact E1). subst t. rewrite (Hag 1%uint63) by (vm_compute; reflexivity).
      change (rho0 1%uint63) with (SPz - CSQ). unfold WIV, CSQ. cbn [inside]. right. left. lia. }
  destruct (sx_run_sound bgusegs stopq (CInv bgusegs MQ WIV m F fc) NEXTQ rho0 HP 2500 rho0 [] logE SQ SE ms0
              (agree_below_refl _ _) ltac:(cbn [SQ s_next]; lia) HRn0 HC0 (Forall_nil _) (Forall_nil _) Erun)
    as (rho1 & ms1 & Hag1 & Hms & HRn1 & HC1 & Hlog1 & _).
  cbn [SQ s_next] in Hag1.
  assert (Hv : forall t, to_Z t < to_Z NEXTQ -> rho1 t = rho0 t) by exact Hag1.

  pose proof (Rn_R bgusegs rho1 SE ms1 HRn1) as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_finalq as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step bgusegs rho1 IEmpty ic' SE ms1 (ic_ok_empty bgusegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_trans bgusegs _ _ _ Hms (msteps_one bgusegs _ _ Hstep))|].
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
  { rewrite E2. unfold pword. rewrite Hv by (vm_compute; reflexivity). change (rho0 1%uint63) with (SPz - CSQ). change (wZ (W false CSQI)) with CSQ.
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
    assert (Hlt : hsum (map rho1 TAQ) * hsum (map rho1 TAQ) < (MW ^ 8)).
    { rewrite HA1, !hsum_lval. pose proof (lval_bound a LA) as H1. rewrite HLA in H1.
      change (MW ^ 8) with (Bp 4 * Bp 4). clear -H1. nia. }
    destruct (mul_cert rho1 (rev logE) TAQ TAQ (outs_of rgE) (to_Z NEXTQ) (MW ^ 8) stE (Forall_rev Hlog1) Hin Hincr Harun Hchk ltac:(vm_compute; reflexivity) Hlt) as [Hsum Hrange].
    rewrite HA1, !hsum_lval in Hsum.
    set (L := map rho1 (outs_of rgE)) in *.
    assert (HLl : limbs L).
    { unfold L, limbs. rewrite Forall_map. eapply Forall_impl; [|exact Hrange]. intros t Ht. cbn in Ht. unfold limb, BW. unfold MW in Ht. exact Ht. }
    assert (EL : L = sqr_comba4 a).
    { unfold sqr_comba4. rewrite <- (to_limbs_unique L (lval a * lval a) HLl Hsum). reflexivity. }
    rewrite <- EL.
    pose proof (proj1 HRm _ _ EgR) as HokR.
    destruct (kb_check_sound bgusegs rho1 TQ_R rgE m' (kbs_ptrs (outs_of rgE)) 0 HokR Hkb ltac:(lia)) as (bs & HF & Hb & _).
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
      pose proof (region_mapped bgusegs rho1 TQ_R rgE m' (proj1 HRm _ _ EgR)) as Hmp. unfold rbase in Hmp. rewrite EaR, EsR, Hv in Hmp by (vm_compute; reflexivity).
      change (rho0 TQ_R) with RP in Hmp. destruct (Hmp (x - RP) ltac:(lia)) as [Hm' _]. replace (RP + (x - RP)) with x in Hm' by lia. exact Hm'.
    + exists bb. unfold mrd in *. rewrite MU; [exact Hbb|]. rewrite wa_unsigned by lia. unfold WIV, CSQ, RSZ in *. cbn [outside]. lia.
    + specialize (Hd1 1%uint63). rewrite MQ_get1 in Hd1.
      destruct (mget (s_mem SE) 1%uint63) as [rg1|] eqn:Eg1; [|contradiction].
      pose proof (region_mapped bgusegs rho1 1%uint63 rg1 m' (proj1 HRm _ _ Eg1)) as Hmp.
      rewrite (rbase_same_dir rho1 1%uint63 cq_1 rg1 Hd1) in Hmp. destruct Hd1 as (_ & Es1 & _). rewrite Es1 in Hmp.
      unfold rbase in Hmp. cbn [rg_abs rg_size cq_1] in Hmp. rewrite Hv in Hmp by (vm_compute; reflexivity).
      change (rho0 1%uint63) with (SPz - CSQ) in Hmp. change (to_Z CSQI) with CSQ in Hmp.
      destruct (Hmp (x - (SPz - CSQ)) ltac:(lia)) as [Hm' _].
      replace (SPz - CSQ + (x - (SPz - CSQ))) with x in Hm' by lia. exact Hm'.
Qed.

