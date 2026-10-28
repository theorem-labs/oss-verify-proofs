(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA Mem Cells Step Frame Exec MState Arr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common Require Import PropExec FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxStep HxStepSound HxRunSound HxHook HxHookSound HxToolkit HxGlue HxQuery HxLearn HxSym HxPoly.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXS Require Import HxsStep HxsStepSound HxsHook HxsHookSound HxsKit HxsSym.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnKaraCorrect.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnMem W_mul_normal BnCalls.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.HXB Require Import HxaImage HxaInv HxaHooks HxaComba8Init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition CS8A : Z := 592.

(* [comment removed for export] *)
Definition comba8_aspec (CS8 : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a b : list Z) (lo : Z),
    limbs a -> limbs b -> length a = 8%nat -> length b = 8%nat ->
    limbs_at bsegs m (bv_unsigned a1) a -> limbs_at bsegs m (bv_unsigned a2) b ->
    wr_at bsegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned a2 \/ bv_unsigned a2 + 64 <= bv_unsigned a0)%Z ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS8)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    (bv_unsigned a2 + 64 <= bv_unsigned sp - CS8 \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
    mem_inv bsegs m ->
    shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m ->
    acc bsegs m (bv_unsigned a0) 128 -> acc bsegs m (bv_unsigned a1) 64 -> acc bsegs m (bv_unsigned a2) 64 ->
    aptrs3 (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) 16 lo ->
    (0 < bv_unsigned a0)%Z -> (0 < bv_unsigned a1)%Z -> (0 < bv_unsigned a2)%Z ->
    (bv_unsigned a0 + 128 <= 65536 \/ 12570624 <= bv_unsigned a0)%Z ->
    evt bsegs (W_mul_normal.vl_post bsegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS8 (mul_comba8 a b) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x226a50) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition stop8 (pc : w64) : bool := w_eqb pc PC_C8A_RET.
(* [comment removed for export] *)
Definition FUEL8 : nat := 3500.
Definition c8_run : option (list snode * sstate) := sxs_run SHBW bsegs stop8 FUEL8 [] S8A.

Definition TA8 : list int := [40; 41; 42; 43; 44; 45; 46; 47]%uint63.
Definition TB8 : list int := [48; 49; 50; 51; 52; 53; 54; 55]%uint63.
Definition st08 : ubmap * nmap := fold_left ainput (TA8 ++ TB8) (PositiveMap.empty Z, PositiveMap.empty ninfo).

(* [comment removed for export] *)
Definition final_regs8 : list (rix * hval) :=
  [(X1, VP T8_RA w_zero); (X2, VP T8_STK (W false CS8AI)); (X3, VP T8_GP w_zero); (X4, VP T8_TP w_zero);
   (X8, VP T8_S0 w_zero); (X9, VP (T8_S0 + 1)%uint63 w_zero); (X18, VP (T8_S0 + 2)%uint63 w_zero); (X19, VP (T8_S0 + 3)%uint63 w_zero);
   (X20, VP (T8_S0 + 4)%uint63 w_zero); (X21, VP (T8_S0 + 5)%uint63 w_zero); (X22, VP (T8_S0 + 6)%uint63 w_zero); (X23, VP (T8_S0 + 7)%uint63 w_zero);
   (X24, VP (T8_S0 + 8)%uint63 w_zero); (X25, VP (T8_S0 + 9)%uint63 w_zero); (X26, VP (T8_S0 + 10)%uint63 w_zero); (X27, VP (T8_S0 + 11)%uint63 w_zero)].

Definition final_regs_ok8 (S : sstate) : bool := forallb (fun rv => hval_eqb (rget S (fst rv)) (snd rv)) final_regs8.

(* [comment removed for export] *)
Definition outs_of (rg : region) : list int :=
  map (fun k => match rd_cell bsegs rg k with CP t _ => t | CW _ _ => 0%uint63 end) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%uint63.

Definition kbs_ptrs (tags : list int) : list kb := concat (map kbs_ptr tags).

Definition c8_ok (r : option (list snode * sstate)) : bool :=
  match r with
  | Some (log, X) =>
      w_eqb (s_pc X) PC_C8A_RET && (match s_resv X with RNone => true | _ => false end) && final_regs_ok8 X
      && match mget (s_mem X) T8_R with
         | Some rg =>
             (match rg_abs rg with None => true | Some _ => false end) && (to_Z (rg_size rg) =? 128)
             && kb_check bsegs rg 0 (kbs_ptrs (outs_of rg))
             && incr_chk 56 (rev log)
             && match arun st08 (rev log) with
                | Some st => mul_check st TA8 TB8 (outs_of rg) (MW ^ 16)
                | None => false
                end
         | None => false
         end
  | None => false
  end.

Lemma c8_ok_inv (r : option (list snode * sstate)) : c8_ok r = true ->
  exists log X rg st, r = Some (log, X) /\ s_pc X = PC_C8A_RET /\ s_resv X = RNone /\ final_regs_ok8 X = true
    /\ mget (s_mem X) T8_R = Some rg /\ rg_abs rg = None /\ to_Z (rg_size rg) = 128
    /\ kb_check bsegs rg 0 (kbs_ptrs (outs_of rg)) = true /\ incr_chk 56 (rev log) = true
    /\ arun st08 (rev log) = Some st /\ mul_check st TA8 TB8 (outs_of rg) (MW ^ 16) = true.
Proof.
  destruct r as [[log X]|]; cbn [c8_ok]; [|discriminate]. intros H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  destruct (mget (s_mem X) T8_R) as [rg|] eqn:Eg; [|discriminate].
  apply andb_prop in H4 as [H4 H9]. apply andb_prop in H4 as [H4 H8]. apply andb_prop in H4 as [H4 H7]. apply andb_prop in H4 as [H5 H6].
  destruct (arun st08 (rev log)) as [st|] eqn:Ea; [|discriminate].
  exists log, X, rg, st. split; [reflexivity|]. split; [apply w_eqb_true_iff; exact H1|].
  split; [destruct (s_resv X); [reflexivity | discriminate | discriminate]|]. split; [exact H3|]. split; [exact Eg|].
  split; [destruct (rg_abs rg); [discriminate | reflexivity]|]. split; [apply Z.eqb_eq; exact H6|]. auto.
Qed.

Lemma c8_run_unfold : c8_run = sxs_run SHBW bsegs stop8 FUEL8 [] S8A.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c8_checked : c8_ok c8_run = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_final8 : exists ic', hx_fetch bsegs IEmpty PC_C8A_RET = Some (DJalr X0 X1 w_zero, ic').
Proof. eexists. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition dir_b8 (k : Z) (rg : region) : bool :=
  (k <? 10) &&
  match rg_abs rg with
  | Some _ => negb (rg_wr rg) && ((k =? 1) || (k =? 9))
  | None => ((k =? 2) && negb (rg_wr rg)) || ((k =? 3) && negb (rg_wr rg)) || ((k =? 4) && negb (rg_wr rg)) || ((k =? 5) && negb (rg_wr rg))
            || ((k =? 6) && (to_Z (rg_size rg) =? 128)) || ((k =? 7) && negb (rg_wr rg)) || ((k =? 8) && (to_Z (rg_size rg) =? CS8A))
  end.

Lemma M8A_checked : mem_check dir_b8 M8A = true.
Proof. vm_compute. reflexivity. Qed.

Lemma M8A_get8 : mget M8A T8_STK = Some c8_stk.
Proof. vm_compute. reflexivity. Qed.

Lemma M8A_class (t : int) (rg : region) : mget M8A t = Some rg ->
  match rg_abs rg with
  | Some _ => rg_wr rg = false
  | None => (rg_wr rg = true -> (t = T8_R /\ to_Z (rg_size rg) = 128) \/ (t = T8_STK /\ to_Z (rg_size rg) = CS8A))
            /\ (tag_even t = false -> t = 3%uint63 \/ t = 5%uint63 \/ t = 7%uint63)
  end.
Proof.
  intros G. pose proof (mem_check_ok dir_b8 M8A M8A_checked t rg G) as H. unfold dir_b8 in H. apply andb_prop in H as [_ H].
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma hsum_lval (l : list Z) : hsum l = lval l.
Proof. induction l as [|x l IH]; cbn [hsum lval]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Lemma mapped_below (m : word -> option byte) (A n : Z) : mem_inv bsegs m -> 0 <= A -> A + n <= 2 ^ 64 -> 0 < n ->
  (forall i, 0 <= i < n -> exists b, mrd bsegs m (wa (A + i)) = Some b) -> A + n <= UTOP.
Proof.
  intros MI HA Hn Hpos H. destruct (H (n - 1) ltac:(lia)) as [b Hb]. pose proof (mrd_below bsegs m _ _ MI Hb) as X.
  rewrite wa_unsigned in X by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma acc_zero_bytes (m : word -> option byte) (p n : Z) : p mod 8 = 0 -> acc bsegs m p n -> 0 < n -> n mod 8 = 0 ->
  bytes_at bsegs m (shad p) (repeat z8 (Z.to_nat (n / 8))).
Proof.
  intros Hp Hacc Hn Hn8.
  assert (G : forall i, 0 <= i < n / 8 -> bytes_at bsegs m (shad p + i) [z8]).
  { intros i Hi. rewrite <- (shad_add8 p i). apply (acc_gran0 bsegs m p n (p + 8 * i) Hacc); Z.div_mod_to_equations; lia. }
  split; [|split].
  - destruct (G 0 ltac:(Z.div_mod_to_equations; lia)) as (B0 & _ & _). lia.
  - rewrite repeat_length, Z2Nat.id by (Z.div_mod_to_equations; lia).
    destruct (G (n / 8 - 1) ltac:(Z.div_mod_to_equations; lia)) as (_ & B1 & _). cbn [length Z.of_nat Pos.of_succ_nat] in B1. lia.
  - intros k Hk. rewrite repeat_length in Hk. rewrite nth_error_repeat by exact Hk.
    destruct (G (Z.of_nat k) ltac:(lia)) as (_ & _ & B). specialize (B 0%nat ltac:(cbn; lia)). cbn [nth_error Z.of_nat] in B.
    rewrite Z.add_0_r in B. exact B.
Qed.

(* [comment removed for export] *)
Lemma final_regs_den8 (rho : valuation) (S : sstate) (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) :
  final_regs_ok8 S = true ->
  Rregs rho (s_regs S) (Core (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv) ->
  x1 = pword rho T8_RA w_zero /\ x2 = pword rho T8_STK (W false CS8AI) /\ x3 = pword rho T8_GP w_zero /\ x4 = pword rho T8_TP w_zero
  /\ x8 = pword rho T8_S0 w_zero /\ x9 = pword rho (T8_S0 + 1)%uint63 w_zero /\ x18 = pword rho (T8_S0 + 2)%uint63 w_zero
  /\ x19 = pword rho (T8_S0 + 3)%uint63 w_zero /\ x20 = pword rho (T8_S0 + 4)%uint63 w_zero /\ x21 = pword rho (T8_S0 + 5)%uint63 w_zero
  /\ x22 = pword rho (T8_S0 + 6)%uint63 w_zero /\ x23 = pword rho (T8_S0 + 7)%uint63 w_zero /\ x24 = pword rho (T8_S0 + 8)%uint63 w_zero
  /\ x25 = pword rho (T8_S0 + 9)%uint63 w_zero /\ x26 = pword rho (T8_S0 + 10)%uint63 w_zero /\ x27 = pword rho (T8_S0 + 11)%uint63 w_zero.
Proof.
  intros Hok HR. unfold final_regs_ok8, final_regs8 in Hok. cbn [forallb fst snd] in Hok.
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac closed_side := first [ vm_compute; reflexivity | apply Z.leb_le; vm_compute; reflexivity | vm_compute; discriminate ].

(* [comment removed for export] *)
Lemma c8_le8 (m : word -> option byte) (A : Z) (w : word) : ro_cells bsegs m A [C8 w] -> bytes_at bsegs m A (le8 w).
Proof. intros [_ B1]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1. Qed.

Section Handoff8.
Variables (rho : valuation) (m : word -> option byte) (a b : list Z) (AP BP RP lo sp0 : Z).
Hypothesis MI : mem_inv bsegs m.
Hypothesis LA : limbs a.
Hypothesis LB : limbs b.
Hypothesis HLA : length a = 8%nat.
Hypothesis HLB : length b = 8%nat.
Hypothesis RA : limbs_at bsegs m AP a.
Hypothesis RB : limbs_at bsegs m BP b.
Hypothesis WR : wr_at bsegs m RP 128.
Hypothesis Hr8 : rho T8_STK = sp0 - CS8A.
Hypothesis Hr2 : rho T8_A = AP.
Hypothesis Hr3 : rho 3%uint63 = shad AP.
Hypothesis Hr4 : rho T8_B = BP.
Hypothesis Hr5 : rho 5%uint63 = shad BP.
Hypothesis Hr6 : rho T8_R = RP.
Hypothesis Hr7 : rho 7%uint63 = shad RP.
Hypothesis HrA : map rho TA8 = a.
Hypothesis HrB : map rho TB8 = b.
Hypothesis SHBC : shb_cells bsegs g_GOT_shadow_offset_cell g_shadow_memory_dynamic_address m.
Hypothesis ACR : acc bsegs m RP 128.
Hypothesis ACA : acc bsegs m AP 64.
Hypothesis ACB : acc bsegs m BP 64.

(* [comment removed for export] *)
Definition ptr_ok8 (p : Z) : Prop := 0 < p /\ p mod 2 ^ to_Z AL8A = 0.

Lemma tags_range (tags : list int) (l : list Z) : map rho tags = l -> limbs l -> Forall (fun t => 0 <= rho t < 2 ^ 64) tags.
Proof.
  intros E HL. subst l. unfold limbs in HL. rewrite Forall_map in HL. eapply Forall_impl; [|exact HL].
  intros t Ht. cbn in Ht. unfold limb, BW in Ht. change (2 ^ 64) with 18446744073709551616. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma c8_got_ok : region_ok bsegs rho T8_GOT c8_got m.
Proof.
  destruct SHBC as [C1 _].
  apply (static_region_ok bsegs rho T8_GOT c8_got m GOT_SHB_CELL (kbs_Z 8 (to_Z SHB_CELL)) (le8 (Z_to_bv 64 g_shadow_memory_dynamic_address)) eq_refl eq_refl);
    [closed_side | apply kbs_Z_intro; closed_side | exact (c8_le8 m _ _ C1) | closed_side | closed_side].
Qed.

Lemma c8_shb_ok : region_ok bsegs rho T8_SHB c8_shb m.
Proof.
  destruct SHBC as [_ C2].
  apply (static_region_ok bsegs rho T8_SHB c8_shb m SHB_CELL (kbs_Z 8 SHB) (le8 (Z_to_bv 64 SHB)) eq_refl eq_refl);
    [closed_side | apply kbs_Z_intro; closed_side | exact (c8_le8 m _ _ C2) | closed_side | closed_side].
Qed.

(* [comment removed for export] *)
Lemma limb_region_ok (t t0 : int) (tags : list int) (A : Z) (l : list Z) :
  rho t = A -> map rho tags = l -> limbs l -> length l = 8%nat -> limbs_at bsegs m A l -> ptr_ok8 A ->
  learn_check bsegs (RG None 64 AL8A false DUnk 3%nat (limb_cells t0)) [(0, kbs_ptrs tags)] 0 64 = true ->
  region_ok bsegs rho t (RG None 64 AL8A false DUnk 3%nat (limb_cells t0)) m.
Proof.
  intros Er El HL Hlen Hat [Hp Hal] Hck. pose proof (limbs_at_bound bsegs m A l Hat) as [B0 B1]. rewrite Hlen in B1.
  assert (Hmap : forall i, 0 <= i < 64 -> exists x, mrd bsegs m (wa (A + i)) = Some x).
  { intros i Hi. apply (bytes_at_mapped bsegs m A (lbytes l) Hat). rewrite lbytes_lengthZ, Hlen. lia. }
  pose proof (mapped_below m A 64 MI B0 ltac:(lia) ltac:(lia) Hmap) as HU. unfold UTOP in HU.
  apply (region_ok_learn_gen bsegs rho t _ m [(0, kbs_ptrs tags)]); unfold rbase; cbn [rg_abs rg_size rg_d rg_al rg_wr]; rewrite ?Er;
    change (to_Z 64%uint63) with 64.
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

Hypothesis PA : ptr_ok8 AP.
Hypothesis PB : ptr_ok8 BP.
Hypothesis PR : ptr_ok8 RP.

Lemma c8_a_ok : region_ok bsegs rho T8_A c8_a m.
Proof. apply (limb_region_ok T8_A T8_LA TA8 AP a Hr2 HrA LA HLA RA PA). vm_compute. reflexivity. Qed.

Lemma c8_b_ok : region_ok bsegs rho T8_B c8_b m.
Proof. apply (limb_region_ok T8_B T8_LB TB8 BP b Hr4 HrB LB HLB RB PB). vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma AP_hi : AP + 64 <= UTOP.
Proof.
  pose proof (limbs_at_bound bsegs m AP a RA) as [B0 B1]. rewrite HLA in B1.
  apply (mapped_below m AP 64 MI B0 ltac:(lia) ltac:(lia)). intros i Hi. apply (bytes_at_mapped bsegs m AP (lbytes a) RA). rewrite lbytes_lengthZ, HLA. lia.
Qed.
Lemma BP_hi : BP + 64 <= UTOP.
Proof.
  pose proof (limbs_at_bound bsegs m BP b RB) as [B0 B1]. rewrite HLB in B1.
  apply (mapped_below m BP 64 MI B0 ltac:(lia) ltac:(lia)). intros i Hi. apply (bytes_at_mapped bsegs m BP (lbytes b) RB). rewrite lbytes_lengthZ, HLB. lia.
Qed.
Lemma RP_hi : RP + 128 <= UTOP.
Proof.
  destruct WR as (W0 & W1 & Hw). apply (mapped_below m RP 128 MI W0 W1 ltac:(lia)).
  intros i Hi. apply (wview_mrd bsegs m _ asegs_wr_rd). apply Hw. exact Hi.
Qed.

Lemma c8_r_ok : region_ok bsegs rho T8_R c8_r m.
Proof.
  pose proof RP_hi as HU. unfold UTOP in HU. destruct PR as [Hp Hal]. unfold c8_r.
  apply (fresh_region_ok rho T8_R 128 AL8A true m RP Hr6 Hp); change (to_Z 128%uint63) with 128; [unfold two63; lia | lia | closed_side | exact Hal | exact WR].
Qed.

(* [comment removed for export] *)
Lemma c8_ash_ok : region_ok bsegs rho 3%uint63 c8_ash m.
Proof.
  pose proof AP_hi as HU. unfold UTOP in HU. destruct PA as [Hp Hal]. change (2 ^ to_Z AL8A) with 8 in Hal.
  pose proof (AsKit.shad_range AP ltac:(lia)) as SR. unfold SHLO, SHHI in SR. unfold c8_ash.
  apply (zero_region_ok rho 3%uint63 8 m (shad AP) Hr3); change (to_Z 8%uint63) with 8; [lia | unfold two63; lia | lia |].
  change (Z.to_nat 8) with (Z.to_nat (64 / 8)). exact (acc_zero_bytes m AP 64 Hal ACA ltac:(lia) eq_refl).
Qed.
Lemma c8_bsh_ok : region_ok bsegs rho 5%uint63 c8_bsh m.
Proof.
  pose proof BP_hi as HU. unfold UTOP in HU. destruct PB as [Hp Hal]. change (2 ^ to_Z AL8A) with 8 in Hal.
  pose proof (AsKit.shad_range BP ltac:(lia)) as SR. unfold SHLO, SHHI in SR. unfold c8_bsh.
  apply (zero_region_ok rho 5%uint63 8 m (shad BP) Hr5); change (to_Z 8%uint63) with 8; [lia | unfold two63; lia | lia |].
  change (Z.to_nat 8) with (Z.to_nat (64 / 8)). exact (acc_zero_bytes m BP 64 Hal ACB ltac:(lia) eq_refl).
Qed.
Lemma c8_rsh_ok : region_ok bsegs rho 7%uint63 c8_rsh m.
Proof.
  pose proof RP_hi as HU. unfold UTOP in HU. destruct PR as [Hp Hal]. change (2 ^ to_Z AL8A) with 8 in Hal.
  pose proof (AsKit.shad_range RP ltac:(lia)) as SR. unfold SHLO, SHHI in SR. unfold c8_rsh.
  apply (zero_region_ok rho 7%uint63 16 m (shad RP) Hr7); change (to_Z 16%uint63) with 16; [lia | unfold two63; lia | lia |].
  change (Z.to_nat 16) with (Z.to_nat (128 / 8)). exact (acc_zero_bytes m RP 128 Hal ACR ltac:(lia) eq_refl).
Qed.

Hypothesis STKH : stk bsegs m lo sp0.
Hypothesis Hlo : lo <= sp0 - CS8A.
Hypothesis LOHI : SHHI <= lo.

Lemma c8_stk_ok : region_ok bsegs rho T8_STK c8_stk m.
Proof.
  destruct STKH as (S0 & S1 & Hs). unfold SHHI in LOHI.
  assert (Hmap : forall i, 0 <= i < CS8A -> exists x, mrd bsegs m (wa (sp0 - CS8A + i)) = Some x).
  { intros i Hi. exact (proj2 (Hs (sp0 - CS8A + i) ltac:(unfold CS8A in *; lia))). }
  pose proof (mapped_below m (sp0 - CS8A) CS8A MI ltac:(unfold CS8A in *; lia) ltac:(unfold CS8A in *; lia) ltac:(unfold CS8A; lia) Hmap) as HU. unfold UTOP in HU.
  assert (W : wr_at bsegs m (sp0 - CS8A) (to_Z CS8AI)).
  { change (to_Z CS8AI) with CS8A. split; [unfold CS8A in *; lia|]. split; [unfold CS8A in *; lia|]. intros i Hi. exact (proj1 (Hs (sp0 - CS8A + i) ltac:(unfold CS8A in *; lia))). }
  unfold c8_stk. apply (fresh_region_ok rho T8_STK CS8AI 0 true m (sp0 - CS8A) Hr8); change (to_Z CS8AI) with CS8A; unfold CS8A in *;
    [lia | unfold two63; lia | lia | closed_side | apply Z.mod_1_r | exact W].
Qed.

Hypothesis DRA : RP + 128 <= AP \/ AP + 64 <= RP.
Hypothesis DRB : RP + 128 <= BP \/ BP + 64 <= RP.
Hypothesis SEPR : RP + 128 <= sp0 - CS8A \/ sp0 <= RP.
Hypothesis SEPA : AP + 64 <= sp0 - CS8A \/ sp0 <= AP.
Hypothesis SEPB : BP + 64 <= sp0 - CS8A \/ sp0 <= BP.
Hypothesis OFFR : RP + 8 * 16 <= SHLO \/ SHHI <= RP.
Hypothesis RIMG : RP + 128 <= 65536 \/ 12570624 <= RP.

Local Ltac sep8 :=
  unfold rbase; cbn [rg_abs rg_size rg_wr c8_got c8_shb c8_a c8_ash c8_b c8_bsh c8_r c8_rsh c8_stk shadow_region]; rewrite ?Hr8, ?Hr2, ?Hr3, ?Hr4, ?Hr5, ?Hr6, ?Hr7;
  change (to_Z 64%uint63) with 64; change (to_Z 128%uint63) with 128; change (to_Z 8%uint63) with 8; change (to_Z 16%uint63) with 16;
  change (to_Z CS8AI) with CS8A; change (to_Z GOT_SHB_CELL) with 6163672; change (to_Z SHB_CELL) with 6961656; unfold CS8A in *;
  repeat (constructor; [cbn [fst snd]; intros Hw; first [lia | unfold shad, SHB in *; Z.div_mod_to_equations; lia | destruct Hw as [X|X]; discriminate X]|]); constructor.

Lemma rmem8 : Rmem bsegs rho M8A m.
Proof.
  pose proof AP_hi as HUA. pose proof BP_hi as HUB. pose proof RP_hi as HUR. unfold UTOP in HUA, HUB, HUR.
  pose proof PA as [PA0 _]. pose proof PB as [PB0 _]. pose proof PR as [PR0 _].
  unfold SHLO, SHHI in OFFR, LOHI.
  pose proof (Rmem_empty bsegs rho m) as R0. pose proof (dir_inw_empty rho) as I0.
  destruct (Rmem_add_sepw bsegs rho IEmpty T8_GOT c8_got m [] R0 I0 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_got_ok ltac:(constructor)) as [R1 I1].
  destruct (Rmem_add_sepw bsegs rho _ T8_SHB c8_shb m _ R1 I1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_shb_ok ltac:(sep8)) as [R2 I2].
  destruct (Rmem_add_sepw bsegs rho _ T8_A c8_a m _ R2 I2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_a_ok ltac:(sep8)) as [R3 I3].
  destruct (Rmem_add_sepw bsegs rho _ 3%uint63 c8_ash m _ R3 I3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_ash_ok ltac:(sep8)) as [R4 I4].
  destruct (Rmem_add_sepw bsegs rho _ T8_B c8_b m _ R4 I4 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_b_ok ltac:(sep8)) as [R5 I5].
  destruct (Rmem_add_sepw bsegs rho _ 5%uint63 c8_bsh m _ R5 I5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_bsh_ok ltac:(sep8)) as [R6 I6].
  destruct (Rmem_add_sepw bsegs rho _ 7%uint63 c8_rsh m _ R6 I6 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_rsh_ok ltac:(sep8)) as [R7 I7].
  destruct (Rmem_add_sepw bsegs rho _ T8_R c8_r m _ R7 I7 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_r_ok ltac:(sep8)) as [R8 I8].
  exact (proj1 (Rmem_add_sepw bsegs rho _ T8_STK c8_stk m _ R8 I8 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) c8_stk_ok ltac:(sep8))).
Qed.

End Handoff8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rho8A (sp0 AP BP RP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (a b : list Z) : valuation := fun t =>
  if (t =? T8_STK)%uint63 then sp0 - CS8A
  else if (t =? T8_A)%uint63 then AP else if (t =? 3)%uint63 then shad AP
  else if (t =? T8_B)%uint63 then BP else if (t =? 5)%uint63 then shad BP
  else if (t =? T8_R)%uint63 then RP else if (t =? 7)%uint63 then shad RP
  else if (t =? T8_RA)%uint63 then bv_unsigned ra else if (t =? T8_GP)%uint63 then bv_unsigned gp else if (t =? T8_TP)%uint63 then bv_unsigned tp
  else if (t =? T8_S0)%uint63 then bv_unsigned s0 else if (t =? T8_S0 + 1)%uint63 then bv_unsigned s1
  else if (t =? T8_S0 + 2)%uint63 then bv_unsigned s2 else if (t =? T8_S0 + 3)%uint63 then bv_unsigned s3
  else if (t =? T8_S0 + 4)%uint63 then bv_unsigned s4 else if (t =? T8_S0 + 5)%uint63 then bv_unsigned s5
  else if (t =? T8_S0 + 6)%uint63 then bv_unsigned s6 else if (t =? T8_S0 + 7)%uint63 then bv_unsigned s7
  else if (t =? T8_S0 + 8)%uint63 then bv_unsigned s8 else if (t =? T8_S0 + 9)%uint63 then bv_unsigned s9
  else if (t =? T8_S0 + 10)%uint63 then bv_unsigned s10 else if (t =? T8_S0 + 11)%uint63 then bv_unsigned s11
  else if ((T8_LA <=? t) && (t <? T8_LB))%uint63 then nth (Z.to_nat (to_Z t - 40)) a 0
  else if ((T8_LB <=? t) && (t <? NEXT8A))%uint63 then nth (Z.to_nat (to_Z t - 48)) b 0
  else 0.

Lemma Rregs_init8 (rho : valuation) (a b : list Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word) :
  (forall t, to_Z t < to_Z NEXT8A -> rho t = rho8A (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a0) ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a b t) ->
  CS8A <= bv_unsigned sp ->
  Rregs rho regs8A (Core (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F pc fc rv).
Proof.
  intros Hrho Hsp r.
  assert (Esp : pword rho T8_STK (W false CS8AI) = sp).
  { unfold pword. rewrite (Hrho T8_STK) by (vm_compute; reflexivity).
    change (rho8A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T8_STK) with (bv_unsigned sp - CS8A).
    change (wZ (W false CS8AI)) with CS8A. replace (bv_unsigned sp - CS8A + CS8A) with (bv_unsigned sp) by lia. apply Z_to_bv_bv_unsigned. }
  destruct (reg_cases r) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
    subst r; try exact I; try reflexivity; try exact (eq_sym Esp);
    cbn [den]; symmetry; apply pword_scalar; rewrite Hrho by (vm_compute; reflexivity); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma tags_small : forallb (fun t => (to_Z t <? 56)) (TA8 ++ TB8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma SHBW_Z8 : wZ SHBW = SHB. Proof. reflexivity. Qed.

Theorem comba8_okA : comba8_aspec CS8A.
Proof.
  unfold comba8_aspec.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m a b lo
         LA LB HLA HLB RA RB WR DRA DRB Hstk Hlo SEPR SEPA SEPB Hmi SHBC ACR ACA ACB (AL_R & AL_A & AL_B & OFFR & LOHI) P0R P0A P0B RIMG.
  set (SPz := bv_unsigned sp) in *. set (RP := bv_unsigned a0) in *. set (AP := bv_unsigned a1) in *. set (BP := bv_unsigned a2) in *.
  set (rho0 := rho8A SPz AP BP RP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a b).
  set (WIV := [(RP, RP + 8 * 16); (SPz - CS8A, SPz)]).
  set (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x226a50) fc None m (seg_rom bsegs)).
  assert (HspC : CS8A <= SPz) by (destruct Hstk as (S0 & _); lia).
  assert (PA : ptr_ok8 AP) by (split; [exact P0A | exact AL_A]).
  assert (PB : ptr_ok8 BP) by (split; [exact P0B | exact AL_B]).
  assert (PR : ptr_ok8 RP) by (split; [exact P0R | exact AL_R]).
  (* [comment removed for export] *)
  assert (HA0 : map rho0 TA8 = a).
  { destruct a as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate HLA. reflexivity. }
  assert (HB0 : map rho0 TB8 = b).
  { destruct b as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|]]]]]]]]]; try discriminate HLB. reflexivity. }
  (* [comment removed for export] *)
  destruct (c8_ok_inv c8_run c8_checked) as (logE & SE & rgE & stE & Erun & Epc & Erv & Hregs & EgR & EaR & EsR & Hkb & Hincr & Harun & Hchk).
  rewrite c8_run_unfold in Erun.
  assert (Hmaps : forall rho2, (forall t, to_Z t < to_Z NEXT8A -> rho2 t = rho0 t) -> map rho2 TA8 = a /\ map rho2 TB8 = b).
  { intros rho2 Hr. rewrite <- HA0, <- HB0. unfold TA8, TB8. cbn [map]. rewrite !Hr by (vm_compute; reflexivity). split; reflexivity. }
  (* [comment removed for export] *)
  assert (HRS0 : RSn bsegs SHBW rho0 S8A ms0).
  { split.
    - intros rho2 Hag. cbn [S8A s_next] in Hag.
      assert (Hrho : forall t, to_Z t < to_Z NEXT8A -> rho2 t = rho0 t) by exact Hag.
      destruct (Hmaps rho2 Hrho) as [HA2 HB2].
      unfold R, ms0. cbn [ms_svc_pending ms_pc_val ms_resv ms_mem MS S8A s_pc s_regs s_resv s_mem].
      split; [reflexivity|]. split; [reflexivity|]. split.
      { unfold core_of. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv MS]. eapply Rregs_init8; [exact Hrho | exact HspC]. }
      split; [reflexivity|].
      apply (rmem8 rho2 m a b AP BP RP lo SPz Hmi LA LB HLA HLB RA RB WR); try assumption;
        first [ exact (Hrho T8_STK ltac:(vm_compute; reflexivity)) | exact (Hrho T8_A ltac:(vm_compute; reflexivity))
              | exact (Hrho 3%uint63 ltac:(vm_compute; reflexivity)) | exact (Hrho T8_B ltac:(vm_compute; reflexivity))
              | exact (Hrho 5%uint63 ltac:(vm_compute; reflexivity)) | exact (Hrho T8_R ltac:(vm_compute; reflexivity))
              | exact (Hrho 7%uint63 ltac:(vm_compute; reflexivity)) ].
    - (* [comment removed for export] *)
      cbn [S8A s_next s_mem]. intros rho2 Hag s rg G Ea Hodd. rewrite SHBW_Z8.
      pose proof (M8A_class s rg G) as C. rewrite Ea in C. destruct C as [_ C].
      destruct (C Hodd) as [-> |[-> | ->]].
      + rewrite (Hag 3%uint63) by (vm_compute; reflexivity). change ((3 - 1)%uint63) with T8_A. rewrite (Hag T8_A) by (vm_compute; reflexivity). reflexivity.
      + rewrite (Hag 5%uint63) by (vm_compute; reflexivity). change ((5 - 1)%uint63) with T8_B. rewrite (Hag T8_B) by (vm_compute; reflexivity). reflexivity.
      + rewrite (Hag 7%uint63) by (vm_compute; reflexivity). change ((7 - 1)%uint63) with T8_R. rewrite (Hag T8_R) by (vm_compute; reflexivity). reflexivity. }
  (* [comment removed for export] *)
  assert (HC0 : CInv bsegs M8A WIV m F fc S8A ms0).
  { unfold CInv, ms0. cbn [S8A s_mem ms_mem ms_fregs ms_fcsr ms_rom ms_regs MS].
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hmi|].
    repeat (split; [reflexivity|]). do 31 eexists. reflexivity. }
  assert (HP : forall rho, agree_below NEXT8A rho0 rho -> sx_pres bsegs rho (CInv bsegs M8A WIV m F fc)).
  { intros rho Hag. apply CInv_sx. intros t rg G Hw. pose proof (M8A_class t rg G) as C. unfold rbase.
    destruct (rg_abs rg) as [x|]; [rewrite Hw in C; discriminate C|]. destruct C as [C _].
    destruct (C Hw) as [[-> Es]|[-> Es]]; rewrite Es.
    - rewrite (Hag T8_R) by (vm_compute; reflexivity). change (rho0 T8_R) with RP. unfold WIV. cbn [inside]. left. lia.
    - rewrite (Hag T8_STK) by (vm_compute; reflexivity). change (rho0 T8_STK) with (SPz - CS8A). unfold WIV, CS8A. cbn [inside]. right. left. lia. }
  destruct (sxs_run_sound SHBW bsegs stop8 (CInv bsegs M8A WIV m F fc) NEXT8A rho0 HP FUEL8 rho0 [] logE S8A SE ms0
              (agree_below_refl _ _) ltac:(cbn [S8A s_next]; lia) HRS0 HC0 (Forall_nil _) (Forall_nil _) Erun)
    as (rho1 & ms1 & Hag1 & Hms & HRS1 & HC1 & Hlog1 & _).
  cbn [S8A s_next] in Hag1.
  assert (Hv : forall t, to_Z t < to_Z NEXT8A -> rho1 t = rho0 t) by exact Hag1.
  (* [comment removed for export] *)
  pose proof (Rn_R bsegs rho1 SE ms1 (proj1 HRS1)) as HR1. pose proof HR1 as (Hsvc & Hpc & HRg & Hrv & HRm).
  destruct fetch_final8 as [ic' Hfetch]. rewrite <- Epc in Hfetch.
  destruct (hx_ret_step bsegs rho1 IEmpty ic' SE ms1 (ic_ok_empty bsegs) HR1 Hfetch) as (ms2 & Hstep & Ems2).
  exists ms2. split; [exact (msteps_trans bsegs _ _ _ Hms (msteps_one bsegs _ _ Hstep))|].
  destruct HC1 as (Hd1 & MU & WM & MI1 & Hfr & Hfc & Hro & Hnf).
  rewrite Erv in Hrv. cbn [Rresv] in Hrv.
  destruct Hnf as (y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20
                   & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & Eregs).
  unfold core_of in HRg, Ems2. rewrite Eregs in HRg, Ems2. rewrite Hfr, Hfc, Hro, Hrv in Ems2.
  destruct (final_regs_den8 rho1 SE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hregs HRg)
    as (E1 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  rewrite (pword_scalar rho1 T8_RA ra) in E1 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 T8_GP gp) in E3 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 T8_TP tp) in E4 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 T8_S0 s0) in E8 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 1)%uint63 s1) in E9 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 2)%uint63 s2) in E18 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 3)%uint63 s3) in E19 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 4)%uint63 s4) in E20 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 5)%uint63 s5) in E21 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 6)%uint63 s6) in E22 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 7)%uint63 s7) in E23 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 8)%uint63 s8) in E24 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 9)%uint63 s9) in E25 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 10)%uint63 s10) in E26 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  rewrite (pword_scalar rho1 (T8_S0 + 11)%uint63 s11) in E27 by (rewrite Hv by (vm_compute; reflexivity); reflexivity).
  assert (E2' : y2 = sp).
  { rewrite E2. unfold pword. rewrite Hv by (vm_compute; reflexivity). change (rho0 T8_STK) with (SPz - CS8A). change (wZ (W false CS8AI)) with CS8A.
    replace (SPz - CS8A + CS8A) with SPz by lia. apply Z_to_bv_bv_unsigned. }
  subst y1 y2 y3 y4 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27.
  change (Sem.rget _ (Z_to_bv 5 1)) with ra in Ems2. rewrite E2' in Ems2.
  (* [comment removed for export] *)
  set (m' := ms_mem ms1) in *.
  unfold vl_post. exists y5, y6, y7, y10, y11, y12, y13, y14, y15, y16, y17, y28, y29, y30, y31, m'.
  split; [exact Ems2|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1|].
  split.
  - (* [comment removed for export] *)
    destruct (Hmaps rho1 Hv) as [HA1 HB1].
    assert (Hin : forall t, In t (TA8 ++ TB8) -> 0 <= rho1 t < MW /\ to_Z t < 56).
    { intros t Ht. split; [|apply Z.ltb_lt; exact (proj1 (forallb_forall _ _) tags_small t Ht)].
      apply in_app_or in Ht. change MW with (2 ^ 64).
      destruct Ht as [Ht|Ht]; [exact (proj1 (Forall_forall _ _) (tags_range rho1 TA8 a HA1 LA) t Ht) | exact (proj1 (Forall_forall _ _) (tags_range rho1 TB8 b HB1 LB) t Ht)]. }
    assert (Hlt : hsum (map rho1 TA8) * hsum (map rho1 TB8) < MW ^ 16).
    { rewrite HA1, HB1, !hsum_lval. pose proof (lval_bound a LA) as H1. pose proof (lval_bound b LB) as H2. rewrite HLA in H1. rewrite HLB in H2.
      change (MW ^ 16) with (Bp 8 * Bp 8). apply mul_bound_lt; assumption. }
    destruct (mul_cert rho1 (rev logE) TA8 TB8 (outs_of rgE) 56 (MW ^ 16) stE (Forall_rev Hlog1) Hin Hincr Harun Hchk ltac:(vm_compute; reflexivity) Hlt) as [Hsum Hrange].
    rewrite HA1, HB1, !hsum_lval in Hsum.
    set (L := map rho1 (outs_of rgE)) in *.
    assert (HLl : limbs L).
    { unfold L, limbs. rewrite Forall_map. eapply Forall_impl; [|exact Hrange]. intros t Ht. cbn in Ht. unfold limb, BW. unfold MW in Ht. exact Ht. }
    assert (EL : L = mul_comba8 a b).
    { unfold mul_comba8. rewrite <- (to_limbs_unique L (lval a * lval b) HLl Hsum). reflexivity. }
    rewrite <- EL.
    pose proof (proj1 HRm _ _ EgR) as HokR.
    destruct (kb_check_sound bsegs rho1 T8_R rgE m' (kbs_ptrs (outs_of rgE)) 0 HokR Hkb ltac:(lia)) as (bs & HF & Hb & _).
    { rewrite EsR. unfold kbs_ptrs, outs_of. cbn [map concat length app kbs_ptr seq]. lia. }
    unfold rbase in Hb. rewrite EaR, Hv, Z.add_0_r in Hb by (vm_compute; reflexivity). change (rho0 T8_R) with RP in Hb.
    unfold limbs_at, L. rewrite <- (kbs_ptrs_bytes rho1 (outs_of rgE) bs); [exact Hb | | exact HF].
    eapply Forall_impl; [|exact Hrange]. intros t Ht. cbn in Ht. unfold MW in Ht. change (2 ^ 64) with 18446744073709551616. exact Ht.
  - (* [comment removed for export] *)
    destruct Hstk as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. intros x Hx. destruct (S3 x Hx) as [Hwv (bb & Hbb)].
    split; [apply WM; exact Hwv|].
    destruct (Z_lt_le_dec x (SPz - CS8A)) as [Lt|Ge]; [destruct (Z_lt_le_dec x RP) as [L1|G1]; [|destruct (Z_lt_le_dec x (RP + 128)) as [L2|G2]]|].
    + exists bb. unfold mrd in *. rewrite MU; [exact Hbb|]. rewrite wa_unsigned by lia. unfold WIV, CS8A in *. cbn [outside]. lia.
    + (* [comment removed for export] *)
      pose proof (region_mapped bsegs rho1 T8_R rgE m' (proj1 HRm _ _ EgR)) as Hmp. unfold rbase in Hmp. rewrite EaR, EsR, Hv in Hmp by (vm_compute; reflexivity).
      change (rho0 T8_R) with RP in Hmp. destruct (Hmp (x - RP) ltac:(lia)) as [Hm' _]. replace (RP + (x - RP)) with x in Hm' by lia. exact Hm'.
    + exists bb. unfold mrd in *. rewrite MU; [exact Hbb|]. rewrite wa_unsigned by lia. unfold WIV, CS8A in *. cbn [outside]. lia.
    + specialize (Hd1 T8_STK). rewrite M8A_get8 in Hd1.
      destruct (mget (s_mem SE) T8_STK) as [rg1|] eqn:Eg1; [|contradiction].
      pose proof (region_mapped bsegs rho1 T8_STK rg1 m' (proj1 HRm _ _ Eg1)) as Hmp.
      rewrite (rbase_same_dir rho1 T8_STK c8_stk rg1 Hd1) in Hmp. destruct Hd1 as (_ & Es1 & _). rewrite Es1 in Hmp.
      unfold rbase in Hmp. cbn [rg_abs rg_size c8_stk] in Hmp. rewrite Hv in Hmp by (vm_compute; reflexivity).
      change (rho0 T8_STK) with (SPz - CS8A) in Hmp. change (to_Z CS8AI) with CS8A in Hmp.
      destruct (Hmp (x - (SPz - CS8A)) ltac:(lia)) as [Hm' _].
      replace (SPz - CS8A + (x - (SPz - CS8A))) with x in Hm' by lia. exact Hm'.
Qed.

Lemma CS8A_nonneg : 0 <= CS8A.
Proof. unfold CS8A. lia. Qed.
