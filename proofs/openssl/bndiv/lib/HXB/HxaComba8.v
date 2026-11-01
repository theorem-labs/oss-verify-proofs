(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  map (fun k => match iget (rg_d rg) (rg_cells rg) k with Some (CP t _) => t | _ => 0%uint63 end)
      [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%uint63.

Definition kbs_ptrs (tags : list int) : list kb := concat (map kbs_ptr tags).

Definition c8_ok (r : option (list snode * sstate)) : bool :=
  match r with
  | None => false
  | Some (log, X) =>
      let trace := rev log in
      w_eqb (s_pc X) PC_C8A_RET
      && match s_resv X with RNone => true | _ => false end
      && final_regs_ok8 X
      && match mget (s_mem X) T8_R with
         | None => false
         | Some rg =>
             match rg_abs rg with
             | Some _ => false
             | None =>
                 (to_Z (rg_size rg) =? 128) && kb_check bsegs rg 0 (kbs_ptrs (outs_of rg)) && incr_chk 56 trace
                 && match arun st08 trace with
                    | Some st => mul_check st TA8 TB8 (outs_of rg) (MW ^ 16)
                    | None => false
                    end
             end
         end
  end.

Lemma c8_ok_inv (r : option (list snode * sstate)) : c8_ok r = true ->
  exists log X rg st, r = Some (log, X) /\ s_pc X = PC_C8A_RET /\ s_resv X = RNone /\ final_regs_ok8 X = true
    /\ mget (s_mem X) T8_R = Some rg /\ rg_abs rg = None /\ to_Z (rg_size rg) = 128
    /\ kb_check bsegs rg 0 (kbs_ptrs (outs_of rg)) = true /\ incr_chk 56 (rev log) = true
    /\ arun st08 (rev log) = Some st /\ mul_check st TA8 TB8 (outs_of rg) (MW ^ 16) = true.
Proof.
  destruct r as [[log X]|]; intros Hgood; [|discriminate Hgood].
  unfold c8_ok in Hgood. cbv zeta in Hgood.
  apply andb_prop in Hgood as [Hfront Hregion].
  apply andb_prop in Hfront as [Hfront Hregs_ok].
  apply andb_prop in Hfront as [Hpc_ok Hresv_ok].
  destruct (mget (s_mem X) T8_R) as [rg|] eqn:Hget_r; [|discriminate Hregion].
  destruct (rg_abs rg) as [fixed_base|] eqn:Habs_r; [discriminate Hregion|].
  apply andb_prop in Hregion as [Hregion Hpoly].
  apply andb_prop in Hregion as [Hregion Hincr].
  apply andb_prop in Hregion as [Hsize Hkb].
  destruct (arun st08 (rev log)) as [st|] eqn:Harun; [|discriminate Hpoly].
  destruct (s_resv X) as [| held |] eqn:Hresv; [| discriminate Hresv_ok | discriminate Hresv_ok].
  apply w_eqb_true_iff in Hpc_ok. apply Z.eqb_eq in Hsize.
  exists log, X, rg, st.
  repeat split; first [reflexivity | assumption].
Qed.

Lemma c8_run_unfold : c8_run = sxs_run SHBW bsegs stop8 FUEL8 [] S8A.
Proof. unfold c8_run. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c8_checked : c8_ok c8_run = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fetch_final8 : exists ic', hx_fetch bsegs IEmpty PC_C8A_RET = Some (DJalr X0 X1 w_zero, ic').
Proof.
  exists (match hx_fetch bsegs IEmpty PC_C8A_RET with Some (_, cache) => cache | None => IEmpty end).
  vm_compute. reflexivity.
Qed.

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
  intros Hinv Hlo Hfit Hpos Hmapped.
  destruct (Hmapped (n - 1) ltac:(lia)) as [top_byte Htop_rd].
  pose proof (mrd_below bsegs m _ top_byte Hinv Htop_rd) as Htop_lt.
  rewrite wa_unsigned in Htop_lt by lia.
  lia.
Qed.

(* [comment removed for export] *)
Lemma acc_zero_bytes (m : word -> option byte) (p n : Z) : p mod 8 = 0 -> acc bsegs m p n -> 0 < n -> n mod 8 = 0 ->
  bytes_at bsegs m (shad p) (repeat z8 (Z.to_nat (n / 8))).
Proof.
  intros Hp_al Hacc Hn_pos Hn_al.
  assert (Hcount_pos : 0 < n / 8) by (Z.div_mod_to_equations; lia).
  assert (Hcount_eq : n = 8 * (n / 8)) by (Z.div_mod_to_equations; lia).
  destruct (Hacc 0 ltac:(lia)) as (b_first & Hat_first & _).
  destruct (Hacc (n - 1) ltac:(lia)) as (b_last & Hat_last & _).
  apply bytes_at_bound in Hat_first. apply bytes_at_bound in Hat_last. cbn [length] in Hat_first, Hat_last.
  rewrite Z.add_0_r in Hat_first.
  rewrite (shad_aligned_add p (n - 1) Hp_al ltac:(lia)) in Hat_last.
  assert (Hlast_slot : (n - 1) / 8 = n / 8 - 1) by (Z.div_mod_to_equations; lia).
  rewrite Hlast_slot in Hat_last.
  split; [lia|]. split.
  - rewrite repeat_length, Z2Nat.id by lia. lia.
  - intros i Hi. rewrite repeat_length in Hi.
    assert (Hi_lt : Z.of_nat i < n / 8).
    { apply Nat2Z.inj_lt in Hi. rewrite Z2Nat.id in Hi by lia. exact Hi. }
    rewrite nth_error_repeat by exact Hi.
    assert (Hslot_al : (p + 8 * Z.of_nat i) mod 8 = 0).
    { replace (p + 8 * Z.of_nat i) with (p + Z.of_nat i * 8) by ring. rewrite Z.mod_add by lia. exact Hp_al. }
    pose proof (acc_gran0 bsegs m p n (p + 8 * Z.of_nat i) Hacc Hslot_al ltac:(lia) ltac:(lia)) as Hgranule.
    rewrite shad_add8 in Hgranule.
    destruct Hgranule as (_ & _ & Hgranule_rd).
    specialize (Hgranule_rd 0%nat ltac:(cbn [length]; lia)).
    change (Z.of_nat 0) with 0 in Hgranule_rd. rewrite Z.add_0_r in Hgranule_rd.
    exact Hgranule_rd.
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
Proof.
  intros [_ Hcell_bytes]. cbn [cells_bytes cbytes] in Hcell_bytes.
  rewrite app_nil_r in Hcell_bytes. exact Hcell_bytes.
Qed.

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
Proof using SHBC.
  pose proof SHBC as [Hgot_cell _].
  pose proof (c8_le8 m _ _ Hgot_cell) as Hgot_bytes.
  unfold le8, word_to_le_bytes in Hgot_bytes.
  rewrite unsigned_lit in Hgot_bytes by (unfold g_shadow_memory_dynamic_address; split; closed_side).
  apply (static_region_ok bsegs rho T8_GOT c8_got m GOT_SHB_CELL
           (kbs_Z 8 g_shadow_memory_dynamic_address) (Z_to_le_bytes 8 g_shadow_memory_dynamic_address));
    [ reflexivity | reflexivity | vm_compute; reflexivity | | exact Hgot_bytes | | vm_compute; reflexivity ].
  - apply kbs_Z_intro. unfold g_shadow_memory_dynamic_address. closed_side.
  - rewrite length_Z_to_le_bytes. reflexivity.
Qed.

Lemma c8_shb_ok : region_ok bsegs rho T8_SHB c8_shb m.
Proof using SHBC.
  pose proof SHBC as [_ Hshb_cell].
  pose proof (c8_le8 m _ _ Hshb_cell) as Hshb_bytes.
  unfold le8, word_to_le_bytes in Hshb_bytes.
  rewrite unsigned_lit in Hshb_bytes by (unfold SHB; split; closed_side).
  assert (Hshb_len : Z.of_nat (length (Z_to_le_bytes 8 SHB)) = to_Z (rg_size c8_shb)).
  { rewrite length_Z_to_le_bytes. reflexivity. }
  apply (static_region_ok bsegs rho T8_SHB c8_shb m SHB_CELL (kbs_Z 8 SHB) (Z_to_le_bytes 8 SHB) eq_refl eq_refl);
    [ vm_compute; reflexivity | apply kbs_Z_intro; unfold SHB; closed_side | exact Hshb_bytes | exact Hshb_len | vm_compute; reflexivity ].
Qed.

(* [comment removed for export] *)
Lemma limb_region_ok (t t0 : int) (tags : list int) (A : Z) (l : list Z) :
  rho t = A -> map rho tags = l -> limbs l -> length l = 8%nat -> limbs_at bsegs m A l -> ptr_ok8 A ->
  learn_check bsegs (RG None 64 AL8A false DUnk 3%nat (limb_cells t0)) [(0, kbs_ptrs tags)] 0 64 = true ->
  region_ok bsegs rho t (RG None 64 AL8A false DUnk 3%nat (limb_cells t0)) m.
Proof using MI HLA HLB.
  intros Hbase Htags Hlimbs Hlen Hat Hptr Hlearn.
  destruct Hptr as [Hpos Halign].
  pose proof (limbs_at_bound bsegs m A l Hat) as [Hlo Hfit]. rewrite Hlen in Hfit.
  pose proof (bytes_at_mapped bsegs m A (lbytes l) Hat) as Hmapped.
  rewrite lbytes_lengthZ, Hlen in Hmapped.
  pose proof (mapped_below m A 64 MI Hlo ltac:(lia) ltac:(lia) Hmapped) as Htop.
  unfold UTOP in Htop.
  assert (Hrb : rbase rho t (RG None 64%uint63 AL8A false DUnk 3%nat (limb_cells t0)) = A) by exact Hbase.
  apply (region_ok_learn bsegs rho t _ m [(0, kbs_ptrs tags)]); rewrite ?Hrb; cbn [rg_size rg_d rg_al rg_wr];
    [ exact Hpos | | closed_side | closed_side | closed_side | closed_side | exact Halign | | | | exact Hlearn ].
  - change (to_Z 64%uint63) with 64. unfold two63. lia.
  - intros i Hi. apply Hmapped. change (to_Z 64%uint63) with 64 in Hi. lia.
  - intros Hro. discriminate Hro.
  - constructor; [|constructor]. exists (lbytes l). cbn [fst snd]. rewrite Z.add_0_r. split; [|exact Hat].
    rewrite <- Htags. apply kbs_ptrs_intro. exact (tags_range tags l Htags Hlimbs).
Qed.

Hypothesis PA : ptr_ok8 AP.
Hypothesis PB : ptr_ok8 BP.
Hypothesis PR : ptr_ok8 RP.

Lemma c8_a_ok : region_ok bsegs rho T8_A c8_a m.
Proof using MI LA HLA HLB RA Hr2 HrA PA.
  apply (limb_region_ok T8_A T8_LA TA8 AP a Hr2 HrA LA HLA RA PA). vm_compute. reflexivity.
Qed.

Lemma c8_b_ok : region_ok bsegs rho T8_B c8_b m.
Proof using MI LB HLA HLB RB Hr4 HrB PB.
  apply (limb_region_ok T8_B T8_LB TB8 BP b Hr4 HrB LB HLB RB PB). vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma AP_hi : AP + 64 <= UTOP.
Proof using MI HLA HLB RA.
  pose proof (limbs_at_bound bsegs m AP a RA) as [Hlo Hfit]. rewrite HLA in Hfit.
  apply (mapped_below m AP 64 MI Hlo ltac:(lia) ltac:(lia)).
  intros i Hi. apply (bytes_at_mapped bsegs m AP (lbytes a) RA). rewrite lbytes_lengthZ, HLA. lia.
Qed.
Lemma BP_hi : BP + 64 <= UTOP.
Proof using MI HLA HLB RB.
  assert (Hnonempty : lbytes b <> []).
  { intros Hempty. pose proof (lbytes_length b) as Hblen. rewrite Hempty, HLB in Hblen. discriminate Hblen. }
  pose proof (bytes_at_below bsegs m BP (lbytes b) MI RB Hnonempty) as Hbelow.
  rewrite lbytes_lengthZ, HLB in Hbelow. lia.
Qed.
Lemma RP_hi : RP + 128 <= UTOP.
Proof using MI HLA HLB WR. exact (wr_at_below bsegs m RP 128 MI WR ltac:(lia)). Qed.

Lemma c8_r_ok : region_ok bsegs rho T8_R c8_r m.
Proof using MI HLA HLB WR Hr6 PR.
  pose proof RP_hi as Hr_top. pose proof PR as [Hr_pos Hr_align]. unfold UTOP in Hr_top.
  apply (fresh_region_ok rho T8_R 128%uint63 AL8A true m RP Hr6 Hr_pos); [| closed_side | closed_side | exact Hr_align | exact WR].
  change (to_Z 128%uint63) with 128. unfold two63. lia.
Qed.

(* [comment removed for export] *)
Lemma c8_ash_ok : region_ok bsegs rho 3%uint63 c8_ash m.
Proof using MI HLA HLB RA Hr3 ACA PA.
  pose proof AP_hi as Ha_top. pose proof PA as [Ha_pos Ha_align]. unfold UTOP in Ha_top.
  change (2 ^ to_Z AL8A) with 8 in Ha_align.
  pose proof (acc_zero_bytes m AP 64 Ha_align ACA ltac:(lia) eq_refl) as Ha_zero.
  apply (zero_region_ok rho 3%uint63 8%uint63 m (shad AP) Hr3); [| | closed_side | exact Ha_zero].
  - unfold shad, SHB. Z.div_mod_to_equations. lia.
  - change (to_Z 8%uint63) with 8. unfold shad, SHB, two63. Z.div_mod_to_equations. lia.
Qed.
Lemma c8_bsh_ok : region_ok bsegs rho 5%uint63 c8_bsh m.
Proof using MI HLA HLB RB Hr5 ACB PB.
  pose proof BP_hi as Hb_top. pose proof PB as [Hb_pos Hb_align]. unfold UTOP in Hb_top.
  change (2 ^ to_Z AL8A) with 8 in Hb_align.
  apply (zero_region_ok rho 5%uint63 8%uint63 m (shad BP) Hr5).
  - unfold shad, SHB. Z.div_mod_to_equations. lia.
  - change (to_Z 8%uint63) with 8. unfold shad, SHB, two63. Z.div_mod_to_equations. lia.
  - closed_side.
  - exact (acc_zero_bytes m BP 64 Hb_align ACB ltac:(lia) eq_refl).
Qed.
Lemma c8_rsh_ok : region_ok bsegs rho 7%uint63 c8_rsh m.
Proof using MI HLA HLB WR Hr7 ACR PR.
  pose proof RP_hi as Hr_top. pose proof PR as [Hr_pos Hr_align]. unfold UTOP in Hr_top.
  change (2 ^ to_Z AL8A) with 8 in Hr_align.
  assert (Hr_shad_lo : 0 <= shad RP) by (unfold shad, SHB; Z.div_mod_to_equations; lia).
  assert (Hr_shad_hi : shad RP + 16 < two63) by (unfold shad, SHB, two63; Z.div_mod_to_equations; lia).
  exact (zero_region_ok rho 7%uint63 16%uint63 m (shad RP) Hr7 Hr_shad_lo Hr_shad_hi ltac:(closed_side)
           (acc_zero_bytes m RP 128 Hr_align ACR ltac:(lia) eq_refl)).
Qed.

Hypothesis STKH : stk bsegs m lo sp0.
Hypothesis Hlo : lo <= sp0 - CS8A.
Hypothesis LOHI : SHHI <= lo.

Lemma c8_stk_ok : region_ok bsegs rho T8_STK c8_stk m.
Proof using MI HLA HLB Hr8 STKH Hlo LOHI.
  pose proof STKH as (Hlo_nonneg & Hsp_fit & Hframe).
  unfold CS8A, SHHI in *.
  assert (Hsp_top : sp0 <= UTOP).
  { destruct (Hframe (sp0 - 1) ltac:(lia)) as [Hview _].
    pose proof (wview_below bsegs m _ MI Hview) as Hview_lt. rewrite wa_unsigned in Hview_lt by lia. lia. }
  unfold UTOP in Hsp_top.
  apply (fresh_region_ok rho T8_STK CS8AI 0%uint63 true m (sp0 - 592) Hr8); [lia | | closed_side | closed_side | |].
  - change (to_Z CS8AI) with 592. unfold two63. lia.
  - change (2 ^ to_Z 0%uint63) with 1. apply Z.mod_1_r.
  - change (to_Z CS8AI) with 592. split; [lia|]. split; [lia|].
    intros i Hi. exact (proj1 (Hframe (sp0 - 592 + i) ltac:(lia))).
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
Proof using All.
  pose proof AP_hi as Ha_top. pose proof BP_hi as Hb_top. pose proof RP_hi as Hr_top.
  pose proof PA as [Ha_pos _]. pose proof PB as [Hb_pos _]. pose proof PR as [Hr_pos _].
  unfold UTOP, SHLO, SHHI in *.
  pose proof (Rmem_empty bsegs rho m) as Rm_0. pose proof (dir_inw_empty rho) as Dw_0.
  destruct (Rmem_add_sepw bsegs rho IEmpty T8_GOT c8_got m [] Rm_0 Dw_0
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_got_ok ltac:(sep8)) as [Rm_got Dw_got].
  destruct (Rmem_add_sepw bsegs rho M8_got T8_SHB c8_shb m _ Rm_got Dw_got
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_shb_ok ltac:(sep8)) as [Rm_shb Dw_shb].
  destruct (Rmem_add_sepw bsegs rho M8_shb T8_A c8_a m _ Rm_shb Dw_shb
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_a_ok ltac:(sep8)) as [Rm_a Dw_a].
  destruct (Rmem_add_sepw bsegs rho M8_a 3%uint63 c8_ash m _ Rm_a Dw_a
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_ash_ok ltac:(sep8)) as [Rm_ash Dw_ash].
  destruct (Rmem_add_sepw bsegs rho M8_ash T8_B c8_b m _ Rm_ash Dw_ash
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_b_ok ltac:(sep8)) as [Rm_b Dw_b].
  destruct (Rmem_add_sepw bsegs rho M8_b 5%uint63 c8_bsh m _ Rm_b Dw_b
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_bsh_ok ltac:(sep8)) as [Rm_bsh Dw_bsh].
  destruct (Rmem_add_sepw bsegs rho M8_bsh 7%uint63 c8_rsh m _ Rm_bsh Dw_bsh
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_rsh_ok ltac:(sep8)) as [Rm_rsh Dw_rsh].
  destruct (Rmem_add_sepw bsegs rho M8_rsh T8_R c8_r m _ Rm_rsh Dw_rsh
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_r_ok ltac:(sep8)) as [Rm_r Dw_r].
  destruct (Rmem_add_sepw bsegs rho M8_r T8_STK c8_stk m _ Rm_r Dw_r
              ltac:(vm_compute; reflexivity) ltac:(closed_side) c8_stk_ok ltac:(sep8)) as [Rm_all _].
  exact Rm_all.
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
    Hlimbs_a Hlimbs_b Hlen_a Hlen_b Hat_a Hat_b Hwr_r Hsep_ra Hsep_rb Hstk Hlo_frame Hsep_rs Hsep_as Hsep_bs
    Hinv Hshb Hacc_r Hacc_a Hacc_b Hptrs Hpos_r Hpos_a Hpos_b Himg_r.
  destruct Hptrs as (Hal_r & Hal_a & Hal_b & Hoff_r & Hshhi_lo).
  pose proof Hstk as (Hlo_nn & Hsp_fit & Hframe).
  assert (Hsp_floor : CS8A <= bv_unsigned sp) by (unfold CS8A in *; lia).

  (* the symbolic start state: every tag below NEXT8A gets its concrete value *)
  pose (rho0 := rho8A (bv_unsigned sp) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a0)
                      ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a b).
  pose (Wfoot := [(bv_unsigned a0, bv_unsigned a0 + 8 * 16); (bv_unsigned sp - CS8A, bv_unsigned sp)]).
  pose (ms0 := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x226a50) fc None m (seg_rom bsegs)).
  assert (Hspell_a : [nth 0 a 0; nth 1 a 0; nth 2 a 0; nth 3 a 0; nth 4 a 0; nth 5 a 0; nth 6 a 0; nth 7 a 0] = a).
  { clear - Hlen_a. do 8 (destruct a as [|? a]; [discriminate Hlen_a|]). destruct a; [reflexivity | discriminate Hlen_a]. }
  assert (Hspell_b : [nth 0 b 0; nth 1 b 0; nth 2 b 0; nth 3 b 0; nth 4 b 0; nth 5 b 0; nth 6 b 0; nth 7 b 0] = b).
  { clear - Hlen_b. do 8 (destruct b as [|? b]; [discriminate Hlen_b|]). destruct b; [reflexivity | discriminate Hlen_b]. }
  assert (Hval : forall rho : valuation, agree_below NEXT8A rho0 rho ->
            rho T8_STK = bv_unsigned sp - CS8A /\ rho T8_A = bv_unsigned a1 /\ rho 3%uint63 = shad (bv_unsigned a1)
            /\ rho T8_B = bv_unsigned a2 /\ rho 5%uint63 = shad (bv_unsigned a2)
            /\ rho T8_R = bv_unsigned a0 /\ rho 7%uint63 = shad (bv_unsigned a0)
            /\ map rho TA8 = a /\ map rho TB8 = b).
  { intros rho Hagree.
    assert (Hpin : forall t, to_Z t < 56 -> rho t = rho0 t) by (intros t Ht; exact (Hagree t Ht)).
    rewrite <- Hspell_a, <- Hspell_b. unfold TA8, TB8. cbn [map].
    rewrite !Hpin by closed_side.
    repeat split; reflexivity. }

  (* the run starts related to the machine *)
  assert (HRS0 : RSn bsegs SHBW rho0 S8A ms0).
  { split.
    - intros rho Hagree.
      destruct (Hval rho Hagree) as (Hv8 & Hv2 & Hv3 & Hv4 & Hv5 & Hv6 & Hv7 & HvA & HvB).
      split; [reflexivity|]. split; [reflexivity|]. split.
      + exact (Rregs_init8 rho a b ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                 F (Z_to_bv 64 0x226a50) fc None Hagree Hsp_floor).
      + split; [reflexivity|].
        exact (rmem8 rho m a b (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned a0) lo (bv_unsigned sp)
                 Hinv Hlimbs_a Hlimbs_b Hlen_a Hlen_b Hat_a Hat_b Hwr_r Hv8 Hv2 Hv3 Hv4 Hv5 Hv6 Hv7 HvA HvB
                 Hshb Hacc_r Hacc_a Hacc_b (conj Hpos_a Hal_a) (conj Hpos_b Hal_b) (conj Hpos_r Hal_r)
                 Hstk Hlo_frame Hshhi_lo Hsep_ra Hsep_rb Hsep_rs Hsep_as Hsep_bs Hoff_r Himg_r).
    - intros rho Hagree. change (sh_law (wZ SHBW) rho M8A). intros s rg Hget Habs Hodd.
      destruct (Hval rho Hagree) as (_ & Hv2 & Hv3 & Hv4 & Hv5 & Hv6 & Hv7 & _ & _).
      pose proof (M8A_class s rg Hget) as Hclass. rewrite Habs in Hclass. hnf in Hclass.
      destruct Hclass as [_ Hodd_tags]. rewrite SHBW_Z8.
      destruct (Hodd_tags Hodd) as [-> | [-> | ->]].
      + change (3 - 1)%uint63 with T8_A. rewrite Hv3, Hv2. reflexivity.
      + change (5 - 1)%uint63 with T8_B. rewrite Hv5, Hv4. reflexivity.
      + change (7 - 1)%uint63 with T8_R. rewrite Hv7, Hv6. reflexivity. }
  assert (HC0 : CInv bsegs M8A Wfoot m F fc S8A ms0).
  { unfold CInv. change (s_mem S8A) with M8A.
    split; [apply same_dirs_refl|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact Hinv|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold regs_nf. do 31 eexists. reflexivity. }
  assert (Hpres : forall rho, agree_below NEXT8A rho0 rho -> sx_pres bsegs rho (CInv bsegs M8A Wfoot m F fc)).
  { intros rho Hagree. apply CInv_sx. intros t rg Hget Hwr_rg.
    destruct (Hval rho Hagree) as (Hv8 & _ & _ & _ & _ & Hv6 & _ & _ & _).
    destruct (rg_abs rg) as [fixed_base|] eqn:Habs.
    - pose proof (M8A_class t rg Hget) as Hclass. rewrite Habs in Hclass. hnf in Hclass.
      rewrite Hclass in Hwr_rg. discriminate Hwr_rg.
    - pose proof (M8A_class t rg Hget) as Hclass. rewrite Habs in Hclass. hnf in Hclass.
      destruct Hclass as [Hwr_cases _].
      unfold rbase. rewrite Habs.
      destruct (Hwr_cases Hwr_rg) as [[-> Hsize] | [-> Hsize]]; rewrite Hsize; unfold Wfoot; cbn [inside].
      + left. rewrite Hv6. lia.
      + right. left. rewrite Hv8. lia. }

  (* run the checked symbolic execution and read off its end state *)
  destruct (c8_ok_inv c8_run c8_checked)
    as (log & X & rg & st & Hrun & Hpc_end & Hresv_end & Hregs_ok & Hget_r & Habs_r & Hsize_r & Hkb_r & Hincr & Harun & Hmul).
  rewrite c8_run_unfold in Hrun.
  destruct (sxs_run_sound SHBW bsegs stop8 (CInv bsegs M8A Wfoot m F fc) NEXT8A rho0 Hpres FUEL8 rho0 [] log S8A X ms0
              (agree_below_refl NEXT8A rho0) (Z.le_refl _) HRS0 HC0 (Forall_nil _) (Forall_nil _) Hrun)
    as (rho1 & ms1 & Hagree1 & Hsteps & HRS1 & HC1 & Hlog1 & _).
  destruct (Hval rho1 Hagree1) as (Hv8 & _ & _ & _ & _ & Hv6 & _ & HvA & HvB).
  pose proof (Rn_R bsegs rho1 X ms1 (proj1 HRS1)) as HR1.
  destruct fetch_final8 as [ic_end Hfetch]. rewrite <- Hpc_end in Hfetch.
  destruct (hx_ret_step bsegs rho1 IEmpty ic_end X ms1 (ic_ok_empty bsegs) HR1 Hfetch) as (ms2 & Hstep2 & Hms2).
  destruct HR1 as (_ & _ & Hregs1 & Hresv1 & Hmem1).
  destruct HC1 as (Hdirs1 & Hmunch1 & Hwmono1 & Hinv1 & Hfregs1 & Hfcsr1 & Hrom1 & Hnf1).
  rewrite Hresv_end in Hresv1. cbn [Rresv] in Hresv1.

  (* callee-saved registers come back unchanged *)
  destruct Hnf1 as (x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20
                    & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & Hregs_eq).
  unfold core_of in Hregs1. rewrite Hregs_eq in Hregs1.
  destruct (final_regs_den8 rho1 X (ms_fregs ms1) (ms_pc_val ms1) (ms_fcsr ms1) (ms_resv ms1)
              x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
              Hregs_ok Hregs1)
    as (Ex1 & Ex2 & Ex3 & Ex4 & Ex8 & Ex9 & Ex18 & Ex19 & Ex20 & Ex21 & Ex22 & Ex23 & Ex24 & Ex25 & Ex26 & Ex27).
  assert (Hscalar : forall (t : int) (w : word), to_Z t < 56 -> rho0 t = bv_unsigned w -> pword rho1 t w_zero = w).
  { intros t w Ht Hw. apply pword_scalar. rewrite (Hagree1 t Ht). exact Hw. }
  repeat match goal with
         | E : _ = pword rho1 ?t w_zero |- _ => rewrite (Hscalar t _ ltac:(closed_side) eq_refl) in E
         end.
  assert (Hsp_back : pword rho1 T8_STK (W false CS8AI) = sp).
  { unfold pword. rewrite Hv8. change (wZ (W false CS8AI)) with CS8A. rewrite Z.sub_add. apply Z_to_bv_bv_unsigned. }
  rewrite Hsp_back in Ex2.
  subst x1 x2 x3 x4 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27.

  (* the result region: its bytes are the 16 output tags, whose value is the product *)
  destruct Hmem1 as [Hregions _].
  pose proof (Hregions T8_R rg Hget_r) as Hrg_ok.
  assert (Hrb_r : rbase rho1 T8_R rg = bv_unsigned a0) by (unfold rbase; rewrite Habs_r; exact Hv6).
  assert (Hkbs_len : length (kbs_ptrs (outs_of rg)) = 128%nat) by (vm_compute; reflexivity).
  destruct (kb_check_sound bsegs rho1 T8_R rg (ms_mem ms1) (kbs_ptrs (outs_of rg)) 0 Hrg_ok Hkb_r ltac:(lia)
              ltac:(rewrite Hkbs_len, Hsize_r; lia)) as (out_bytes & Hout_kb & Hout_at & _).
  rewrite Z.add_0_r, Hrb_r in Hout_at.
  assert (Hlimb_tags : Forall (fun t => limb (rho1 t)) (TA8 ++ TB8)).
  { pose proof Hlimbs_a as Hlimbs_ta. pose proof Hlimbs_b as Hlimbs_tb.
    rewrite <- HvA in Hlimbs_ta. rewrite <- HvB in Hlimbs_tb. unfold limbs in Hlimbs_ta, Hlimbs_tb.
    rewrite Forall_map in Hlimbs_ta, Hlimbs_tb. apply Forall_app. split; assumption. }
  assert (Htag_ok : forall t, In t (TA8 ++ TB8) -> 0 <= rho1 t < MW /\ to_Z t < 56).
  { intros t Hin. split.
    - rewrite Forall_forall in Hlimb_tags. exact (Hlimb_tags t Hin).
    - pose proof tags_small as Hsmall. rewrite forallb_forall in Hsmall. apply Z.ltb_lt. exact (Hsmall t Hin). }
  assert (Hprod_lt : hsum (map rho1 TA8) * hsum (map rho1 TB8) < MW ^ 16).
  { rewrite !hsum_lval, HvA, HvB.
    destruct (lval_bound a Hlimbs_a) as [Hval_a_lo Hval_a_hi]. destruct (lval_bound b Hlimbs_b) as [Hval_b_lo Hval_b_hi].
    rewrite Hlen_a in Hval_a_hi. rewrite Hlen_b in Hval_b_hi.
    change (Bp 8) with (MW ^ 8) in Hval_a_hi, Hval_b_hi.
    replace (MW ^ 16) with (MW ^ 8 * MW ^ 8) by (rewrite <- Z.pow_add_r by lia; reflexivity).
    exact (Z.mul_lt_mono_nonneg _ _ _ _ Hval_a_lo Hval_a_hi Hval_b_lo Hval_b_hi). }
  destruct (mul_cert rho1 (rev log) TA8 TB8 (outs_of rg) 56 (MW ^ 16) st ltac:(apply Forall_rev; exact Hlog1)
              Htag_ok Hincr Harun Hmul ltac:(closed_side) Hprod_lt) as [Hprod Hout_range].
  assert (Hout_limbs : limbs (map rho1 (outs_of rg))).
  { unfold limbs. rewrite Forall_map. eapply Forall_impl; [|exact Hout_range]. intros t Ht. exact Ht. }
  assert (Hout_len : length (map rho1 (outs_of rg)) = 16%nat) by (rewrite length_map; reflexivity).
  assert (Hout_val : mul_comba8 a b = map rho1 (outs_of rg)).
  { unfold mul_comba8. rewrite <- Hout_len. apply to_limbs_unique; [exact Hout_limbs|].
    rewrite <- hsum_lval, Hprod, !hsum_lval, HvA, HvB. reflexivity. }
  assert (Hout_bytes : out_bytes = lbytes (map rho1 (outs_of rg))).
  { apply (kbs_ptrs_bytes rho1 (outs_of rg) out_bytes); [|exact Hout_kb].
    eapply Forall_impl; [|exact Hout_range]. intros t Ht. exact Ht. }

  (* the stack frame region, for the caller's stack after the return *)
  pose proof (Hdirs1 T8_STK) as Hdir_stk. rewrite M8A_get8 in Hdir_stk.
  destruct (mget (s_mem X) T8_STK) as [rg_stk|] eqn:Hget_stk; [|destruct Hdir_stk].
  destruct Hdir_stk as (Habs_stk & Hsize_stk & _).
  pose proof (Hregions T8_STK rg_stk Hget_stk) as Hstk_ok.
  assert (Hrb_stk : rbase rho1 T8_STK rg_stk = bv_unsigned sp - CS8A) by (unfold rbase; rewrite Habs_stk; exact Hv8).

  (* the return step closes the run, and the post holds there *)
  exists ms2. split.
  { exact (msteps_trans bsegs _ _ _ Hsteps (msteps_one bsegs _ _ Hstep2)). }
  unfold W_mul_normal.vl_post. cbv beta.
  exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, (ms_mem ms1).
  split.
  { assert (Hlink : Sem.rget (core_of ms1) (Z_to_bv 5 1) = ra) by (unfold core_of; rewrite Hregs_eq; reflexivity).
    rewrite Hms2, Hlink, Hregs_eq, Hfregs1, Hfcsr1, Hrom1, Hresv1. reflexivity. }
  split; [exact Hmunch1|]. split; [exact Hwmono1|]. split; [exact Hinv1|]. split.
  { unfold limbs_at. rewrite Hout_val, <- Hout_bytes. exact Hout_at. }
  split; [exact Hlo_nn|]. split; [exact Hsp_fit|].
  intros x Hx. split; [exact (Hwmono1 (wa x) (proj1 (Hframe x Hx)))|].
  assert (Hcases : (bv_unsigned a0 <= x < bv_unsigned a0 + 128) \/ (bv_unsigned sp - CS8A <= x < bv_unsigned sp)
                   \/ outside Wfoot x).
  { unfold Wfoot. cbn [outside]. lia. }
  destruct Hcases as [Hin_res | [Hin_frame | Hout_w]].
  - destruct (region_mapped bsegs rho1 T8_R rg (ms_mem ms1) Hrg_ok (x - bv_unsigned a0) ltac:(rewrite Hsize_r; lia))
      as [[v Hv] _].
    rewrite Hrb_r in Hv. replace (bv_unsigned a0 + (x - bv_unsigned a0)) with x in Hv by ring. exists v. exact Hv.
  - destruct (region_mapped bsegs rho1 T8_STK rg_stk (ms_mem ms1) Hstk_ok (x - (bv_unsigned sp - CS8A))
                ltac:(rewrite Hsize_stk; change (to_Z (rg_size c8_stk)) with CS8A; lia)) as [[v Hv] _].
    rewrite Hrb_stk in Hv. replace (bv_unsigned sp - CS8A + (x - (bv_unsigned sp - CS8A))) with x in Hv by ring.
    exists v. exact Hv.
  - destruct (Hframe x Hx) as [_ [v Hv]]. exists v. unfold mrd in *. unfold munch in Hmunch1.
    rewrite Hmunch1; [exact Hv|]. rewrite wa_unsigned by lia. exact Hout_w.
Qed.

Lemma CS8A_nonneg : 0 <= CS8A.
Proof. unfold CS8A. lia. Qed.
