(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptRoom LeptSlots LeptExec LeptExecW LeptExecFP LeptExecX DitherLib DitherLoop LeptCmapArr LeptExecB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require LeptCellsB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2_code_pixGetLinePtrs.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.
(* [comment removed for export] *)
#[local] Opaque RiscvSemantics.store_ok.

Definition LP_ENTRY : Z := 0x1abe0.
Definition LP_RA : Z := 0x1ac2c.
Definition LP_LOOP : Z := 0x1ac54.
Definition LP_EXIT : Z := 0x1ad08.
Definition LP_RET : Z := 0x1ad18.
Definition LP_CALLOC : Z := 0x3c0f8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma lp_swrap32 : forall t r : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> (t mod 2 ^ 32 = r mod 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r Hr Ht. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma lp_swrap32e : forall t r k : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> t = (r + k * 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r k Hr ->. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.

Lemma lp_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b H. unfold v_addw. rewrite !u_Z2bv_mod. f_equal.
  apply lp_swrap32e with (k := (- 2 ^ 32 * (a / 2 ^ 64) - 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.

Lemma lp_mulw : forall a b : Z, (- 2 ^ 31 <= a * b < 2 ^ 31)%Z -> v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b H. unfold v_mulw. rewrite !u_Z2bv_mod. f_equal. apply lp_swrap32; [exact H |].
  assert (Ea : ((a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32)%Z) by lia.
  assert (Eb : ((b mod 2 ^ 64) mod 2 ^ 32 = b mod 2 ^ 32)%Z) by lia.
  rewrite (Z.mul_mod (a mod 2 ^ 64) (b mod 2 ^ 64) (2 ^ 32)) by lia. rewrite Ea, Eb.
  rewrite <- (Z.mul_mod a b (2 ^ 32)) by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma lp_lxor_ones : forall a : Z, (0 <= a < 2 ^ 64)%Z -> Z.lxor a (Z.ones 64) = (2 ^ 64 - 1 - a)%Z.
Proof.
  intros a Ha.
  assert (L : Z.land a (Z.lxor a (Z.ones 64)) = 0%Z).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 64) as [Hl|Hg].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit a i); reflexivity.
    - rewrite (Z.bits_above_log2 a i); [reflexivity | lia |].
      destruct (Z.eq_dec a 0) as [->|Hn]; [cbn; lia |].
      apply Z.log2_lt_pow2; [lia |]. apply Z.lt_le_trans with (2 ^ 64)%Z; [lia |]. apply Z.pow_le_mono_r; lia. }
  pose proof (Z.add_nocarry_lxor a (Z.lxor a (Z.ones 64)) L) as E.
  rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l in E. rewrite Z.ones_equiv in *. lia.
Qed.

Lemma lp_xor_m1 : forall a : Z, (0 <= a < 2 ^ 64)%Z -> v_xor (Z_to_bv 64 a) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - a).
Proof.
  intros a Ha. unfold v_xor. rewrite (u_Z2bv a) by lia.
  replace (bv_unsigned (Z_to_bv 64 (-1))) with (Z.ones 64) by (vm_compute; reflexivity).
  rewrite lp_lxor_ones by exact Ha. reflexivity.
Qed.

Lemma lp_xor_lit : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

Ltac lp_z1 :=
  first [ rewrite Z.add_0_r | rewrite zbv_add | rewrite zbv_mul | rewrite zbv_addi | rewrite lp_mulw by lia | rewrite lp_addw by lia
        | rewrite lp_xor_m1 by lia | rewrite lp_xor_lit by lia
        | rewrite v_sltu_Z by lia | rewrite v_slt_Z by lia
        | match goal with |- context [(?a <? ?b)%Z] =>
            first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ] end
        | match goal with |- context [Z.lxor ?x ?y] =>
            let v := eval vm_compute in (Z.lxor x y) in lazymatch v with Z0 => change (Z.lxor x y) with v | Zpos _ => change (Z.lxor x y) with v end end ].

Ltac lp_z :=
  rewrite ?ex_ptr_val, ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor, ?w_addw, ?w_mulw, ?m_mul;
  repeat lp_z1.

Ltac lp_sc := lazymatch goal with
  | |- reach _ _ _ => idtac
  | |- store_ok _ _ _ _ = true => (try lp_z); first [ assumption | (rewrite ?Z.add_0_r; assumption) ]
  | _ => (try lp_z); try first [ ex_br | (rewrite ?u_Z2bv by lia; lia) ]
  end.

Ltac lp_val regs :=
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  lp_z; first [ reflexivity | f_equal; lia | ex_ext ].

Ltac lp_mem regs Hms :=
  eapply ex_msteps_mem; [exact Hms |]; cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | first [ solve [ex_bytes_eq regs] | (f_equal; lp_val regs) ] ]);
  reflexivity.

Ltac lp_rinv :=
  repeat (eapply rinv_wbytes;
          [ | rewrite ?length_N_to_le_bytes, ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; reflexivity | lia | lia
          | first [ (eexists; split; [ left; reflexivity | cbn [fst snd]; lia ])
                  | (eexists; split; [ right; left; reflexivity | cbn [fst snd]; lia ]) ] ]);
  apply rinv_refl.

Section Segs.
Variable rom : word -> option byte.
#[local] Existing Instance exf_fxd | 100.

Definition LPA_M (m : word -> option byte) (s : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 1)))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

Lemma lp_A : forall (fx : FPState) regs (m : word -> option byte) (s pix h : Z),
  (4096 + 32 <= s <= 2 ^ 47)%Z ->
  (s mod 16 = 0)%Z ->
  (4096 <= pix)%Z ->
  (pix + 64 <= 2 ^ 47)%Z ->
  (pix mod 16 = 0)%Z ->
  (1 <= h <= 20000)%Z ->
  (pix + 64 <= s - 32 \/ s <= pix)%Z ->
  rdn SEGS m (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
  getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 pix ->
  getr regs 11 = Z_to_bv 64 0 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 LP_ENTRY) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 LP_CALLOC) M' rom /\
      rinv [((s - 32)%Z, 32%Z)] m M' /\
      rdn SEGS M' (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 (getr regs 1)) /\ rdn SEGS M' (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8)) /\
      rdn SEGS M' (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9)) /\
      getr regs' 1 = Z_to_bv 64 LP_RA /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 10 = Z_to_bv 64 h /\ getr regs' 11 = Z_to_bv 64 8 /\
      getr regs' 8 = Z_to_bv 64 pix /\ getr regs' 9 = Z_to_bv 64 h /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs').
Proof.
  intros fx regs m s pix h Hs ALs Hp1 Hp2 ALp Hh DJ Rh SOK H2 H10 H11.
  ex_entry regs [s; pix; h] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; pix; h]) m
                 [KRange (EVar 32) 4128 (2 ^ 47 + 1); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 1 20001;
                  KAlign (EVar 32) 16; KAlign (EVar 33) 16; KWr (SA (EVar 32) (-32)) 32;
                  KWord (SA (EVar 33) 4) 4 (EVar 34); KDisj (SA (EVar 33) 0) 64 (SA (EVar 32) (-32)) 32]).
  { ex_know regs. }
  ex_run 100%nat [LP_CALLOC] (SCR [] [] []) HR HK R' HR' Hms.
  apply (reach_msteps _ _ (@mkst fx R' (Z_to_bv 64 LP_CALLOC) (LPA_M m s regs) rom)).
  { unfold LPA_M. ex_mem regs Hms. }
  apply reach_done. exists R', (LPA_M m s regs). split; [reflexivity |].
  unfold LPA_M. split; [lp_rinv |].
  split; [rdn_chain |]. split; [rdn_chain |]. split; [rdn_chain |].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma lp_B : forall (fx : FPState) regs (m : word -> option byte) (s pix h lines wpl data : Z),
  (4096 + 32 <= s <= 2 ^ 47)%Z ->
  (4096 <= pix)%Z ->
  (pix + 64 <= 2 ^ 47)%Z ->
  (1 <= h <= 20000)%Z ->
  (4096 <= lines)%Z ->
  (lines + 8 * h <= 2 ^ 47)%Z ->
  (lines mod 16 = 0)%Z ->
  (1 <= wpl <= 20000)%Z ->
  (1 <= data < 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl) ->
  rdn SEGS m (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data) ->
  getr regs 2 = Z_to_bv 64 (s - 32) ->
  getr regs 10 = Z_to_bv 64 lines ->
  getr regs 8 = Z_to_bv 64 pix ->
  getr regs 9 = Z_to_bv 64 h ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 LP_RA) m rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 LP_LOOP) M' rom /\
      M' = m /\ getr regs' 9 = Z_to_bv 64 (8 * h) /\ getr regs' 10 = Z_to_bv 64 lines /\ getr regs' 11 = Z_to_bv 64 0 /\
      getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 13 = Z_to_bv 64 wpl /\ getr regs' 14 = Z_to_bv 64 data /\
      getr regs' 15 = Z_to_bv 64 (2 ^ 64 - 1 - lines) /\ getr regs' 16 = Z_to_bv 64 0 /\ getr regs' 17 = Z_to_bv 64 1 /\
      regs_agree (fun r => In r [9; 11; 12; 13; 14; 15; 16; 17]%list) regs regs').
Proof.
  intros fx regs m s pix h lines wpl data Hs Hp1 Hp2 Hh Hl1 Hl2 ALl Hw Hd Rw Rd H2 H10 H8 H9.
  ex_entry regs [(s - 32)%Z; pix; h; lines; wpl; data] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 32)%Z; pix; h; lines; wpl; data]) m
                 [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 4096 (2 ^ 47); KRange (EVar 34) 1 20001;
                  KRange (EVar 35) 4096 (2 ^ 47); KRange (EVar 36) 1 20001; KRange (EVar 37) 1 (2 ^ 47);
                  KAlign (EVar 35) 16;
                  KWord (SA (EVar 33) 16) 4 (EVar 36); KWord (SA (EVar 33) 56) 8 (EVar 37)]).
  { ex_know regs. }
  ex_run 100%nat [LP_LOOP] (SCR [] [] []) HR HK R' HR' Hms.
  apply (reach_msteps _ _ (@mkst fx R' (Z_to_bv 64 LP_LOOP) m rom)).
  { ex_mem regs Hms. }
  apply reach_done. exists R', m. split; [reflexivity |]. split; [reflexivity |].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; try ex_ext; try (lp_val regs).
Qed.

(* [comment removed for export] *)
Definition lp_rows (M : word -> option byte) (lines data W4 k : Z) : Prop :=
  forall i, (0 <= i < k)%Z -> rdn SEGS M (Z_to_bv 64 (lines + 8 * i)) 8 = Some (Z_to_le_bytes 8 (data + W4 * i)).

Lemma lp_loop : forall (n : nat) (fx : FPState) regs (M0 M : word -> option byte) (lines data wpl h i : Z),
  Z.of_nat n = (h - i)%Z -> (0 <= i < h)%Z -> (h <= 20000)%Z -> (1 <= wpl <= 20000)%Z -> (4096 <= lines)%Z -> (lines + 8 * h <= 2 ^ 47)%Z ->
  (1 <= data)%Z -> (data + 4 * wpl * h <= 2 ^ 47)%Z ->
  store_ok SEGS M0 (Z_to_bv 64 lines) (Z.to_nat (8 * h)) = true -> rinv [(lines, (8 * h)%Z)] M0 M -> lp_rows M lines data (4 * wpl) i ->
  getr regs 9 = Z_to_bv 64 (8 * h) -> getr regs 10 = Z_to_bv 64 lines -> getr regs 11 = Z_to_bv 64 (8 * i) -> getr regs 12 = Z_to_bv 64 i ->
  getr regs 13 = Z_to_bv 64 wpl -> getr regs 14 = Z_to_bv 64 data -> getr regs 15 = Z_to_bv 64 (2 ^ 64 - 1 - lines) ->
  getr regs 16 = Z_to_bv 64 0 -> getr regs 17 = Z_to_bv 64 1 ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 LP_LOOP) M rom)
    (fun fin => exists regs' M', fin = @mkst fx regs' (Z_to_bv 64 LP_EXIT) M' rom /\ rinv [(lines, (8 * h)%Z)] M0 M' /\ lp_rows M' lines data (4 * wpl) h /\
                regs_agree (fun r => In r [5; 6; 7; 11; 12]%list) regs regs').
Proof.
  induction n as [|n IH]; intros fx regs M0 M lines data wpl h i Hn Hi Hh Hw Hl1 Hl2 Hd1 Hd2 SOK RI ROWS H9 H10 H11 H12 H13 H14 H15 H16 H17.
  { lia. }
  assert (SOKi : store_ok SEGS M (Z_to_bv 64 (lines + 8 * i)) 8 = true).
  { eapply reg_sok; [exact (proj1 RI) | exact SOK | lia | rewrite Z2Nat.id by lia; lia | lia
                    | rewrite Z2Nat.id by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia]. }
  assert (Hiw : (0 <= i * wpl < 2 ^ 31)%Z) by nia.
  assert (Hrow : (data + 4 * wpl * i + 4 * wpl <= 2 ^ 47)%Z) by nia.
  set (M1 := wbytes M (Z_to_bv 64 (lines + 8 * i)) (word_to_le_bytes 8 (Z_to_bv 64 (data + 4 * wpl * i)))).
  assert (RI1 : rinv [(lines, (8 * h)%Z)] M0 M1).
  { subst M1. eapply rinv_wbytes; [exact RI | rewrite ?length_N_to_le_bytes; reflexivity | lia | lia |].
    eexists. split; [left; reflexivity | cbn [fst snd]; lia]. }
  assert (ROWS1 : lp_rows M1 lines data (4 * wpl) (i + 1)).
  { intros k Hk. subst M1. destruct (Z.eq_dec k i) as [->|Hne].
    - rewrite rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity.
    - rewrite rdn_wbytes_out_Z by (rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). apply ROWS. lia. }
  remember (2 ^ 64 - 1 - lines)%Z as nl eqn:Enl.
  ex_entry regs [lines; (8 * i)%Z; i; wpl; data; (8 * h)%Z; nl] HR.
  assert (HK : know_ok SEGS (ex_env regs [lines; (8 * i)%Z; i; wpl; data; (8 * h)%Z; nl]) M
                 [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 33) 0 160000; KRange (EVar 34) 0 20000; KRange (EVar 35) 1 20001;
                  KRange (EVar 36) 1 (2 ^ 47); KRange (EVar 37) 8 160001; KRange (EVar 38) (2 ^ 64 - 2 ^ 47) (2 ^ 64)]).
  { ex_know regs. }
  destruct (Z.eq_dec (i + 1) h) as [Elast | Emore].
  - ex_run 200%nat [LP_LOOP; LP_EXIT] (SCR [false; false; false] [] []) HR HK R' HR' Hms.
    all: try (lp_sc).
    all: lazymatch goal with |- reach _ _ _ => idtac | _ => idtac "LP-SIDE-LEFT"; fail end.
    apply (reach_msteps _ _ (@mkst fx R' (Z_to_bv 64 LP_EXIT) M1 rom)).
    { subst M1. (lp_mem regs Hms). }
    apply reach_done. exists R', M1. split; [reflexivity |]. split; [exact RI1 |].
    split; [replace h with (i + 1)%Z by lia; exact ROWS1 |]. ex_agree HR HR'.
  - ex_run 200%nat [LP_LOOP; LP_EXIT] (SCR [false; false; true] [] []) HR HK R' HR' Hms.
    all: try (lp_sc).
    all: lazymatch goal with |- reach _ _ _ => idtac | _ => idtac "LP-SIDE-LEFT"; fail end.
    apply (reach_msteps _ _ (@mkst fx R' (Z_to_bv 64 LP_LOOP) M1 rom)).
    { subst M1. (lp_mem regs Hms). }
    assert (AG : regs_agree (fun r => In r [5; 6; 7; 11; 12]%list) regs R') by (ex_agree HR HR').
    subst nl.
    eapply reach_weaken; [| apply (IH fx R' M0 M1 lines data wpl h (i + 1)%Z);
                            first [ assumption | timeout 30 lia | (ex_reg regs HR'; try (lp_val regs)) ] ].   (* timeout-ok: on expiry the next arm runs; without this limit the build exceeds 250 GiB *)
    intros fin (regs' & M' & E & RI' & ROWS' & AG'). exists regs', M'. split; [exact E |]. split; [exact RI' |]. split; [exact ROWS' |].
    eapply regs_agree_trans; [exact AG | exact AG'].
Qed.

(* [comment removed for export] *)
Lemma lp_C : forall (fx : FPState) regs (M : word -> option byte) (s : Z) (ret v8 v9 : word),
  (32 <= s < 2 ^ 63)%Z -> ret_ok ret ->
  rdn SEGS M (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS M (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 v8) ->
  rdn SEGS M (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 v9) -> getr regs 2 = Z_to_bv 64 (s - 32) ->
  reach SEGS (@mkst fx regs (Z_to_bv 64 LP_EXIT) M rom)
    (fun fin => exists regs', fin = @mkst fx regs' ret M rom /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 8 = v8 /\ getr regs' 9 = v9 /\
                regs_agree (fun r => In r [1; 2; 8; 9]%list) regs regs').
Proof.
  intros fx regs M s ret v8 v9 Hs Hret R1 R8 R9 H2.
  pose proof (u64_range ret) as G1. pose proof (u64_range v8) as G8. pose proof (u64_range v9) as G9.
  rewrite <- (zbv_self ret), w2b_Z in R1 by lia. rewrite <- (zbv_self v8), w2b_Z in R8 by lia. rewrite <- (zbv_self v9), w2b_Z in R9 by lia.
  ex_entry regs [(s - 32)%Z; bv_unsigned ret; bv_unsigned v8; bv_unsigned v9] HR.
  assert (HK : know_ok SEGS (ex_env regs [(s - 32)%Z; bv_unsigned ret; bv_unsigned v8; bv_unsigned v9]) M
                 [KRange (EVar 32) 0 (2 ^ 63); KWord (SA (EVar 32) 24) 8 (EVar 33); KWord (SA (EVar 32) 16) 8 (EVar 34);
                  KWord (SA (EVar 32) 8) 8 (EVar 35)]).
  { ex_know regs. }
  ex_run 30%nat (@nil Z) (SCR [] [] []) HR HK R' HR' Hms.
  assert (Q1 : getr R' 1 = ret) by (ex_reg regs HR'; try apply zbv_self).
  assert (Q2 : getr R' 2 = Z_to_bv 64 s) by (ex_reg regs HR').
  assert (Q8 : getr R' 8 = v8) by (ex_reg regs HR'; try apply zbv_self).
  assert (Q9 : getr R' 9 = v9) by (ex_reg regs HR'; try apply zbv_self).
  assert (AG : regs_agree (fun r => In r [1; 2; 8; 9]%list) regs R') by (ex_agree HR HR').
  apply (reach_msteps _ _ (@mkst fx R' (Z_to_bv 64 LP_RET) M rom)).
  { ex_mem regs Hms. }
  unfold reach. eexists. split.
  - unfold LP_RET. norm_pc. stepret F_1ad18 D_1ad18 ret ltac:(exact Q1). apply mst_refl.
  - eexists. split; [reflexivity |]. gres. repeat split; assumption.
Qed.
End Segs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LinePtrsW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Existing Instance exf_fxd | 100.

Definition lines_new (C : lctx) (A A' : AS) (m' : word -> option byte) (lines data wpl h : Z) : Prop :=
  (4096 <= lines)%Z /\ (lines + 8 * h <= alloc_top (c_vm C))%Z /\ (lines mod 16 = 0)%Z /\
  live A (Z_to_bv 64 lines) = None /\ live (c_A0 C) (Z_to_bv 64 lines) = None /\ live A' (Z_to_bv 64 lines) = Some (8 * h)%Z /\
  (forall q, q <> Z_to_bv 64 lines -> live A' q = live A q) /\ lp_rows m' lines data (4 * wpl) h.

Lemma lp_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Lemma pixGetLinePtrs_W : forall (fx : FPState) C A m md regs (s pix h wpl data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + CALLOC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 0 ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> (0 <= pix < 2 ^ 64)%Z -> (1 <= h <= 20000)%Z -> (1 <= wpl <= 20000)%Z -> (1 <= data)%Z -> (data + 4 * wpl * h <= 2 ^ 47)%Z ->
  rdn SEGS m (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS m (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl) ->
  rdn SEGS m (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (alloc_margin (8 * h) <= bR)%Z ->
  (forall A' m' vm' regs' (lines : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 lines -> lines_new C A A' m' lines data wpl h ->
     aroom A' vm' (kR - 1) (bR - alloc_margin (8 * h)) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x1abe0) m al_rom) md) S.
Proof.
  intros fx C A m md regs s pix h wpl data ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Lp Hp Hh Hw Hd1 Hd2 Rh Rw Rd kR bR HRM HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  unfold CALLOC_STACK, ALLOC_STACK in Hlo.
  pose proof (blk_range C A m md _ 64 CK HW Lp ltac:(lia)) as [B1 B2]. rewrite u_Z2bv in B1, B2 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  eapply rz_reach; [exact (w_pure _ _ _ _ HW)
                   | exact (lp_A al_rom fx regs m s pix h ltac:(lia) Hs16 ltac:(lia) ltac:(lia) ALp Hh ltac:(lia) Rh
                              (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H10 H11) |].
  intros fin (r1 & M1 & -> & RI1 & C1 & C2 & C3 & Q1 & Q2 & Q10 & Q11 & Q8 & Q9 & AG1).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1).
  { apply (rinv_WP2 C A A m md M1 [((s - 32)%Z, 32%Z)] s CK HW (sub_live_refl A) Hhi RI1).
    constructor; [left; cbn [fst snd]; lia | constructor]. }
  destruct WP1 as [HW1 PM1].
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl)).
  { rewrite (rinv_rdn SEGS _ m M1 (pix + 16) 4 RI1); [exact Rw | lia | cbn; lia | intros r [<-|[]]; cbn [fst snd]; lia]. }
  assert (Rd1 : rdn SEGS M1 (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data)).
  { rewrite (rinv_rdn SEGS _ m M1 (pix + 56) 8 RI1); [exact Rd | lia | cbn; lia | intros r [<-|[]]; cbn [fst snd]; lia]. }
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x56270) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  apply (W_calloc16_sure C A M1 _ r1 h 8 kR bR (Z_to_bv 64 LP_RA) (s - 32) S CK HW1 Q10 Q11 ltac:(lia) ltac:(lia) ltac:(lia)
           HRM HkR ltac:(rewrite Z.mul_comm; exact HbR) ltac:(unfold ROOM_NMAX; lia) Q1
           ltac:(red; apply bv_eq; reflexivity) Q4 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m1 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQ ZERO AL16 TOP PMa HRMa. rewrite ?with_vmmaps_twice in HWa |- *.
  rewrite Z.mul_comm in L1, HRMa.
  pose proof (u64_range res) as Hru.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (lines := u res) in *. rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
  pose proof (blk_range C A1 m1 _ _ (8 * h) CK HWa L1 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia.
  clearbody lines.
  assert (D1 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). rewrite <- H1. exact C1. }
  assert (D2 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). exact C2. }
  assert (D3 : rdn SEGS m1 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (FRM_rdn16 C (s - 32) M1 m1 (s - 24) 8 CK (proj1 PMa)) by (cbn; lia). exact C3. }
  assert (Rw2 : rdn SEGS m1 (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl)).
  { rewrite (LeptCellsB.LIVK_rdn SEGS A M1 m1 (Z_to_bv 64 pix) 64 (pix + 16) 4 (proj2 PMa) Lp) by (rewrite u_Z2bv by lia; cbn; lia). exact Rw1. }
  assert (Rd2 : rdn SEGS m1 (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data)).
  { rewrite (LeptCellsB.LIVK_rdn SEGS A M1 m1 (Z_to_bv 64 pix) 64 (pix + 56) 8 (proj2 PMa) Lp) by (rewrite u_Z2bv by lia; cbn; lia). exact Rd1. }
  assert (PM1' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E8 : getr r2 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  eapply rz_reach; [exact (w_pure _ _ _ _ HWa)
                   | exact (lp_B al_rom fx r2 m1 s pix h lines wpl data ltac:(lia) ltac:(lia) ltac:(lia) Hh ltac:(lia) ltac:(lia) AL16 Hw
                              ltac:(lia) Rw2 Rd2 E2 Hres E8 E9) |].
  intros fin (r3 & M3 & -> & -> & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & K17 & AG3).
  assert (SOKl : store_ok SEGS m1 (Z_to_bv 64 lines) (Z.to_nat (8 * h)) = true).
  { apply (lp_sok_blk C A1 m1 _ (Z_to_bv 64 lines) (8 * h) lines _ CK HWa L1); rewrite ?u_Z2bv, ?Z2Nat.id by lia; lia. }
  eapply rz_reach; [exact (w_pure _ _ _ _ HWa)
                   | exact (lp_loop al_rom (Z.to_nat h) fx r3 m1 m1 lines data wpl h 0 ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) ltac:(lia) Hw
                              ltac:(lia) ltac:(lia) Hd1 Hd2 SOKl (rinv_refl _ _) ltac:(intros k Hk; lia)
                              K9 K10 ltac:(rewrite K11; reflexivity) ltac:(rewrite K12; reflexivity) K13 K14 K15 K16 K17) |].
  intros fin (r4 & M4 & -> & RI4 & ROWS4 & AG4).
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A s m1 M4).
  { apply (rinv_WP2 C A A1 m1 _ M4 [(lines, (8 * h)%Z)] s CK HWa SUBa Hhi RI4).
    constructor; [right; exists (Z_to_bv 64 lines), (8 * h)%Z; rewrite u_Z2bv by lia; cbn [fst snd]; repeat split; try assumption; lia | constructor]. }
  destruct WP4 as [HW4 PM4].
  assert (F1 : rdn SEGS M4 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (rinv_rdn SEGS _ m1 M4 (s - 8) 8 RI4); [exact D1 | lia | cbn; lia | intros r [<-|[]]; cbn [fst snd]; lia]. }
  assert (F2 : rdn SEGS M4 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (rinv_rdn SEGS _ m1 M4 (s - 16) 8 RI4); [exact D2 | lia | cbn; lia | intros r [<-|[]]; cbn [fst snd]; lia]. }
  assert (F3 : rdn SEGS M4 (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (getr regs 9))).
  { rewrite (rinv_rdn SEGS _ m1 M4 (s - 24) 8 RI4); [exact D3 | lia | cbn; lia | intros r [<-|[]]; cbn [fst snd]; lia]. }
  assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  eapply rz_reach; [exact (w_pure _ _ _ _ HW4)
                   | exact (lp_C al_rom fx r4 M4 s ret (getr regs 8) (getr regs 9) ltac:(lia) Hret F1 F2 F3 Y2) |].
  intros fin (r5 & -> & V2 & V8 & V9 & AG5).
  apply (HK A1 M4 vm1 r5 lines HW4).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1' | exact PM4].
  - csr; reflexivity.
  - split; [lia |]. split; [lia |]. split; [exact AL16 |]. split; [exact L0 |]. split; [exact L00 |]. split; [exact L1 |].
    split; [exact LEQ | exact ROWS4].
  - exact HRMa.
Qed.
End LinePtrsW.
