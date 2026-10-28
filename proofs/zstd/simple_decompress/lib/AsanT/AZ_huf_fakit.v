(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface AZ_huf_iface3 AZ_kx AZ_hufkit AZ_hufkit2 AZ_huf_lbkit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Lemma a_land_ff0000 : forall x, 0 <= x -> Z.land x 16711680 = ((x / 65536) mod 256) * 65536.
Proof.
  intros x Hx.
  change 16711680 with (Z.shiftl (Z.ones 8) 16).
  change 256 with (2^8). rewrite <- (Z.land_ones (x / 65536) 8) by lia.
  change 65536 with (2^16). rewrite <- Z.shiftr_div_pow2, <- Z.shiftl_mul_pow2 by lia.
  apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec.
  destruct (Z_lt_le_dec k 16) as [L|L].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec by lia. rewrite Z.land_spec, Z.shiftr_spec by lia. replace (k - 16 + 16) with k by lia. reflexivity.
Qed.

Lemma a_hdr_log11 : forall dth : list byte, Z.of_nat (length dth) = 4 ->
  Z.land (bv_unsigned (Z_to_bv 64 (extz true 4 (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat 0) dth)))))) 16711680 = 720896 ->
  nth_error dth 2 = Some (Z_to_bv 8 11).
Proof.
  intros dth HL H.
  destruct dth as [|d0 [|d1 [|d2 [|d3 [|? ?]]]]]; cbn [length] in HL; try lia.
  change (Z.to_nat 0) with 0%nat in H. cbn [skipn firstn] in H.
  rewrite Bytes.bytes_le_to_Z_le_val in H. cbn [map Bytes.le_val] in H.
  pose proof (bv_unsigned_in_range 8 d0) as R0. pose proof (bv_unsigned_in_range 8 d1) as R1.
  pose proof (bv_unsigned_in_range 8 d2) as R2. pose proof (bv_unsigned_in_range 8 d3) as R3.
  unfold bv_modulus in *. change (2 ^ Z.of_N 8) with 256 in *.
  set (u := bv_unsigned d0 + 256 * (bv_unsigned d1 + 256 * (bv_unsigned d2 + 256 * (bv_unsigned d3 + 256 * 0)))) in *.
  assert (HU : 0 <= u < 2^32) by (unfold u; lia).
  unfold extz in H. change (8 * N.of_nat 4)%N with 32%N in H.
  rewrite Z_to_bv_unsigned, AS.PropExec.bv_wrap64_mod in H.
  assert (E : exists k, 0 <= bv_swrap 32 u mod 2^64 /\ bv_swrap 32 u mod 2^64 = u + k * 2^32).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32).
    change (2^32 / 2) with (2^31).
    destruct (Z_lt_le_dec u (2^31)) as [S|S].
    - exists 0. rewrite (Z.mod_small (u + 2^31) (2^32)) by lia. rewrite Z.mod_small by lia. lia.
    - exists (2^32 - 1).
      replace ((u + 2^31) mod 2^32) with (u - 2^31)
        by (rewrite <- (Z.mod_add (u + 2^31) (-1) (2^32)) by lia; rewrite Z.mod_small by lia; lia).
      replace (u - 2^31 - 2^31) with (u - 2^32) by lia.
      replace ((u - 2^32) mod 2^64) with (u - 2^32 + 2^64)
        by (rewrite <- (Z.mod_add (u - 2^32) 1 (2^64)) by lia; rewrite Z.mod_small by lia; lia).
      lia. }
  destruct E as (k & E0 & E). rewrite a_land_ff0000 in H by exact E0. rewrite E in H.
  assert (D2 : bv_unsigned d2 = 11).
  { assert (((u + k * 2^32) / 65536) mod 256 = bv_unsigned d2).
    { replace (u + k * 2^32) with (bv_unsigned d0 + 256 * bv_unsigned d1 + (bv_unsigned d2 + 256 * (bv_unsigned d3 + k * 256)) * 65536) by (unfold u; lia).
      rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned d0 + 256 * bv_unsigned d1)) by lia.
      rewrite Z.add_0_l. rewrite Z.mul_comm with (n := 256), Z.mod_add by lia. apply Z.mod_small. lia. }
    lia. }
  cbn [nth_error]. f_equal. apply bv_eq. rewrite D2. rewrite Z_to_bv_unsigned. reflexivity.
Qed.


(* [comment removed for export] *)
Definition fa_hb_expr (j : nat) : expr :=
  (EAluw ALU_SRL (EMd M_MUL (ELit 16843009) (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (ELit (-1))) (ELit 1)) (ELit 1431655765)))) (ELit (-1))) (ELit 858993459)) (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (ELit (-1))) (ELit 1)) (ELit 1431655765)))) (ELit (-1))) (ELit 2)) (ELit 858993459))) (ELit 4)) (EAlu ALU_ADD (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (ELit (-1))) (ELit 1)) (ELit 1431655765)))) (ELit (-1))) (ELit 858993459)) (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (EMd M_MUL (ELit (-1)) (EAlu ALU_AND (EAlu ALU_SRL (EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (EAlu ALU_SRL (EAlu ALU_OR (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (EAlu ALU_SRL (EAlu ALU_OR (EVar j) (EAlu ALU_SRL (EVar j) (ELit 1))) (ELit 2))) (ELit 4)))) (ELit (-1))) (ELit 1)) (ELit 1431655765)))) (ELit (-1))) (ELit 2)) (ELit 858993459)))) (ELit 252645135))) (ELit 24)).

(* [comment removed for export] *)
Definition famtZ (v : Z) : Z :=
  if v =? 0 then 0 else -1 * Z.lxor (bv_unsigned (edenot (kx_cenv (Z_to_bv 64 v)) (fa_hb_expr 0))) 31 + 8.

Lemma famtZ_eq : forall E j, bv_unsigned (ev E j) <> 0 ->
  -1 * Z.lxor (bv_unsigned (edenot E (fa_hb_expr j))) 31 + 8 = famtZ (bv_unsigned (ev E j)).
Proof.
  intros E j H. unfold famtZ. rewrite (proj2 (Z.eqb_neq _ _) H). rewrite Z_to_bv_bv_unsigned.
  rewrite (edenot_only j E (kx_cenv (ev E j)) (fa_hb_expr j)); [reflexivity | | reflexivity].
  cbn [evars_only fa_hb_expr andb]. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma famtZ_0 : famtZ 0 = 0.
Proof. reflexivity. Qed.

Lemma famtZ_range : forall v, 0 <= v <= 255 -> 0 <= famtZ v <= 8.
Proof.
  intros v Hv.
  assert (C : forallb (fun k => let f := famtZ (Z.of_nat k) in (0 <=? f) && (f <=? 8)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C (Z.to_nat v) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in C by lia.
  cbv zeta in C. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2. lia.
Qed.

(* [comment removed for export] *)
Lemma lbw_init : forall (x y : word), EVENW x -> bv_unsigned y <= 8 -> LBW 8 (alu64 ALU_SLL (alu64 ALU_ADD x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hx Hy. change (LBW 8) with (LBW (0 + 8)). apply lbw_sll; [apply lbw_add1; exact Hx | | lia].
  pose proof (bv_unsigned_in_range 64 y). rewrite Z.mod_small by lia. exact Hy.
Qed.
Lemma lbw_init_or : forall (x y : word), bv_unsigned y <= 8 -> LBW 8 (alu64 ALU_SLL (alu64 ALU_OR x (Z_to_bv 64 1)) y).
Proof.
  intros x y Hy. change (LBW 8) with (LBW (0 + 8)). apply lbw_sll; [apply lbw_or1 | | lia].
  pose proof (bv_unsigned_in_range 64 y). rewrite Z.mod_small by lia. exact Hy.
Qed.

(* [comment removed for export] *)
Ltac fa_lb_init KXA HC :=
  lazymatch goal with
  | |- LBW 8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_ADD ?x (ELit 1)) (EVar ?a))) =>
      change (LBW 8 (alu64 ALU_SLL (alu64 ALU_ADD (edenot E x) (Z_to_bv 64 1)) (ev E a)));
      apply lbw_init; [u41_even | rewrite (KXA a) by (cbn [length]; lia); cbn [znth nth]; rewrite u_small by lia; lia]
  | |- LBW 8 (edenot ?E (EAlu ALU_SLL (EAlu ALU_OR ?x (ELit 1)) (EVar ?a))) =>
      change (LBW 8 (alu64 ALU_SLL (alu64 ALU_OR (edenot E x) (Z_to_bv 64 1)) (ev E a)));
      apply lbw_init_or; rewrite (KXA a) by (cbn [length]; lia); cbn [znth nth]; rewrite u_small by lia; lia
  | |- ?G => fail 1 "fa_lb_init: unexpected container" G
  end.

(* [comment removed for export] *)
Ltac fa_set_a4 NEW TAC :=
  lazymatch goal with
  | |- evtF ?segs ?RNG ?Q (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16 ?x17 ?x18 ?x19 ?x20
                          ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) ?F ?pc ?fc ?rv ?m ?rom) =>
      replace (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)
         with (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 NEW x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F pc fc rv m rom)
         by (f_equal; f_equal; TAC)
  end.
Ltac fa_fix_a4 KR :=
  lazymatch goal with
  | H : bv_unsigned (ev ?E ?j) = 0 |- _ =>
      fa_set_a4 (Z_to_bv 64 (famtZ (bv_unsigned (ev E j))))
        ltac:(first [ apply word_eq_Z | symmetry; apply word_eq_Z ]; rewrite H, famtZ_0; reflexivity);
      kx_fact KR (0 <= bv_unsigned (ev E j) <= 255)
  | H : bv_unsigned (ev ?E ?j) <> 0 |- _ =>
      fold (fa_hb_expr j);
      fa_set_a4 (Z_to_bv 64 (famtZ (bv_unsigned (ev E j)))) ltac:(rewrite (famtZ_eq E j H); reflexivity);
      kx_fact KR (0 <= bv_unsigned (ev E j) <= 255)
  | |- _ => fail "fa_fix_a4: no lastByte path hypothesis"
  end.

(* [comment removed for export] *)
Ltac fa_join HJ REGS :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?m _) =>
      kx_gen_regsF REGS;
      kx_revert_mem m;
      repeat match goal with H : kx_keep _ |- _ => revert H end;
      repeat match goal with
      | |- context [ev ?E ?j] => generalize (ev E j)
      | |- context [edenot ?E ?e] => generalize (edenot E e)
      end;
      repeat match goal with v : kxword |- _ => revert v end;
      exact HJ
  end.

(* [comment removed for export] *)
Ltac fa_keep_lb KXA HC :=
  match goal with
  | AC : rw_cells _ _ _ ?cs |- _ =>
      lazymatch cs with
      | context [C8 (edenot ?E (EAlu ALU_SLL ?a ?b))] =>
          let KB := fresh "KB" in
          assert (KB : kx_keep (LBW 8 (edenot E (EAlu ALU_SLL a b)))) by (unfold kx_keep; fa_lb_init KXA HC)
      end
  end.

(* [comment removed for export] *)
Ltac fa_amt c HC :=
  match goal with
  | K : 0 <= bv_unsigned ?v <= 255 |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (famtZ (bv_unsigned ?v))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      set (c := famtZ (bv_unsigned v)) in *;
      assert (HC : 0 <= c <= 8) by (subst c; apply famtZ_range; exact K); clearbody c; clear K
  | |- _ => fail "fa_amt: no byte-range fact for the a1 amount"
  end.


(* [comment removed for export] *)
Ltac fa_kzs SPV ARGS DST dsz SRC n DT b0 b1 b2 b3 b4 b5 C :=
  constr:([KZRange C 0 8;
           KZRange (n - (b0 + 256 * b1) - (b2 + 256 * b3) - (b4 + 256 * b5) - 6) 8 4294967296;
           KZRange (n - (b0 + 256 * b1) - (b2 + 256 * b3) - 6) 16 4294967296;
           KZRange (n - (b0 + 256 * b1) - 6) 24 4294967296;
           KZRange (SRC + (b0 + 256 * b1) + (b2 + 256 * b3) + (b4 + 256 * b5)) 4096 140737488355313;
           KZRange (SRC + (b0 + 256 * b1) + (b2 + 256 * b3)) 4096 140737488355305;
           KZRange (SRC + (b0 + 256 * b1)) 4096 140737488355297;
           KZRange (b0 + 256 * b1) 8 65535; KZRange (b2 + 256 * b3) 8 65535; KZRange (b4 + 256 * b5) 8 65535;
           KZRange b0 0 255; KZRange b1 0 255; KZRange b2 0 255; KZRange b3 0 255; KZRange b4 0 255; KZRange b5 0 255;
           KZRange SPV 17594333495296 140737488355328; KZRange ARGS 4096 140737488355176; KZRange SRC 4096 140737488355290; KZRange n 30 4294967296;
           KZRange (SRC + n) 4096 140737488355327;
           KZRange DT 4096 140737488355324; KZRange DST 4096 140737488355328; KZRange dsz 1 4294967296; KZRange (DST + dsz) 4097 140737488355328;
           KZAlign ARGS 8; KZAlign DT 4;
           KZWr ARGS 152; KZWr (SPV + -48) 48;
           KZDisj ARGS 152 SRC n; KZDisj ARGS 152 DT 4; KZDisj (SPV + -48) 48 SRC n; KZDisj (SPV + -48) 48 DT 4; KZDisj (SPV + -48) 48 ARGS 152]).
(* [comment removed for export] *)
Ltac fa_pose_ranges KZS :=
  lazymatch KZS with
  | @nil _ => idtac
  | @cons _ (KZRange ?e ?lo ?hi) ?t =>
      let lo' := eval vm_compute in lo in let hi' := eval vm_compute in hi in
      first [ lazymatch goal with _ : lo' <= e <= hi' |- _ => idtac end
            | let H := fresh "GF" in assert (H : lo' <= e <= hi') by (kx_clear_or2; lia)
            | idtac ];
      fa_pose_ranges t
  | @cons _ _ ?t => fa_pose_ranges t
  end.
Ltac fa_facts b0 b1 b2 b3 b4 b5 C :=
  lazymatch goal with
  | |- evtF _ _ (fast_args_post3A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?SPV ?ARGS ?DST ?dsz ?SRC ?n ?DT _ _ _) _ =>
      let K := fa_kzs SPV ARGS DST dsz SRC n DT b0 b1 b2 b3 b4 b5 C in fa_pose_ranges K
  end.
Ltac fa_autoA STOPS b0 b1 b2 b3 b4 b5 C :=
  lazymatch goal with
  | FR : rw_cells _ _ (?SPV' + -48) _
    |- evtF _ _ (fast_args_post3A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?SPV ?ARGS ?DST ?dsz ?SRC ?n ?DT _ _ _) _ =>
      let K := fa_kzs SPV ARGS DST dsz SRC n DT b0 b1 b2 b3 b4 b5 C in
      kx_autoFLA FR [KAUnp ARGS 152; KAUnp SRC n; KAUnp DT 4; KAApp ARGS 152; KAApp (SPV - 48) 48] STOPS 250%nat K
        [(SRC, n); (DT, 4)] [(SRC, n); (DT, 4); (SPV - 48, 48); (ARGS, 152)];
      try kx_cell_lit; try kx_z; try match goal with H : rng_aimg _ |- accP _ _ _ => kx_acc H end
  end.
(* [comment removed for export] *)
Ltac fa_carry UA US UD SPV :=
  lazymatch goal with MUx : munch _ ?m ?mc |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch type of UA with unpoisoned m ?A (?A + _) =>
    lazymatch SPV with SPV =>
    pose proof (unp_carryS m mc A 152 SPV 48 _ _ UA MUx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as UAc;
    pose proof (unp_carryS m mc A 152 SPV 48 _ _ US MUx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as USc;
    pose proof (unp_carryS m mc A 152 SPV 48 _ _ UD MUx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as UDc;
    lazymatch type of UAc with unpoisoned _ ?a (?a + ?k) =>
      pose proof (unpoisoned_unpZ mc a (a + k) a (a + k) UAc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; lia)) as UAz end;
    lazymatch type of USc with unpoisoned _ ?a (?a + ?k) =>
      pose proof (unpoisoned_unpZ mc a (a + k) a (a + k) USc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; lia)) as USz end;
    lazymatch type of UDc with unpoisoned _ ?a (?a + ?k) =>
      pose proof (unpoisoned_unpZ mc a (a + k) a (a + k) UDc ltac:(lia) ltac:(lia) ltac:(unfold KXKEND; lia)) as UDz end
    end end end.
(* [comment removed for export] *)
Ltac fa_ret0 FR STK SPV MU WM AC :=
  kx_mem; zstep; release_frame FR STK SPV;
  apply evtF_done; unfold fast_args_post3A; repeat (lazymatch goal with |- ex _ => eexists end);
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact STK|];
  right; split; [first [left; reflexivity | right; vm_compute; reflexivity]|]; split; [lia|];
  destruct (rw_cells_forget bsegs _ _ _ AC) as [bs Hbs]; exists bs; exact Hbs.

