(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_arrlA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition acc_postB (E : aenvA) (FR : Z) (G : Z -> Z -> Prop) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (c0 c1 : Z),
    ms' = MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz c0) (wz c1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom asegs)
    /\ frm0 fc' /\ munch [(q - FR, q)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' (ae_lo E) q /\ G c0 c1.

Definition acc_stmtB (E : aenvA) (H FR : Z) (G : Z -> Z -> Prop) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q node : Z),
    stk asegs m (ae_lo E) q -> ae_lo E + FR <= q -> q <= ae_hi E -> q mod 16 = 0 -> mem_inv asegs m -> frm0 fc ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> (node + 16 <= q - FR \/ q <= node) -> node + 16 < 2^63 ->
    (forall m', munch [(q - FR, q)] m m' -> AINV_A E m') ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shb_cells m') ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    evt asegs (acc_postB E FR G ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz H) fc None m (seg_rom asegs)).

Definition acc_stmtSB (E : aenvA) (H FR : Z) (G : Z -> Z -> Prop) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (q node : Z),
    stk asegs m (ae_lo E) q -> ae_lo E + FR <= q -> q <= ae_hi E -> q mod 16 = 0 -> mem_inv asegs m -> frm0 fc ->
    rw_cells asegs m node [C8 (wz (ae_DOC E)); C8 (wz 1)] -> 0 < node -> (node + 16 <= q - FR \/ q <= node) -> node + 16 < 2^63 ->
    (forall m', munch [(q - FR, q)] m m' -> AINV_A E m') ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shb_cells m') ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' node 16) ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' (ae_DOC E) 16) ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' (ae_TAPE E) (8 * ae_n E)) ->
    (forall m', munch [(q - FR, q)] m m' -> wmono asegs m m' -> shz m' (ae_SBUF E) (ae_NS E)) ->
    evt asegs (acc_postB E FR G ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m)
      (MS (mkR ra (wz q) gp (wz TPV) t0 t1 t2 s0 s1 (wz node) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz H) fc None m (seg_rom asegs)).
Lemma acc_stmt_SB : forall E H FR G, acc_stmtB E H FR G -> acc_stmtSB E H FR G.
Proof. intros E H FR G X. unfold acc_stmtSB. intros. eapply X; eassumption. Qed.

Lemma shl8_shr8_tval : forall x, 0 <= x -> Z.shiftr (Z.land (Z.shiftl x 8) 18446744073709551615) 8 = tval x.
Proof. intros x Hx. rewrite zb_shl_shr_land by lia. unfold tval. change (2 ^ (64 - 8) - 1) with (Z.ones 56). rewrite Z.land_ones by lia. reflexivity. Qed.

Definition G_int (c0 c1 : Z) : Prop := 0 <= c0 < 2^64 /\ 0 <= c1 <= 18.

Definition G_dbl (c0 c1 : Z) : Prop := 0 <= c0 <= 17 /\ 0 <= c1 < 2^64.

Lemma land_le_r : forall a b, 0 <= b -> 0 <= Z.land a b <= b.
Proof.
  intros a b Hb. split; [apply Z.land_nonneg; right; exact Hb|].
  rewrite Z.land_comm. pose proof (Z.sub_land_same_l b a). pose proof (proj2 (Z.land_nonneg b (Z.lnot a)) (or_introl Hb)). lia.
Qed.

Lemma sub_fp_acc_tix : forall q, sub_fp [(q + -48 + -16, q + -48)] [(q - 64, q)].
Proof. intros q x Hx. cbn [outside] in *. lia. Qed.
Lemma sub_fp_acc_own : forall q, sub_fp [(q + -48, q)] [(q - 64, q)].
Proof. intros q x Hx. cbn [outside] in *. lia. Qed.

Lemma sub_fp_1 : forall a b c d, c <= a -> b <= d -> sub_fp [(a, b)] [(c, d)].
Proof. intros a b c d H1 H2 x Hx. cbn [outside] in *. lia. Qed.

Definition G_any (c0 c1 : Z) : Prop := True.

Ltac w_range := lazymatch goal with |- 0 <= bv_unsigned ?w < _ => pose proof (bv_unsigned_in_range 64 w) as X; unfold bv_modulus in X; cbn in X; lia end.
Ltac g_int := unfold G_int; split; [w_range| first [rewrite a_u64_small by lia; lia
  | lazymatch goal with |- 0 <= bv_unsigned (Z_to_bv 64 (Z.land ?x ?k)) <= _ => pose proof (land_le_r x k ltac:(lia)); rewrite a_u64_small by lia; lia end
  | lazymatch goal with |- 0 <= bv_unsigned ?w <= _ => pose proof (bv_unsigned_in_range 64 w); lia end]].
Ltac g_dbl := unfold G_dbl; split; [first [rewrite a_u64_small by lia; lia| lazymatch goal with |- 0 <= bv_unsigned ?w <= _ => pose proof (bv_unsigned_in_range 64 w); lia end]| w_range].
