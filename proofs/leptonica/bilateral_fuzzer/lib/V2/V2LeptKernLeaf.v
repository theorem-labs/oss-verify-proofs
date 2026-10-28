(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac W2Lib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2KernUb V2_code_krng.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := []%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_kernelSetOrigin : Z := 232020.

(* [comment removed for export] *)
Ltac cell4 HK Hlf rb b rk z pfz name :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?m ?kn =>
    lazymatch type of Hlf with
    | log_flat _ ?log =>
      let lk := eval vm_compute in (ex_lookup segs kn log rb rk 4%nat) in
      lazymatch lk with
      | Some (?v, ?scs) =>
          let scs0 := eval vm_compute in (flat_sc kn (SA rb rk) 4%nat ++ scs) in
          pose proof (ex_cell_Z segs E m kn log rb rk 4%nat v scs scs0 (b + rk)%Z z HK Hlf ltac:(lia) ltac:(lia)
                        ltac:(vm_cast_no_check (eq_refl lk)) ltac:(vm_cast_no_check (eq_refl scs0)) ltac:(exW_scs0)
                        ltac:(exW_adenot b rk) ltac:(pfz) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia)) as name
      | _ => fail 100 "cell4: no value at" rb rk
      end
    end
  end.

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Lemma kso_sok : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Lemma kso_seg : forall (fx : FPState) regs m (kel cy cx : Z) (ret : word),
  (1 <= kel)%Z -> (kel + 16 < 2 ^ 64)%Z -> (kel mod 8 = 0)%Z -> store_ok SEGS m (Z_to_bv 64 (kel + 8)) 8 = true ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 kel -> getr regs 11 = Z_to_bv 64 cy -> getr regs 12 = Z_to_bv 64 cx ->
  exists regs',
    msteps SEGS (@mkst fx regs (0x38a54 : word) m al_rom)
      (@mkst fx regs' ret (wbytes (wbytes m (Z_to_bv 64 (kel + 8)) (word_to_le_bytes 4 (Z_to_bv 64 cy)))
                                  (Z_to_bv 64 (kel + 12)) (word_to_le_bytes 4 (Z_to_bv 64 cx))) al_rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10; 13]%list) regs regs'.
Proof.
  intros fx regs m kel cy cx ret Hk Hk64 ALk SOK H1 Hret H10 H11 H12. eexists. split.
  - stepb_ft F_38a54 D_38a54 ltac:(condZ).
    sn F_38a58 D_38a58.
    stepiv F_38a5c D_38a5c (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite ALk; reflexivity).
    stepb_ft F_38a60 D_38a60 ltac:(condZ).
    stepST F_38a64 D_38a64 (Z_to_bv 64 (kel + 8)) (Z_to_bv 64 cy) ltac:(sok_in SOK).
    stepST F_38a68 D_38a68 (Z_to_bv 64 (kel + 12)) (Z_to_bv 64 cx) ltac:(sok_in SOK).
    stepret F_38a6c D_38a6c ret ltac:(first [exact H1 | pin; reflexivity]).
    apply mst_refl.
  - repeat split; gres; pin; try reflexivity. solve_regs_agree.
Qed.

Lemma kernelSetOrigin_W : forall (fx : FPState) C Ar A m md regs (s kel cy cx : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 kel -> getr regs 11 = Z_to_bv 64 cy -> getr regs 12 = Z_to_bv 64 cx ->
  (0 <= kel < 2 ^ 64)%Z -> (0 <= cy < 2 ^ 31)%Z -> (0 <= cx < 2 ^ 31)%Z ->
  live A (Z_to_bv 64 kel) = Some 24%Z -> live Ar (Z_to_bv 64 kel) = None -> live (c_A0 C) (Z_to_bv 64 kel) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     (forall a : word, ~ (kel + 8 <= bv_unsigned a < kel + 16)%Z -> m' a = m a) ->
     rdn SEGS m' (Z_to_bv 64 (kel + 8)) 4 = Some (Z_to_le_bytes 4 cy) ->
     rdn SEGS m' (Z_to_bv 64 (kel + 12)) 4 = Some (Z_to_le_bytes 4 cx) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_kernelSetOrigin) m al_rom) md) S.
Proof.
  intros fx C Ar A m md regs s kel cy cx ret S CK HW SUBr H2 Hlo Hhi H1 Hret H10 H11 H12 Hkel Hcy Hcx Lk LkR Lk0 HK.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (blk_range C A m md _ _ CK HW Lk ltac:(lia)) as [G TOP]. rewrite u_Z2bv in G, TOP by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lk) as (_ & ALk & _). rewrite u_Z2bv in ALk by lia.
  destruct (kso_seg fx regs m kel cy cx ret ltac:(lia) ltac:(lia) (al16_mod8 _ ALk)
              (kso_sok C A m md _ 24 (kel + 8) 8 CK HW Lk ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
              H1 Hret H10 H11 H12) as (r1 & RUN & V10 & AG).
  unfold PC_kernelSetOrigin. replace (Z_to_bv 64 232020) with (0x38a54 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP : W C A M1 md /\ POSTM C Ar s m M1).
  { subst M1.
    apply (WP_blk C Ar A m _ md (Z_to_bv 64 kel) _ 24); [exact CK | | exact Lk | exact LkR | exact Lk0 | exact SUBr | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    apply (WP_blk C Ar A m _ md (Z_to_bv 64 kel) _ 24); [exact CK | | exact Lk | exact LkR | exact Lk0 | exact SUBr | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    split; [exact HW | apply POSTM_refl]. }
  destruct WP as [HW1 PM1].
  apply (HK M1 r1 HW1).
  - apply cs_kept_intro; csr; reflexivity.
  - exact PM1.
  - intros a Ha. subst M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity.
  - subst M1. rewrite <- (w2b_Z 4 cy) by lia. rdn_chain.
  - subst M1. rewrite <- (w2b_Z 4 cx) by lia. rdn_chain.
  - exact V10.
Qed.
End Chain.
