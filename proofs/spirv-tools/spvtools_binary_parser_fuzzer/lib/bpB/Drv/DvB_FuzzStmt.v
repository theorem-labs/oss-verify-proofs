(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma lb_small_le : forall LB, lb_small LB <= 64512 * Z.of_nat (length LB).
Proof.
  induction LB as [|b LB IH]; [cbn; lia|]. rewrite lb_small_cons. cbn [length].
  assert (N2 : nsmall (blk_size b) <= 64512) by (unfold nsmall; destruct (Z.leb_spec (blk_size b) 64512); lia). lia.
Qed.
Lemma nlarge_bound : forall LB, 0 <= nlarge LB <= Z.of_nat (length LB).
Proof. induction LB as [|b LB IH]; [cbn; lia|]. rewrite nlarge_cons. cbn [length]. pose proof (nlg_bounds (blk_size b)). lia. Qed.
Lemma lb_small_perm : forall LB LB', Permutation LB' LB -> lb_small LB' = lb_small LB.
Proof. intros LB LB' P. induction P; rewrite ?lb_small_cons in *; lia. Qed.
Lemma nlarge_perm : forall LB LB', Permutation LB' LB -> nlarge LB' = nlarge LB.
Proof. intros LB LB' P. induction P; rewrite ?nlarge_cons in *; lia. Qed.

Definition P_FUZZ_ENTRY : Z := 0xe8894.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition AFUZZ_STACK : Z := 65536.

Definition AFUZZ_EMPTY : Z := 0x6c36a0.

Record fuzz_params : Type := FZP {
  fz_cost  : Z -> Z;
  fz_tr_ok : asr -> Prop;
  fz_pf    : list (Z * list Z);
  fz_inv   : mem -> Prop;

  fz_small : Z;
  fz_cnt   : Z;
  fz_large : Z
}.

Section W.
  Variable H : asr.
  Variable P : fuzz_params.

  Definition fuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (N lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (XS : list (Z * Z))
                    (F' : bvmap 5 word) (fc' : bv 32),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ FPSteps.frm_zero fc'
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Permutation LB' LB
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XS) m m'

      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - fz_cost P N
      /\ fz_inv P m'.

  Definition fuzz_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (D N lo B shi : Z) (ds : list byte) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_FUZZ_ENTRY) fc None m (seg_rom asegs) ->
      FPSteps.frm_zero fc ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N ->

      bytes_at asegs m D ds -> Z.of_nat (length ds) = N -> N < 2^26 -> D mod 16 = 0 ->
      (1 <= N -> exists pD, In (pD, D, N) LB) -> (N = 0 -> D = AFUZZ_EMPTY) ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_small LB + fz_small P <= RT_SMALL_MAX -> Z.of_nat (length LB) + fz_cnt P <= RT_CNT_MAX -> nlarge LB + fz_large P <= RT_LARGE_MAX ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFUZZ_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      fz_inv P m ->
      bv_unsigned ra mod 2 = 0 ->

      ACONST m ->
      (1 <= N -> addressable m D N) ->
      as_RFS H LF m -> (length LF + 16 <= AFS_MAXLIVE_BP)%nat ->
      stack0 m lo shi -> bv_unsigned sp <= shi ->
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) (fz_pf P) (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      fz_tr_ok P H ->
      fz_cost P N <= as_AL H s ->
      as_SR H (fuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF N lo B shi m mo)
        (mkCfg msF mo).

  Definition fz_cost_nonneg : Prop := forall n, 0 <= n -> 0 <= fz_cost P n.
  Definition fz_cost_mono : Prop := forall n n', 0 <= n <= n' -> fz_cost P n <= fz_cost P n'.

  Definition fz_params_ok : Prop :=
    fz_cost_nonneg /\ fz_cost_mono /\ 0 <= fz_small P /\ 0 <= fz_cnt P /\ 0 <= fz_large P
    /\ fz_small P + 3 * 64512 <= RT_SMALL_MAX /\ fz_cnt P + 3 <= RT_CNT_MAX /\ fz_large P + 3 <= RT_LARGE_MAX.
End W.

End HCW.
