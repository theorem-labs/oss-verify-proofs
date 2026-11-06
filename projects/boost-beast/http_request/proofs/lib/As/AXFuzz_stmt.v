(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsCXXHeap AsStack0 AXPres AsTRList.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition P_AFUZZ_ENTRY : Z := 0xa3808.     (* [comment removed for export] *)
Definition AFUZZ_RA      : Z := 0xa306c.     (* [comment removed for export] *)
Definition AFUZZ_EMPTY   : Z := 0x65bae0.    (* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFUZZ_STACK : Z := 32768.
(* [comment removed for export] *)
Definition AFUZZ_LIVE : Z := 2^30.
Definition AFUZZ_CNT  : Z := 2100.
(* [comment removed for export] *)
Definition AFUZZ_FRAMES : nat := 16.

(* [comment removed for export] *)
Definition AXH_LO : Z := 0x65bb90.
Definition AXH_HI : Z := 0x65c950.
Definition AXH_X : list (Z * Z) := [(AXH_LO, AXH_HI); (AERRNO, AERRNO + 4)]%Z.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AXRELRO_LO : Z := 0x115000.  Definition AXRELRO_HI : Z := 0x11d000.
Definition AXDATA_LO  : Z := 0x11fa70.  Definition AXDATA_HI  : Z := 0x11fc20.
Definition ACANARY : Z := 0x67d4f0.          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition APF_FUZZ : list (Z * list Z) := APF_a3980.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pristine (m : mem) (lo hi : Z) : Prop := forall a, lo <= a < hi -> m (wa a) = None.
Definition AXImg (m : mem) : Prop := pristine m AXRELRO_LO AXRELRO_HI /\ pristine m AXDATA_LO AXDATA_HI.

(* [comment removed for export] *)
Definition hs_local (HS : mem -> Prop) : Prop :=
  forall m m', HS m -> (forall a, AXH_LO <= a < AXH_HI -> m' (wa a) = m (wa a)) -> HS m'.
Definition hs_initial (HS : mem -> Prop) : Prop :=
  forall m, pristine m AXH_LO AXH_HI -> HS m.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition afuzz_tr_ok (H : asr) : Prop := True.

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  Definition afuzz_cost (N : Z) : Z := as_Cm H (13 * N + 600000000) + as_Cf H (11 * N + 400000).

  Lemma afuzz_cost_nonneg : asan_rt_hyps H -> forall n, 0 <= n -> 0 <= afuzz_cost n.
  Proof.
    intros HH n Hn. pose proof (ah_costs H HH) as (C1 & C2 & C3 & C4 & _). unfold afuzz_cost.
    pose proof (C1 (13 * n + 600000000) ltac:(lia)). pose proof (C3 (11 * n + 400000) ltac:(lia)). lia.
  Qed.
  Lemma afuzz_cost_mono : asan_rt_hyps H -> forall n n', 0 <= n <= n' -> afuzz_cost n <= afuzz_cost n'.
  Proof.
    intros HH n n' Hn. pose proof (ah_costs H HH) as (C1 & C2 & C3 & C4 & _). unfold afuzz_cost.
    pose proof (C2 (13 * n + 600000000) (13 * n' + 600000000) ltac:(lia)).
    pose proof (C4 (11 * n + 400000) (11 * n' + 400000) ltac:(lia)). lia.
  Qed.

  Variable HS : mem -> Prop.

  Definition afuzz_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (N lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (XS : list (Z * Z)),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ Permutation LB' LB
      /\ Forall (fs_scratch H LF) XS
      /\ xpres H LB (bv_unsigned sp) (AXH_X ++ XS) m m'
      /\ HS m'
      (* [comment removed for export] *)
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - afuzz_cost N.

  Definition afuzz_stmt_with : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (CH : list (Z * Z)) (D N lo B shi : Z) (ds : list byte) (errv can : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 P_AFUZZ_ENTRY) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 N ->
      (* [comment removed for export] *)
      bytes_at asegs m D ds -> Z.of_nat (length ds) = N -> N < 2^26 -> D mod 16 = 0 ->
      (1 <= N -> exists pD, In (pD, D, N) LB) -> (N = 0 -> D = AFUZZ_EMPTY) ->
      (* [comment removed for export] *)
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + AFUZZ_LIVE <= as_LIVE_MAX H -> Z.of_nat (length LB) + AFUZZ_CNT <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->
      (* [comment removed for export] *)
      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AFUZZ_STACK ->
      bv_unsigned sp <= 0x7fffffffffff ->
      (* [comment removed for export] *)
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      AXImg m -> bytes_at asegs m ACANARY (word_to_le_bytes 8 can) -> HS m ->
      bv_unsigned ra mod 2 = 0 ->
      (* [comment removed for export] *)
      F = bvmap_empty -> fc = Z_to_bv 32 0 ->
      (* [comment removed for export] *)
      ACONST m ->
      (1 <= N -> addressable m D N) ->
      as_RFS H LF m -> (length LF + AFUZZ_FRAMES <= AFS7_MAXLIVE)%nat ->     (* [comment removed for export] *)
      stack0 m lo shi -> bv_unsigned sp + 64 <= shi ->     (* [comment removed for export] *)
      as_chain H m (bv_unsigned s0) CH -> pf_ok (as_TR H) APF_FUZZ (bv_unsigned ra) CH ->
      (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->     (* [comment removed for export] *)
      afuzz_tr_ok H ->
      afuzz_cost N <= as_AL H s ->
      as_SR H (afuzz_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF N lo B shi m mo)
        (mkCfg msF mo).
End W.

(* [comment removed for export] *)
Definition afuzz_stmt (H : asr) : Prop :=
  exists HS : mem -> Prop, hs_local HS /\ hs_initial HS /\ afuzz_stmt_with H HS.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pristine_agree : forall m m' lo hi,
  pristine m lo hi -> (forall a, lo <= a < hi -> m' (wa a) = m (wa a)) -> pristine m' lo hi.
Proof. intros m m' lo hi P AG a Ha. rewrite AG by exact Ha. apply P. exact Ha. Qed.

Lemma AXImg_agree : forall m m',
  AXImg m -> (forall a, (AXRELRO_LO <= a < AXRELRO_HI \/ AXDATA_LO <= a < AXDATA_HI) -> m' (wa a) = m (wa a)) -> AXImg m'.
Proof.
  intros m m' [P1 P2] AG. split; (eapply pristine_agree; [eassumption|]); intros a Ha; apply AG; [left|right]; exact Ha.
Qed.

End HCW.
