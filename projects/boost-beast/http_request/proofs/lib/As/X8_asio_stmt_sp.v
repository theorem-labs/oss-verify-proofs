(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsIface5 AsIface6 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import X8SRKit X8_A_leaves2.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shc_entry_ok (E : Z) : Prop := E = P_A_SHCOUNT_CTOR_IMPL \/ E = P_A_SHCOUNT_CTOR_STATE.
Definition shc_size (E : Z) : Z := if E =? P_A_SHCOUNT_CTOR_IMPL then SZ_SPCI_IMPL else SZ_SPCI_STATE.
Definition shc_vp (E : Z) : Z := if E =? P_A_SHCOUNT_CTOR_IMPL then AVP_SPCI_IMPL else AVP_SPCI_STATE.
Definition ASHCOUNT_CTOR_STACK : Z := 48 + AOPNEW_STACK.

Lemma shc_size_eq : forall E, shc_entry_ok E -> (E = P_A_SHCOUNT_CTOR_IMPL /\ shc_size E = 96 /\ shc_vp E = AVP_SPCI_IMPL)
                                               \/ (E = P_A_SHCOUNT_CTOR_STATE /\ shc_size E = 312 /\ shc_vp E = AVP_SPCI_STATE).
Proof. intros E [-> | ->]; [left| right]; repeat split; reflexivity. Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Section W.
  Variable H : asr.

Definition shcount_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (E : Z) (s : as_St H) (LB : list block) (LF : list fframe) (PC lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (q : Z) j7 junk,
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range q (shc_size E) /\ as_RHEAP H s' ((p, q, shc_size E) :: LB) m'
    /\ rw_cells asegs m' PC [C8 (Z_to_bv 64 q)]
    /\ rw_cells asegs m' q (SpcHdrCells (mkSPC (shc_vp E) 1 1 0) j7)
    /\ rw_cells asegs m' (q + 32) [CB (Z.to_nat (shc_size E - 32)) junk]
    /\ addressable m' q (shc_size E)
    /\ xpres H LB (bv_unsigned sp) [(PC, PC + 8)]%Z m m'
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cm H (shc_size E).

Definition shcount_ctor_stmt (E : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (PC lo B shi : Z) (errv : word) (jpc : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 E) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 PC -> a1 = Z_to_bv 64 0 ->
    rw_cells asegs m PC [CB 8 jpc] -> bv_unsigned sp <= PC -> PC + 8 <= shi -> PC mod 8 = 0 ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + shc_size E <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ASHCOUNT_CTOR_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_Cm H (shc_size E) <= as_AL H s ->
    as_SR H (shcount_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc E s LB LF PC lo B shi m mo)
      (mkCfg msF mo).

End W.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AANYEX_COPY_STACK : Z := 32.     (* [comment removed for export] *)
Definition AANYEX_MOVE_STACK : Z := 48.     (* [comment removed for export] *)

Definition anyex_copy_post (ra sp gp tp s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (D S ioc lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 a4 a5 a6 m' jm,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + 48)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' D [C8 (wz ioc); CB 16 jm; C8 (wz AT_ANYEX_OBJECT_FNS); C8 (wz D); C8 (wz AT_ANYEX_TARGET_FNS)].

Definition anyex_copy_stmt : Prop :=
  forall (D S ioc lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (jd j16 : list byte),
  rw_cells asegs m D [CB 48 jd] -> ro_cells asegs m S (AnyExecCells S ioc j16) -> AXStatics2 m ->
  stk asegs m lo (bv_unsigned sp) -> lo + AANYEX_COPY_STACK <= bv_unsigned sp -> aceil <= lo ->
  (D + 48 <= lo \/ bv_unsigned sp <= D) -> (S + 56 <= lo \/ bv_unsigned sp <= S) -> (S + 56 <= D \/ D + 48 <= S) ->
  0 <= ioc < 2^64 -> 0 < S -> bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> accessible m S 48 -> S mod 8 = 0 -> accessible m D 48 -> D mod 8 = 0 -> oloc D 48 ->
  evt asegs (anyex_copy_post ra sp gp tp s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc D S ioc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_ANYEX_COPY) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
Definition anyex_move_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (D S ioc lo : Z) (j16 : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 a7 m' jm,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (D, D + 48); (S, S + 48)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' D [C8 (wz ioc); CB 16 jm; C8 (wz AT_ANYEX_OBJECT_FNS); C8 (wz D); C8 (wz AT_ANYEX_TARGET_FNS)]
    /\ rw_cells asegs m' S [C8 (wz ioc); CB 16 j16; C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz AT_ANYEX_PROP_FNS)].

Definition anyex_move_stmt : Prop :=
  forall (D S ioc lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (jd j16 : list byte),
  rw_cells asegs m D [CB 48 jd] -> rw_cells asegs m S (AnyExecCells S ioc j16) -> AXStatics2 m ->
  stk asegs m lo (bv_unsigned sp) -> lo + AANYEX_MOVE_STACK <= bv_unsigned sp -> aceil <= lo ->
  (D + 48 <= lo \/ bv_unsigned sp <= D) -> (S + 56 <= lo \/ bv_unsigned sp <= S) -> (S + 56 <= D \/ D + 48 <= S) ->
  0 <= ioc < 2^64 -> 0 < S -> bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> accessible m S 48 -> S mod 8 = 0 -> oloc S 48 -> accessible m D 48 -> D mod 8 = 0 -> oloc D 48 ->
  evt asegs (anyex_move_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc D S ioc lo j16 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) (wz S) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_ANYEX_MOVE) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASPLITBUF_DTOR_STACK : Z := 16.
Definition AVEC_READOP_RESERVE_STACK : Z := 64.
Definition AVEC_READOP_DESTROY_STACK : Z := 32.

Definition splitbuf_statep_dtor_nil_post (ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition splitbuf_statep_dtor_nil_stmt : Prop :=
  forall (T e c lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells asegs m T [C8 (wz 0); C8 (wz e); C8 (wz e); C8 (wz c)] ->
  0 <= e < 2^64 -> 0 <= c < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo + ASPLITBUF_DTOR_STACK <= bv_unsigned sp -> aceil <= lo ->
  (T + 32 <= lo \/ bv_unsigned sp <= T) ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> accessible m T 32 -> T mod 8 = 0 ->
  evt asegs (splitbuf_statep_dtor_nil_post ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_SPLITBUF_STATEP_DTOR) fc None m (seg_rom asegs)).

Definition vec_readop_reserve0_post (ra sp gp tp s0 s1 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a2 a3 a4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition vec_readop_reserve0_stmt : Prop :=
  forall (V vb ve vc lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells asegs m V [C8 (wz vb); C8 (wz ve); C8 (wz vc)] -> 0 <= vb < 2^64 -> 0 <= vc < 2^64 ->
  stk asegs m lo (bv_unsigned sp) -> lo + AVEC_READOP_RESERVE_STACK <= bv_unsigned sp -> aceil <= lo ->
  (V + 24 <= lo \/ bv_unsigned sp <= V) ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> accessible m V 24 -> V mod 8 = 0 ->
  evt asegs (vec_readop_reserve0_post ra sp gp tp s0 s1 (wz 0) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz V) (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_VEC_READOP_RESERVE) fc None m (seg_rom asegs)).

Definition vec_readop_destroy_nil_post (ra sp gp tp s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition vec_readop_destroy_nil_stmt : Prop :=
  forall (D V lo : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells asegs m D [C8 (wz V)] -> ro_cells asegs m V [C8 (wz 0)] ->
  stk asegs m lo (bv_unsigned sp) -> lo + AVEC_READOP_DESTROY_STACK <= bv_unsigned sp -> aceil <= lo ->
  (D + 8 <= lo \/ bv_unsigned sp <= D) -> (V + 8 <= lo \/ bv_unsigned sp <= V) ->
  0 < V -> bv_unsigned ra mod 2 = 0 ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  ACONST m -> accessible m D 8 -> D mod 8 = 0 -> accessible m V 8 -> V mod 8 = 0 ->
  evt asegs (vec_readop_destroy_nil_post ra sp gp tp s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_A_VEC_READOP_DESTROY) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMAKE_SHARED_IMPL_STACK : Z := 64 + ASHCOUNT_CTOR_STACK.

Section W4.
  Variable H : asr.

Definition make_shared_impl_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : as_St H) (LB : list block) (LF : list fframe) (R lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
  fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (p : bptr) (q : Z),
    as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
    /\ rblock_range q SZ_SPCI_IMPL /\ as_RHEAP H s' ((p, q, SZ_SPCI_IMPL) :: LB) m'
    /\ rw_cells asegs m' R [C8 (wz (q + O_SPC_STORAGE)); C8 (wz q)]
    /\ AImplBlock ((p, q, SZ_SPCI_IMPL) :: LB) m' q (mkIMPL (mkSPC AVP_SPCI_IMPL 1 1 1) 0 0 [] 0)
    /\ AXStatics2 m'
    /\ xpres H LB (bv_unsigned sp) [(R, R + 16)]%Z m m'
    /\ accessible m' R 16
    /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
    /\ as_AL H s' >= as_AL H s - as_Cm H SZ_SPCI_IMPL.

Definition make_shared_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
         (s : as_St H) (LB : list block) (LF : list fframe) (R lo B shi : Z) (errv : word) (jr : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 P_A_MAKE_SHARED_IMPL) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 R ->
    rw_cells asegs m R [CB 16 jr] -> aobj LB LF R 16 -> R mod 8 = 0 -> accessible m R 16 ->
    AXStatics2 m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
    lb_bytes LB + SZ_SPCI_IMPL <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AMAKE_SHARED_IMPL_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned ra mod 2 = 0 ->
    (* [comment removed for export] *)
    bv_unsigned sp mod 16 = 0 ->
    as_RFS H LF m -> ACONST m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
    as_Cm H SZ_SPCI_IMPL <= as_AL H s ->
    as_SR H (make_shared_impl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF R lo B shi m mo)
      (mkCfg msF mo).

End W4.

End HCW.
