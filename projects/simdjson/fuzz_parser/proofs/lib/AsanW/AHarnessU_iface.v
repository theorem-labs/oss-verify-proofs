(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface Stdio_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AU_kit AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Export AU_consts.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Export ADkModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition harness_invA (m : amem) : Prop := client_img m /\ client_sh m.

(* [comment removed for export] *)
Definition client_wr : list (Z * Z) :=
  [(0x642200, 0x642208); (0x642220, 0x642222); (0x6422a0, 0x6422cc); (0x642300, 0x642302)].
Definition harness_pres (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  magree asegs (fun a => aclient_addr CI LB SP a /\ outside client_wr a) m m'.
Lemma harness_pres_of_aheap_pres : forall CI LB SP m m', aheap_pres CI LB SP m m' -> harness_pres CI LB SP m m'.
Proof. intros CI LB SP m m' H a Ha [Hc _]. exact (H a Ha Hc). Qed.

(* [comment removed for export] *)
Definition HU_TRACES : list (list Z) :=
  [[AMALLOC_PC; AOPNEW_RET];
   [AFREE_PC; 0x95b88]; [AFREE_PC; 0x95b90]; [AFREE_PC; 0x96580];          (* [comment removed for export] *)
   [AFREE_PC; 0xc0790]; [AFREE_PC; 0xc07b8]; [AFREE_PC; 0xc07fc];            (* [comment removed for export] *)
   [AFREE_PC; 0x959ec; 0x95758];                                             (* [comment removed for export] *)
   (* [comment removed for export] *)
   [AFREE_PC; 0x9a8b0; 0x95fbc]; [AFREE_PC; 0x9fc20; 0x95fbc]; [AFREE_PC; 0xa0228; 0x95fbc]]%Z.
Definition HU (L : alayout) : Prop := Forall (fun tr => In tr (al_U L)) HU_TRACES.

(* [comment removed for export] *)
Definition client_static0 (m : amem) : Prop :=
  rw_cells asegs m AACTIVE [C8 w0] /\ rw_cells asegs m AACTIVE_GUARD guard0
  /\ rw_cells asegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] /\ rw_cells asegs m AFALLBACK_GUARD guard0.
Definition client_static1 (m : amem) : Prop :=
  rw_cells asegs m AACTIVE [C8 (Z_to_bv 64 AFALLBACK)] /\ rw_cells asegs m AACTIVE_GUARD guard1
  /\ rw_cells asegs m AFALLBACK fallback_cells /\ rw_cells asegs m AFALLBACK_GUARD guard1.
(* [comment removed for export] *)
Definition client_static (s : APS) (LB : list ablock) (m : amem) : Prop := aps_cl s = None /\ (client_static0 m \/ client_static1 m).
(* [comment removed for export] *)
Definition HUX (L : alayout) : Prop := True.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FuzzOneU.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  (* [comment removed for export] *)
  Variable rng_fs : alayout -> footprint -> Prop.

  (* [comment removed for export] *)
  Definition astk_shadow_pres (SP : Z) (m m' : amem) : Prop :=
    forall a, shad ATOP <= a < shad SP -> m' (wa a) = m (wa a).

  (* [comment removed for export] *)
  Definition payload_atA (LB : list ablock) (D : Z) (payload : list Z) : Prop :=
    (exists p, In (HB p D (zlength payload)) LB /\ 0 < zlength payload) \/ (payload = [] /\ D = AEMPTY).

  Definition fuzz_oneU_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : APS) (LB : list ablock) (lo : Z) (m : amem)
      (r : Z) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : amem) (LB' : list ablock),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom asegs)
      /\ r = 0
      /\ mem_inv asegs m' /\ frm0 fc'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ harness_pres CI LB (bv_unsigned sp) m m'
      /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' (aps_m s') LB' m'
      /\ harness_invA m' /\ client_static s' LB' m'
      /\ aps_rest s' = aps_rest s
      /\ LB' = LB /\ aps_cl s' = aps_cl s      (* [comment removed for export] *)
      /\ AFRESH (aps_m s') /\ dk (aps_m s') <= dk (aps_m s) + 8.   (* [comment removed for export] *)

  Definition fuzz_oneU_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
      AHEAP AI L RNG (aps_m s) LB m ->
      (forall b, In b LB -> exists p A n, b = HB p A n) ->          (* [comment removed for export] *)
      payload_atA LB D payload ->
      bytes_at asegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      harness_invA m -> client_static s LB m ->
      stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + 208 = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv asegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      HU L ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      aps_ok L s ->
      (* [comment removed for export] *)
      AFRESH (aps_m s) -> dk (aps_m s) <= DKF -> wr_at asegs m (bv_unsigned sp) (al_top L - bv_unsigned sp) ->
      implMA RNG (fuzz_oneA AAllocAsan payload) s
             (fuzz_oneU_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom asegs)).
End FuzzOneU.
End CANSEC1.
