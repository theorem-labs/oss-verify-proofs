(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface Stdio_kit AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import AU_kit AU_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Export AU_consts.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
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
  [(0x6afb00, 0x6afb18); (0x6afb40, 0x6afb42); (0x6afc00, 0x6afc02); (0x6afc20, 0x6afc30); (0x6afc40, 0x6afc42); (0x6afc60, 0x6afc68);
   (0x6afc80, 0x6afcac); (0x6afce0, 0x6afce2); (0x6b1eb8, 0x6b1ebc); (0x6d1f00, 0x6d1f04); (0x6d1f38, 0x6d1f48); (0x6d2038, 0x6d2048)].
Definition harness_pres (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  magree bsegs (fun a => aclient_addr CI LB SP a /\ outside client_wr a) m m'.
Lemma harness_pres_of_aheap_pres : forall CI LB SP m m', aheap_pres CI LB SP m m' -> harness_pres CI LB SP m m'.
Proof. intros CI LB SP m m' H a Ha [Hc _]. exact (H a Ha Hc). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition HU_TRACES : list (list Z) := [[AMALLOC_PC; AOPNEW_RET]; [AFREE_PC; 0xb3460]; [AFREE_PC; 0xb1ef4; 0xb1528; ATRUN_RET]; [AFREE_PC; 0xb1618; ATRUN_RET]]%Z.
Definition HU (L : alayout) : Prop := Forall (fun tr => In tr (al_U L)) HU_TRACES.
Lemma HU_opnew : forall L, HU L -> In [AMALLOC_PC; AOPNEW_RET] (al_U L).
Proof. intros L H. exact (Forall_inv H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition atexit_rt (m : amem) : Prop :=
  rw_cells bsegs m 0x175cc0 [C8 (Z_to_bv 64 0x1545d0)]
  /\ (exists (cdt thr sec : byte) (tm1 : word), rw_cells bsegs m 0x6d2138 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]).
(* [comment removed for export] *)
Definition client_tbl (s : APS) : list (Z * Z) :=
  match aps_cl s with None => TBL_REG | Some _ => TBL_RUN ADTOR_THUNK AVEC end.
Definition client_static (s : APS) (LB : list ablock) (m : amem) : Prop :=
  atexit_rt m /\ ATEXIT (client_tbl s) m /\
  match aps_cl s with
  | None =>
         rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] /\ rw_cells bsegs m AVEC_GUARD guard0
      /\ rw_cells bsegs m 0x6afc00 guard0 /\ rw_cells bsegs m 0x6afc20 [C8 w0; C8 w0] /\ rw_cells bsegs m 0x6afc40 guard0
      /\ rw_cells bsegs m 0x6afc60 [C8 w0]
      /\ rw_cells bsegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] /\ rw_cells bsegs m 0x6afce0 guard0
      /\ wr_at bsegs m (shad 0x6afb00) 8          (* [comment removed for export] *)
  | Some p => exists V, In (HB p V 8) LB
      /\ rw_cells bsegs m V [C8 (Z_to_bv 64 AFALLBACK)]
      /\ rw_cells bsegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] /\ rw_cells bsegs m AVEC_GUARD guard1
      /\ rw_cells bsegs m 0x6afc00 guard1 /\ rw_cells bsegs m 0x6afc20 [C8 (Z_to_bv 64 0x6afc60); C8 (Z_to_bv 64 1)] /\ rw_cells bsegs m 0x6afc40 guard1
      /\ rw_cells bsegs m 0x6afc60 [C8 (Z_to_bv 64 AFALLBACK)]
      /\ rw_cells bsegs m AFALLBACK [C8 (Z_to_bv 64 AFALLBACK_VT); C8 (Z_to_bv 64 0x29520); C8 (Z_to_bv 64 8); C8 (Z_to_bv 64 0x29720); C8 (Z_to_bv 64 0x1f); C4 w0]
      /\ rw_cells bsegs m 0x6afce0 guard1
  end.
(* [comment removed for export] *)
Definition client_static0 (m : amem) : Prop :=
  atexit_rt m /\ ATEXIT TBL_MAIN m /\
  (rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] /\ rw_cells bsegs m AVEC_GUARD guard0
      /\ rw_cells bsegs m 0x6afc00 guard0 /\ rw_cells bsegs m 0x6afc20 [C8 w0; C8 w0] /\ rw_cells bsegs m 0x6afc40 guard0
      /\ rw_cells bsegs m 0x6afc60 [C8 w0]
      /\ rw_cells bsegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] /\ rw_cells bsegs m 0x6afce0 guard0
      /\ wr_at bsegs m (shad 0x6afb00) 8).
(* [comment removed for export] *)
Lemma client_static_after_reg : forall s LB m, aps_cl s = None -> atexit_rt m ->
  (rw_cells bsegs m AVEC [C8 w0; C8 w0; C8 w0] /\ rw_cells bsegs m AVEC_GUARD guard0
      /\ rw_cells bsegs m 0x6afc00 guard0 /\ rw_cells bsegs m 0x6afc20 [C8 w0; C8 w0] /\ rw_cells bsegs m 0x6afc40 guard0
      /\ rw_cells bsegs m 0x6afc60 [C8 w0]
      /\ rw_cells bsegs m AFALLBACK [C8 w0; C8 w0; C8 w0; C8 w0; C8 w0; C4 w0] /\ rw_cells bsegs m 0x6afce0 guard0
      /\ wr_at bsegs m (shad 0x6afb00) 8) ->
  ATEXIT TBL_REG m -> client_static s LB m.
Proof. intros s LB m E RT CELLS AT. unfold client_static, client_tbl. rewrite E. split; [exact RT|]. split; [exact AT| exact CELLS]. Qed.

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
               F' (ret_pc ra) fc' None m' (seg_rom bsegs)
      /\ r = 0
      /\ mem_inv bsegs m' /\ frm0 fc'
      /\ stk bsegs m' lo (bv_unsigned sp)
      /\ harness_pres CI LB (bv_unsigned sp) m m'
      /\ astk_shadow_pres (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' (aps_m s') LB' m'
      /\ harness_invA m' /\ client_static s' LB' m'
      /\ aps_rest s' = aps_rest s
      /\ match aps_cl s with
         | Some _ => LB' = LB /\ aps_cl s' = aps_cl s        (* [comment removed for export] *)
         | None   => exists p V, LB' = HB p V 8 :: LB /\ aps_cl s' = Some p
         end.

  Definition fuzz_oneU_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (D : Z) (payload : list Z) (lo : Z) (rstk : region),
      AHEAP AI L RNG (aps_m s) LB m ->
      (forall b, In b LB -> exists p A n, b = HB p A n) ->          (* [comment removed for export] *)
      payload_atA LB D payload ->
      bytes_at bsegs m D (map (Z_to_bv 8) payload) -> Forall (fun c => 0 <= c < 256) payload ->
      D mod 16 = 0 -> zlength payload < 2^26 ->
      harness_invA m -> client_static s LB m ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AHARNESS_STACK ->
      bv_unsigned sp + 208 = al_sp0 L -> bv_unsigned sp mod 16 = 0 ->      (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      s0 = Z_to_bv 64 (zlength payload) ->
      mem_inv bsegs m -> frm0 fc ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 (zlength payload) -> ra = Z_to_bv 64 ATRUN_RET ->
      HU L ->
      rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG -> rrng RNG rstk ->
      aps_ok L s ->
      implMA RNG (fuzz_oneA AAllocAsan payload) s
             (fuzz_oneU_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 AFUZZ_ENTRY) fc None m (seg_rom bsegs)).
  (* [comment removed for export] *)
  Definition fuzz_oneM_stmt : Prop := fuzz_oneU_stmt.
End FuzzOneU.
End CANSEC1.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Definition AFOE_S0 : Z := 0x6d1efc.       (* [comment removed for export] *)
Definition AVDTOR_STACK : Z := 16384.    (* [comment removed for export] *)
Definition HUX (L : alayout) : Prop := In [AFREE_PC; AVECDEL_RET] (al_U L).
(* [comment removed for export] *)
Definition vdtor_pres (CI : list (Z * Z)) (LB : list ablock) (SP : Z) (m m' : amem) : Prop :=
  magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (AVEC <= a < AVEC + 24)) m m'.

Section VDtor.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  Definition avdtor_post (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (V lo : Z) (m : amem)
      (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ vdtor_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
      /\ AHEAP AI L RNG' (aps_m s') (lb_remove p LB) m'
      /\ aps_rest s' = aps_rest s
      /\ harness_invA m'
      /\ rw_cells bsegs m' AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8))].

  Definition avdtor_stmt : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (V lo : Z) (rstk : region),
      AHEAP AI L RNG (aps_m s) LB m -> In (HB p V 8) LB ->
      (forall b, In b LB -> exists q A n, b = HB q A n) ->          (* [comment removed for export] *)
      harness_invA m ->
      rw_cells bsegs m AVEC [C8 (Z_to_bv 64 V); C8 (Z_to_bv 64 (V + 8)); C8 (Z_to_bv 64 (V + 8))] ->
      rw_cells bsegs m V [C8 (Z_to_bv 64 AFALLBACK)] ->
      mem_inv bsegs m -> frm0 fc ->
      stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AVDTOR_STACK ->
      bv_unsigned sp + 16 <= 2^47 -> bv_unsigned sp mod 16 = 0 ->       (* [comment removed for export] *)
      rclean m rstk -> r_lo rstk <= lo -> bv_unsigned sp <= r_hi rstk -> ATOP <= r_rlo rstk ->
      tp = Z_to_bv 64 ATP ->
      a0 = Z_to_bv 64 AVEC -> s0 = Z_to_bv 64 AFOE_S0 ->
      4096 <= bv_unsigned ra -> bv_unsigned ra mod 2 = 0 ->
      HUX L -> In [AFREE_PC] (al_U L) ->                                 (* [comment removed for export] *)
      rng RNG lo (al_top L - lo) -> rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rrng RNG rstk ->
      aps_ok L s ->
      implMA RNG (HarnessM.opdelete afree_M p) s
             (fun _ => avdtor_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB p V lo m)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 FR (Z_to_bv 64 ADTOR_THUNK) fc None m (seg_rom bsegs)).
End VDtor.
End CANSEC2.
