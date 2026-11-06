(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARtStmts ARtSscs ARtSf1m.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic AMTac AMallocI AMallocA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalc5w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMalmys AMaly5g ANodeA7 ASecComb ASecr83 ASecO1 ATransp ASecB1.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalc5w.AMalloc1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecr83 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecO1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

(* [comment removed for export] *)
Definition sec_exc (a : Z) : Prop := a = 0x137620 \/ (0x5e8334 <= a < 0x5e8338).
Definition const_noexc (c : Z * list byte) : bool :=
  ((fst c + Z.of_nat (length (snd c)) <=? 0x137620) || (0x137621 <=? fst c)) &&
  ((fst c + Z.of_nat (length (snd c)) <=? 0x5e8334) || (0x5e8338 <=? fst c)).
Lemma pa_consts_noexc : forallb const_noexc pa_consts = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac alc_h H := cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
       al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks al_internal_alloc_inited al_internal_allocator_inst
       al_theDepot al_depot_n_uniq_ids al_depot_nodes_map1 al_stackStore al_tp AL_pasan cl_tp cl_shared cl_consts cl_segs LPA] in H.

(* [comment removed for export] *)

Section Refusal.
Context {Clg : Ceiling}.
  Variables (ra sp gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AState) (n : Z) (T : TSet).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis RA4 : bv_unsigned ra mod 4 = 0.
  Hypothesis SITE : In (bv_unsigned ra) (cl_sites LPA).
  Hypothesis S0C : bv_unsigned s0 < alloc_ceiling.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
  Hypothesis SM : mapped (aview_of (pa_hull A) m) (bv_unsigned sp - ASTK) ASTK.
  Hypothesis LNULL : lma_null_stmt.
  Hypothesis KK : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AState) (m' : mem) (md' : Model),
          let v' := aview_of (pa_hull A') m' in
          @pa_ainv _ DepotRepL A' m' md' -> mem_inv (cl_segs LPA) v' -> amd_frame md md' ->
          hull_le (pa_hull A) (pa_hull A') ->
          (forall ff, as_fframe A' ff = as_fframe A ff) ->
          as_tinycred A' = as_tinycred A - (if Z.ltb n 16 then 1 else 0) ->
          (   (r = 0 /\ (forall q, as_live A' q = as_live A q) /\ as_livebytes A' = as_livebytes A /\
               as_nlive A' = as_nlive A /\ as_seccred A' = as_seccred A /\ as_primcred A' = as_primcred A (* [comment removed for export] *))
           \/ (r <> 0 /\ as_live A r = None /\ as_live A' r = Some n /\
               (forall q, q <> r -> as_live A' q = as_live A q) /\
               as_livebytes A' = as_livebytes A + n /\ as_nlive A' = as_nlive A + 1 /\
               as_seccred A' = as_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               as_primcred A' = as_primcred A - prim_cost n (* [comment removed for export] *))) ->
          frame_ok LPA (pa_owned A) (pa_owned A') (bv_unsigned sp) ASTK nowhere (newblk r n)
                   (aview_of (pa_hull A) m) v' ->
          srealizes (cl_segs LPA) (mkCfg (MS (mkR ra sp gp (cl_tp LPA) t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' (seg_rom (cl_segs LPA))) md') T.

  #[warnings="-notation-for-abbreviation"] Local Notation fp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation H0 := (hidc (pa_hull A)).

  (* [comment removed for export] *)
  Variables (m1 : mem) (md1 : Model) (t0' t1' t2' a6' t3' t4' t5' t6' : word) (pad jb1 jrest junk0 scrL scrM : list byte)
            (oomb : byte) (e0 : word).
  Hypothesis MU1 : munch [(bv_unsigned sp - ASTK, fp); (thr + off_th_unwinding, thr + off_th_unwinding + 1)] v m1.
  Hypothesis WM1 : wmono rsegs v m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 (bv_unsigned sp - ASTK) (fp + -2144 + -128 + -48 + -96 + -48).
  Hypothesis HI1 : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
  Hypothesis SB1 : same_but_materialized md md1.
  Hypothesis CL1 : forall a, H0 a = true -> m1 a = None.
  Hypothesis O0 : rw_cells rsegs m1 (fp + -2128) [C8 (wz (fp + -2128 + 16))].
  Hypothesis D8 : rw_cells rsegs m1 (fp + -2128 + 8) [C4 (wz (dep_w8 (p_stk_top (a_pl A)) (p_stk_bot (a_pl A)) fp))].
  Hypothesis D16 : rw_cells rsegs m1 (fp + -2128 + 16) [C8 (wz 0x58c14); CB 8 (dep_b16 (p_stk_top (a_pl A)) (p_stk_bot (a_pl A)) fp ra jb1)].
  Hypothesis O12 : rw_cells rsegs m1 (fp + -2128 + 12) [C4 (wz 0)].
  Hypothesis O32 : rw_cells rsegs m1 (fp + -2128 + 32) [CB 2024 jrest].
  Hypothesis PC1 : rw_cells rsegs m1 (fp + -2128 + 2056) [C8 (wz fp)].
  Hypothesis FR : rw_cells rsegs m1 (fp + -64) [CB 8 pad; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis AMF : rw_cells rsegs m1 (fp + -2144) [C8 sp; C8 (wz 0x58c80)].
  Hypothesis TUNW : rw_cells rsegs m1 (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis TTB : rw_cells rsegs m1 (thr + 8) [C8 (wz (p_stk_top (a_pl A))); C8 (wz (p_stk_bot (a_pl A)))].
  Hypothesis FRA : rw_cells rsegs m1 (fp + -2144 + -128)
         (alloc_s1a_frame (wz (fp + -2144)) 1 s11 s10 s9 s8 s7 s6 (wz (fp + -81)) (wz (fp + -2128)) (wz 1) (wz 0x58c14) (wz n) sp (wz 0x3716c) junk0).
  Hypothesis FRC : rw_cells rsegs m1 (fp + -2144 + -128 + -48) (comb_frame (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 0) (wz 0x3743c)).
  Hypothesis FRL : rw_cells rsegs m1 (fp + -2144 + -128 + -48 + -96)
         (lma_frame scrL (wz 7) (wz (-8)) (wz (fp + -2128)) (wz 0xb1d58) (wz n) (wz (rz_size n)) (wz (needed_size2 n)) (wz 8) (wz n) (wz 8) (wz comb_sec_ret)).
  Hypothesis FRM : rw_cells rsegs m1 (fp + -2144 + -128 + -48 + -96 + -48)
         [CB 12 scrM; C4 (wz 34); C8 (wz (map_size n)); C8 (wz ASecComb.LMA); C8 (wz ASecComb.LSTAT); C8 (wz lma_mapret)].
  Hypothesis OOM1 : rw_cells rsegs m1 0x137620 [C1 oomb].
  Hypothesis MRN1 : ro_cells rsegs m1 0x137621 [C1 (Z_to_bv 8 1)].
  Hypothesis ERR1 : rw_cells rsegs m1 (bv_unsigned (cl_tp LPA) + -164) [C4 e0].
  Hypothesis Lgotcf1 : ro_cells rsegs m1 0xa9180 [C8 (wz ANodeA7.CF)].
  Hypothesis Lmlim1 : ro_cells rsegs m1 (ANodeA7.CF + 144) [C8 (wz 0)].

  (* [comment removed for export] *)
End Refusal.
