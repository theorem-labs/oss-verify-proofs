(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AKit
  ECH_AStmt_C1 ECH_AC1_free.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition oszb' (o : oblk) : Z := match o with None => 0 | Some (_, n) => n end.

  Definition acfree_opt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (P : Z) (o : oblk) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ as_rauxv_ok H m' B
      /\ Permutation (blocks_of P o ++ LB') LB /\ (forall b, In b LB' -> In b LB)
      /\ xpres H LB' (bv_unsigned sp) [] m m'
      /\ as_RHEAP H s' LB' m'
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H (oszb' o).

  Lemma acfree_opt_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (P : Z) (o : oblk) (lo B : Z) (errv : word)
           (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 P ->
      (match o with None => P = 0
                  | Some (id, n) => In (id, P, n) LB /\ (exists bs, rw_cells asegs m P [CB (Z.to_nat n) bs]) /\ addressable m P n end) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - CFREE_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      pf_ok (as_TR H) PF_cfree (bv_unsigned ra) CH -> as_Cf H (oszb' o) <= as_AL H s ->
      IMPL_mem m -> GOT_mem m ->
      as_SR H (acfree_opt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB P o lo B errv m mo) (mkCfg msF mo).
  Proof.
    intros until CH. intros VIS A0 HO HP KREL AUX SPB ST CEIL LO ERR MI TP SPA AC CHN CHS PF CF IM GM.
    destruct o as [[id n]|].
    - (* [comment removed for export] *)
      destruct HO as (IN & [bs BC] & AD). cbn [oszb'] in CF.
      eapply (ah_mono H HH).
      { eapply (acfree_spec H HH) with (lo := lo) (B := B) (LB := LB) (s := s) (p := id) (n := n) (A := P) (CH := CH) (bs := bs); eassumption. }
      intros [ms2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                      E & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
      unfold acfree_opt_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', (as_lb_remove H id LB).
      split; [exact E|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|].
      split; [cbn [blocks_of app]; eapply (alb_remove_perm H HH); [exact HP| exact IN]|].
      split; [intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb|].
      split; [exact XP2|]. split; [exact HEAP2|]. split; [exact IM2|]. split; [exact GM2|]. cbn [oszb']. exact AL2.
    - (* [comment removed for export] *)
      subst P. cbn [oszb'] in CF.
      eapply (ah_mono H HH).
      { subst a0. eapply (acfree_null_spec H HH) with (lo := lo) (B := B) (LB := LB) (s := s) (CH := CH); eassumption. }
      intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                      E & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
      unfold acfree_opt_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', LB.
      split; [exact E|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact AC2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|].
      split; [cbn [blocks_of app]; apply Permutation_refl|]. split; [intros b Hb; exact Hb|].
      split; [exact XP2|]. split; [exact HEAP2|]. split; [exact IM2|]. split; [exact GM2|]. cbn [oszb']. exact AL2.
  Qed.
End W.
