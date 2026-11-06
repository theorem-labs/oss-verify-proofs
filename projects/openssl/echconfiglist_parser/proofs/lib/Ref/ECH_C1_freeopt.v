(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C1_free.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  Definition cfree_opt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list block) (P : Z) (o : oblk) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : PState) (LB' : list block),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
      /\ rw_cells rsegs m' (errno_addr tp) [C4 errv] /\ hs_rauxv_ok H m' B
      /\ Permutation (blocks_of P o ++ LB') LB /\ (forall b, In b LB' -> In b LB)
      /\ xpres LB' (bv_unsigned sp) [] m m'
      /\ hs_RHEAP H s' LB' m'
      /\ IMPL_mem m' /\ GOT_mem m'.

  Lemma cfree_opt_spec :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (P : Z) (o : oblk) (lo B : Z) (errv : word),
      a0 = Z_to_bv 64 P -> (match o with None => P = 0 | Some (id, n) => In (id, P, n) LB end) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - CFREE_STACK ->
      rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m -> tp = Z_to_bv 64 RATP ->
      IMPL_mem m -> GOT_mem m ->
      hs_SR H (cfree_opt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB P o lo B errv m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom rsegs)) mo).
  Proof.
    intros until errv. intros A0 HO HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM. subst a0.
    unfold CFREE_STACK, RFREE_STACK in LO. hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    destruct o as [[id n]|].
    - (* [comment removed for export] *)
      pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
      eapply (sr_mono H HH).
      { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := id) (n := n); try reflexivity; try eassumption;
          try (unfold CFREE_STACK, RFREE_STACK; lia). }
      intros [ms2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                      E & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2).
      unfold cfree_opt_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', (hs_lb_remove H id LB).
      split; [exact E|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact ST2|].
      split; [exact ERR2|]. split; [exact AUX2|].
      split; [cbn [blocks_of app]; eapply (lb_remove_perm H HH); [exact HP| exact HO]|].
      split; [intros b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb|].
      split; [exact XP2|]. split; [exact HEAP2|]. split; [exact IM2| exact GM2].
    - (* [comment removed for export] *)
      subst P. pose proof (cfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
      eapply (sr_mono H HH).
      { eapply CF with (lo := lo); [eapply (krel_halted H HH); exact KREL| eapply (krel_lazy H HH); exact KREL| exact ST| exact CEIL| unfold CFREE_STACK, RFREE_STACK in *; lia| exact MI| exact IM| exact GM]. }
      intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E & -> & MU2 & WM2 & MI2 & ST2 & IM2 & GM2).
      unfold cfree_opt_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s, LB.
      split; [exact E|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI2|]. split; [exact ST2|].
      split. { subst tp. rewrite errno_RATP in *. eapply rw_cells_transport; [exact ERR| exact MU2| exact WM2| unfold RERRNO; cbn; lia]. }
      split. { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU2| exact WM2|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
      split; [cbn [blocks_of app]; apply Permutation_refl|]. split; [auto|].
      split. { eapply xpres_of_munch; [exact MU2| exact WM2| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      split. { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      split; [exact IM2| exact GM2].
  Qed.
End W.
