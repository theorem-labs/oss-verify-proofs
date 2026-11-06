(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_malloc ECH_C1_free ECH_C5_stmt ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition SF_RA : Z := 0xe87e8.
  Definition SK_FILE : Z := 0x2a3a6.
  Definition sf_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  Lemma sf_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo -> 0 <= sk_data K < 2^64 ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> mem_inv usegs m ->
      evt usegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 SF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 (sk_data K)) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 496) a3 a4 a5 a6 a7
                       (Z_to_bv 64 SK_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom usegs)
          /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
          /\ stk usegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells usegs m1 (bv_unsigned sp + -32) (sf_frame s2 s1 s0 ra)
          /\ rw_cells usegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_free) fc None m (seg_rom usegs)).
  Proof.
    intros until pad. intros AL HDR POS BL DR ST CEIL LO MI. unfold P_OPENSSL_sk_free, P_CRYPTO_free, SF_RA, SK_FILE.
    unfold sk_hdr_cells, wz in HDR. pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    do 6 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. ubal_by AL. step. if_lit.
    st1. do 5 step. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma sf_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells usegs m (bv_unsigned sp + -32) (sf_frame s2 s1 s0 ra) -> mem_inv usegs m ->
      evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 497) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom usegs))
        (MS (mkR (Z_to_bv 64 SF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 SK_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 SF_RA)) fc None m (seg_rom usegs)).
  Proof.
    intros until a. intros FR MI. unfold SF_RA, SK_FILE, P_CRYPTO_free.
    replace (ret_pc (Z_to_bv 64 0xe87e8)) with (Z_to_bv 64 0xe87e8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. unfold sf_frame in FR.
    do 9 step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.

  (* [comment removed for export] *)
  Lemma skfree_spec_hdr :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block) (a lo B : Z) (K : skrep) (errv : word) (pad : list byte),
      a0 = Z_to_bv 64 a -> rw_cells usegs m a (sk_hdr_cells K pad) -> 0 < a -> In (sk_id K, a, SK_SIZE) LB ->
      ((sk_cap K = 0 /\ sk_data K = 0) \/ (4 <= sk_cap K /\ 0 < sk_data K /\ (a + SK_SIZE <= sk_data K \/ sk_data K + 8 * sk_cap K <= a) /\ In (sk_did K, sk_data K, 8 * sk_cap K) LB)) ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - SKFREE_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (skfree_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K lo B errv m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_OPENSSL_sk_free) fc None m (seg_rom usegs)) mo).
  Proof.
    intros until pad.
    intros A0 HDR POS HIN DAT HP KREL AUX SPB ST CEIL LO ERR MI TP IM GM. subst a0.
    unfold SKFREE_STACK, FR_sk_free, CFREE_STACK, RFREE_STACK in LO.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof (HB _ HIN) as ABL. cbn [blk_addr blk_size fst snd] in ABL. unfold SK_SIZE in ABL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HP HIN) as (_ & AL16 & _). cbn [blk_addr blk_size fst snd] in AL16.
    assert (AL8 : a mod 8 = 0) by (clear - AL16; lia).   (* [comment removed for export] *)
    assert (SUBL : forall p L b, In b (hs_lb_remove H p L) -> In b L) by (intros p L b Hb; eapply (proj2 (proj2 (HH_lb_remove H HH))); exact Hb).
    assert (DR : 0 <= sk_data K < 2^64).
    { destruct DAT as [[X1 D0]|(X2 & DP & X3 & DIN)]; [lia|]. pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL. lia. }
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply sf_seg1 with (lo := lo); [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| exact DR| exact ST| exact CEIL| lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
    assert (HP1 : hs_RHEAP H s LB m1).
    { eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (AUX1 : hs_rauxv_ok H m1 B).
    { eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    subst tp. rewrite errno_RATP in ERR.
    apply (rw_cells_transport usegs _ m m1 _ _ ERR) in MU1 as ERR1; [| exact WM1| unfold RERRNO; cbn; lia].
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (XP1 : xpres LB (bv_unsigned sp) [] m m1).
    { eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    assert (MID : hs_SR H (fun c => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m2 s2' LB2,
                 cfg_ms c = MS (mkR (Z_to_bv 64 SF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) t0' t1' t2' sp (Z_to_bv 64 a)
                                    a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SK_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc (Z_to_bv 64 SF_RA)) fc None m2 (seg_rom usegs)
                 /\ hs_KREL H s2' (cfg_model c) /\ hs_MPRES H mo (cfg_model c) /\ mem_inv usegs m2 /\ stk usegs m2 lo (bv_unsigned sp + -32)
                 /\ rw_cells usegs m2 RERRNO [C4 errv] /\ hs_rauxv_ok H m2 B
                 /\ hs_RHEAP H s2' LB2 m2 /\ In (sk_id K, a, SK_SIZE) LB2
                 /\ Permutation ((if sk_cap K =? 0 then [] else [(sk_did K, sk_data K, 8 * sk_cap K)]) ++ LB2) LB
                 /\ (forall b, In b LB2 -> In b LB)
                 /\ xpres LB2 (bv_unsigned sp + -32) [] m1 m2 /\ IMPL_mem m2 /\ GOT_mem m2
                 /\ rw_cells usegs m2 (bv_unsigned sp + -32) (sf_frame s2 s1 s0 ra))
             (mkCfg (MS (mkR (Z_to_bv 64 SF_RA) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 RATP) t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 (sk_data K)) (Z_to_bv 64 SK_FILE) (Z_to_bv 64 496) a3 a4 a5 a6 a7
                       (Z_to_bv 64 SK_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom usegs)) mo)).
    { destruct DAT as [[C0 D0]|(D4 & DP & DDJ & DIN)].
      - (* [comment removed for export] *)
        rewrite D0. pose proof (cfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
        eapply (sr_mono H HH).
        { eapply CF with (lo := lo); rewrite ?unsigned_lit by lia;
            [eapply (krel_halted H HH); exact KREL| eapply (krel_lazy H HH); exact KREL| exact ST1| exact CEIL| lia| exact MI1| exact IM1| exact GM1]. }
        intros [ms2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & -> & MU2 & WM2 & MI2 & ST2 & IM2 & GM2).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in MU2, ST2 by lia.
        exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s, LB.
        split; [reflexivity|]. split; [exact KREL|]. split; [apply (mpres_refl H HH)|]. split; [exact MI2|]. split; [exact ST2|].
        split; [eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2| unfold RERRNO; cbn; lia]|].
        split. { eapply (HH_rauxv_frame H HH); [exact AUX1| exact MU2| exact WM2|]. unfold RAUXV_CELL. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
        split. { eapply (HH_RHEAP_frame H HH); [exact HP1| exact MU2| exact WM2|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [exact HIN|]. rewrite C0. cbn [Z.eqb app]. split; [apply Permutation_refl|]. split; [auto|].
        split. { eapply xpres_of_munch; [exact MU2| exact WM2| | exact HB]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split; [exact IM2|]. split; [exact GM2|].
        eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| cbn; lia].
      - (* [comment removed for export] *)
        pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL.
        pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
        eapply (sr_mono H HH).
        { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := sk_did K) (n := 8 * sk_cap K); rewrite ?unsigned_lit by lia; try reflexivity.
          all: try first [exact HP1| exact KREL| exact DIN| exact AUX1| exact ST1| exact CEIL| exact MI1| exact IM1| exact GM1].
          all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR1]. }
        intros [ms2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                        -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite errno_RATP in ERR2.
        assert (HIN2 : In (sk_id K, a, SK_SIZE) (hs_lb_remove H (sk_did K) LB)).
        { apply (proj2 (proj2 (proj2 (lb_remove_exact H HH _ _ _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HP) DIN)) (sk_id K, a, SK_SIZE))).
          split; [exact HIN|]. cbn. intros E.
          pose proof (nodup_id_inj LB _ _ (HH_RHEAP_blocks_nodup H HH _ _ _ HP) HIN DIN E) as EE.
          injection EE as E1 E2. unfold SK_SIZE in *. lia. }
        exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', (hs_lb_remove H (sk_did K) LB).
        split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI2|]. split; [exact ST2|].
        split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HEAP2|]. split; [exact HIN2|].
        replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app].
        split; [eapply (lb_remove_perm H HH); [exact HP| exact DIN]|]. split; [intros b Hb; eapply SUBL; exact Hb|].
        split; [exact XP2|]. split; [exact IM2|]. split; [exact GM2|].
        eapply xpres_rw_cells'; [exact XP2| exact FR1| left; cbn; lia| constructor]. }
    eapply (sr_seq H HH); [exact MID|].
    intros [ms2 mo2] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & sx2 & LB2 &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & HEAP2 & HIN2 & PERM2 & SUB2 & XP2 & IM2 & GM2 & FR2).
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP2).
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL2| eapply sf_seg2; [exact FR2| exact MI2]|].
    intros ms3 ->.
    (* [comment removed for export] *)
    unfold sf_frame in FR2.
    pose proof (stk_release usegs m2 lo _ _ ST2 FR2 ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
    replace (bv_unsigned sp + -32 + Z.of_nat 32) with (bv_unsigned sp) in ST3 by lia.
    pose proof (cfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (sr_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB2) (s := sx2) (p := sk_id K) (n := SK_SIZE); try reflexivity.
      all: try first [exact HEAP2| exact KREL2| exact HIN2| exact AUX2| exact SPB| exact ST3| exact CEIL| exact MI2| exact IM2| exact GM2].
      all: first [unfold CFREE_STACK, RFREE_STACK; lia | rewrite errno_RATP; exact ERR2]. }
    intros [ms4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & s4' &
                    -> & KREL4 & MP4 & MI4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4).
    rewrite errno_RATP in ERR4.
    unfold skfree_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m4, s4', (hs_lb_remove H (sk_id K) LB2).
    split; [reflexivity|]. split; [exact KREL4|]. split; [eapply (mpres_trans H HH); [exact MP2| exact MP4]|]. split; [exact MI4|]. split; [exact ST4|].
    split; [rewrite errno_RATP; exact ERR4|]. split; [exact AUX4|].
    split.
    { unfold blocks_SK. cbn [app]. eapply Permutation_trans; [| exact PERM2].
      destruct (sk_cap K =? 0); cbn [app].
      - eapply (lb_remove_perm H HH); [exact HEAP2| exact HIN2].
      - eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply (lb_remove_perm H HH); [exact HEAP2| exact HIN2]. }
    split; [exact HEAP4|].
    split.
    { eapply xpres_trans; [| eapply xpres_trans; [| exact XP4]].
      - eapply xpres_weaken; [exact XP1| lia| intros b Hb; apply SUB2; eapply SUBL; exact Hb| auto].
      - eapply xpres_weaken; [exact XP2| lia| intros b Hb; eapply SUBL; exact Hb| auto]. }
    split; [exact IM4| exact GM4].
  Qed.

  Lemma skfree_spec : skfree_stmt H.
  Proof.
    unfold skfree_stmt. intros until errv. intros A0 SO. intros.
    destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    eapply skfree_spec_hdr with (pad := pad); try eassumption.
    destruct DAT as [D0|(D4 & DP & DDJ & DIN & _)]; [left; exact D0| right; repeat split; assumption].
  Qed.
End W.
