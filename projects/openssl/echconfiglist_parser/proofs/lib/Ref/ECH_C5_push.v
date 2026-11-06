(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState
     ECH_C1_stmt ECH_C1_malloc ECH_C5_stmt ECH_C5_reserve.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition PU_RA : Z := 0xe34a8.    (* [comment removed for export] *)
  Definition ins_frame (s4 s3 s2 s1 s0 ra : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac prep HDR := unfold sk_hdr_cells, wz in HDR; pose proof (rw_cells_bound _ _ _ _ HDR) as HB; cbn [cells_size csize Nat.add] in HB.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pu_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a p lo : Z) (K : skrep) (pad : list byte),
      rw_cells rsegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo -> 0 <= sk_num K <= 2^20 -> 0 < p < 2^64 ->
      stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 PU_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                       (Z_to_bv 64 (sk_num K)) (Z_to_bv 64 p) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_sk_reserve) fc None m1 (seg_rom rsegs)
          /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ stk rsegs m1 lo (bv_unsigned sp + -48)
          /\ rw_cells rsegs m1 (bv_unsigned sp + -48) (ins_frame s4 s3 s2 s1 s0 ra)
          /\ rw_cells rsegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom rsegs)).
  Proof.
    intros until pad. intros HDR POS BL NN PR ST CEIL LO MI. unfold P_OPENSSL_sk_push, P_sk_reserve, PU_RA. prep HDR. unfold SK_SIZE in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 4 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    st1. rewrite sx32_wz by lia. unfold wz. do 3 step.
    release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 8 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    step. step. st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep.
    step. try (if_cases K0; zify_cond K0; [| kill K0]; clear K0).
    do 5 step.
    finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pu_seg2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a p D cap srt cmp cth fth cpth : Z) (el : list Z) (id did : bptr) (pad junk : list byte),
      let K := mkSK el D cap srt cmp cth fth cpth id did in
      let Q := D + 8 * zlength el in
      rw_cells rsegs m a (sk_hdr_cells K pad) -> 0 < a -> a + 56 <= bv_unsigned sp + -48 ->
      0 <= zlength el -> zlength el + 1 <= cap -> cap <= 2^20 -> 0 <= srt <= 1 -> (cmp = 0 \/ zlength el = 0 \/ srt = 0) ->
      0 < D -> D + 8 * cap <= bv_unsigned sp + -48 -> (a + 56 <= D \/ D + 8 * cap <= a) -> 0 < p < 2^64 ->
      rw_cells rsegs m Q [CB (Z.to_nat (8 * (cap - zlength el))) junk] ->
      rw_cells rsegs m (bv_unsigned sp + -48) (ins_frame s4 s3 s2 s1 s0 ra) -> mem_inv rsegs m ->
      evt rsegs (fun ms' => exists a1' a2' a3' m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength el + 1)) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(a, a + 56); (Q, Q + 8)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 a (sk_hdr_cells (sk_after_push K p D cap did) pad)
          /\ rw_cells rsegs m1 Q [C8 (wz p)]
          /\ rw_cells rsegs m1 (Q + 8) [CB (Z.to_nat (8 * (cap - zlength el)) - 8)%nat (skipn 8 junk)])
        (MS (mkR (Z_to_bv 64 PU_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (zlength el)) (Z_to_bv 64 p) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 PU_RA)) fc None m (seg_rom rsegs)).
  Proof.
    intros until junk. intros K Q HDR POS HS NN ROOM CAP SRT NOC DP DS DDJ PR JK FR MI. subst K. unfold PU_RA.
    replace (ret_pc (Z_to_bv 64 0xe34a8)) with (Z_to_bv 64 0xe34a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (word_range sp) as SPR. prep HDR. unfold sk_num in HDR; cbn [sk_elems sk_data sk_sorted sk_cap sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk] in HDR.
    unfold ins_frame in FR.
    destruct (rw_cells_CB_split rsegs _ Q _ 8 junk JK ltac:(lia)) as [JQ JR]. clear JK.
    pose proof (munch_refl [(a, a + 56); (Q, Q + 8)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    st1. rewrite sx32_wz by lia. unfold wz. step.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    match goal with |- evt _ _ ?ms => idtac "STATE_P2" ms end.
    step. try (if_cases K0; zify_cond K0; [| kill K0]; clear K0).
    match goal with |- evt _ _ ?ms => idtac "STATE_P3" ms end.
    zstep. zstep. rewrite (Z.shiftl_mul_pow2 _ 3) by lia. change (2^3) with 8.
    replace (D + zlength el * 8) with Q by lia.
    st1. step. st1. rewrite sx32_wz by lia. unfold wz. zstep. st1.
    (* [comment removed for export] *)
    assert (FIN : forall srt' mX (a1x a3x : word),
      munch [(a, a + 56); (Q, Q + 8)] m mX -> wmono rsegs m mX -> mem_inv rsegs mX ->
      rw_cells rsegs mX a [C4 (Z_to_bv 64 (zlength el + 1)); CB 4 pad; C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 srt'); C4 (Z_to_bv 64 cap);
                           C8 (Z_to_bv 64 cmp); C8 (Z_to_bv 64 cth); C8 (Z_to_bv 64 fth); C8 (Z_to_bv 64 cpth)] ->
      srt' = (if (srt =? 1) && (1 <=? zlength el) then 0 else srt) -> 0 <= srt' <= 1 ->
      rw_cells rsegs mX Q [C8 (Z_to_bv 64 p)] ->
      rw_cells rsegs mX (Q + Z.of_nat 8) [CB (Z.to_nat (8 * (cap - zlength el)) - 8) (skipn 8 junk)] ->
      rw_cells rsegs mX (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt rsegs (fun ms' => exists a1' a2' a3' m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength el + 1)) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom rsegs)
          /\ munch [(a, a + 56); (Q, Q + 8)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1
          /\ rw_cells rsegs m1 a (sk_hdr_cells (sk_after_push (mkSK el D cap srt cmp cth fth cpth id did) p D cap did) pad)
          /\ rw_cells rsegs m1 Q [C8 (wz p)]
          /\ rw_cells rsegs m1 (Q + 8) [CB (Z.to_nat (8 * (cap - zlength el)) - 8)%nat (skipn 8 junk)])
        (MS (mkR (Z_to_bv 64 0xe34a8) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                 (Z_to_bv 64 (zlength el + 1)) a1x (Z_to_bv 64 (zlength el + 1)) a3x a4 a5 a6 a7
                 (Z_to_bv 64 (zlength el)) (Z_to_bv 64 p) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe359c) fc None mX (seg_rom rsegs))).
    { intros srt' mX a1x a3x MUX WMX MIX HDRX E SB QX JX FRX.
      clear MU WM. rename MUX into MU. rename WMX into WM.
      do 8 step. finish.
      unfold sk_hdr_cells, sk_after_push, sk_num, wz. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk].
      unfold zlength in *. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. rewrite <- E. exact HDRX. }
    cbv delta [mkR] in FIN.
    destruct (Z.eq_dec srt 0) as [S0|S1].
    - subst srt. step. try if_true. st1. rewrite ?sx32_wz by lia. unfold wz.
      eapply (FIN 0); try eassumption; try lia. cbn. reflexivity.
    - assert (S1' : srt = 1) by lia. subst srt. step. try if_false.
      (* [comment removed for export] *)
      step.
      all: lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases Kb; try zify_cond Kb
      | _ => idtac
      end.
      all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0xe3598) _ _ _ _) =>
          (* [comment removed for export] *)
          assert (N0 : zlength el = 0)
            by first [ lia
                     | revert Kb; rewrite ?signed_lit by lia; intros Kb; lia
                     | match goal with K : (_ && _) = false |- _ => apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia end ];
          st1; rewrite ?sx32_wz by lia; unfold wz;
          eapply (FIN 1); try eassumption; try lia; rewrite N0; cbn; reflexivity
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0xe359c) _ _ _ _) =>
          assert (N0 : zlength el = 0)
            by first [ lia
                     | revert Kb; rewrite ?signed_lit by lia; intros Kb; lia
                     | match goal with K : (_ && _) = false |- _ => apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia end ];
          rewrite ?sx32_wz by lia; unfold wz;
          eapply (FIN 1); try eassumption; try lia; rewrite N0; cbn; reflexivity
      | |- _ =>
          (* [comment removed for export] *)
          assert (N1 : 1 <= zlength el)
            by first [ lia
                     | revert Kb; rewrite ?signed_lit by lia; intros Kb; lia
                     | match goal with K : (_ && _) = true |- _ => apply Bool.andb_true_iff in K; destruct K as [K _]; apply Z.ltb_lt in K; lia end ];
          assert (C0 : cmp = 0) by lia; subst cmp;
          st1; step; try if_true; st1; st1; rewrite ?sx32_wz by lia; unfold wz;
          eapply (FIN 0); try eassumption; try lia; cbn [Z.eqb Pos.eqb andb]; destruct (Z.leb_spec 1 (zlength el)); [reflexivity| lia]
      end.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Hypothesis HH : heap_sr_hyps H.
  Hypothesis HRE : realloc_sr_stmt H.

  Lemma u64arr_snoc : forall m A ws w,
    u64arr rsegs m A ws -> rw_cells rsegs m (A + 8 * Z.of_nat (length ws)) [C8 w] -> u64arr rsegs m A (ws ++ [w]).
  Proof.
    intros m A ws w [B W] [[_ B1] W1]. cbn [cells_bytes cbytes app] in B1. rewrite app_nil_r in B1. cbn [cells_size csize Nat.add] in W1.
    split.
    - rewrite u64s_app. cbn [u64s map concat]. rewrite app_nil_r. apply bytes_at_app. split; [exact B|]. rewrite u64s_length.
      replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact B1.
    - rewrite length_app. cbn [length]. replace (8 * Z.of_nat (length ws + 1)) with (8 * Z.of_nat (length ws) + 8) by lia.
      apply wr_at_app; [lia| lia|]. split; [exact W|]. replace 8 with (Z.of_nat (8 + 0)) at 2 by reflexivity. exact W1.
  Qed.

  Lemma skpush_spec : skpush_stmt H.
  Proof.
    unfold skpush_stmt. intros until errv.
    intros A0 A1 PR SO NOC CAPX HP KREL BUD BUDC BUDB AUX SPB ST CEIL LO ERR MI TP (MF & IM & GM). subst a0 a1.
    unfold SKPUSH_STACK, FR_sk_insert, SKRESERVE_STACK, FR_sk_reserve, CARRAY_STACK, CREALLOC_ARRAY_STACK, CZALLOC_STACK, CREALLOC_STACK, CMALLOC_STACK,
      FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_realloc, FR_CRYPTO_malloc, RREALLOC_STACK, RMALLOC_STACK in LO. unfold RMALLOC_STACK in LO.
    unfold SK_CAP_MAX in *.
    hcb. pose proof (word_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (HB := HH_blocks_below H HH _ _ _ HP).
    pose proof SO as SO'. destruct SO' as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (HB _ HIN) as ABL. cbn [blk_addr blk_size fst snd] in ABL. unfold SK_SIZE in ABL.
    unfold sk_num in *.
    (* [comment removed for export] *)
    eapply (sr_evt_krel H HH); [exact KREL| eapply pu_seg1 with (lo := lo);
      [exact HDR| exact POS| unfold SK_SIZE; lia| unfold sk_num; clear - NC CAP; lia| exact PR| exact ST| exact CEIL| clear - LO; lia| exact MI]|].
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
    assert (SO1 : SKobj LB m1 a K).
    { eapply (SKobj_rehdr_gen LB m m1); [exact SO| exact PL| exact HDR1| exact MU1| exact WM1|].
      destruct DAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [left; exact C0| right].
      pose proof (HB _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL. cbn. clear - DBL LO CEIL. lia. }
    (* [comment removed for export] *)
    pose proof (skreserve_spec H HH HRE) as RS. unfold skreserve_stmt in RS.
    eapply (sr_seq H HH).
    { eapply RS with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (K := K); rewrite ?unsigned_lit by lia; try reflexivity.
      all: try first [exact SO1| exact KREL| exact ST1| exact CEIL| exact MI1| exact TP| exact BUD| exact BUDC| exact BUDB].
      all: lazymatch goal with
           | |- sk_cap _ <= _ => unfold SK_CAP_MAX; lia
           | |- hs_RHEAP _ _ _ _ => eapply (HH_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; clear - LO CEIL SPR; lia| apply Forall_nil]
           | |- hs_rauxv_ok _ _ _ => eapply (HH_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1|]; unfold RAUXV_CELL; apply Forall_cons; [cbn; clear - LO CEIL SPR SPB HCEILB; lia| apply Forall_nil]
           | |- rw_cells _ _ _ _ => subst tp; rewrite errno_RATP in *; eapply (rw_cells_transport rsegs _ _ _ _ _ ERR MU1 WM1); unfold RERRNO; cbn; clear - LO CEIL SPR HCEILB; lia
           | |- C1env _ _ => split; [| split]; [eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; clear - LO CEIL SPR HCEILB; lia| exact MF]
                                              | eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; clear - LO CEIL SPR HCEILB; lia| exact IM]
                                              | eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; clear - LO CEIL SPR HCEILB; lia| exact GM]]
           | |- _ => unfold SKRESERVE_STACK, FR_sk_reserve, CARRAY_STACK, CREALLOC_ARRAY_STACK, CZALLOC_STACK, CREALLOC_STACK, CMALLOC_STACK,
                       FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_realloc, FR_CRYPTO_malloc, RREALLOC_STACK, RMALLOC_STACK in *;
                     unfold RMALLOC_STACK in *; clear - LO CEIL SPR SPB; lia
           end. }
    intros [ms2 mo2] PO. unfold skreserve_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s' & LB' & K1 & data' & cap' & did' &
                    -> & KREL2 & MP2 & MI2 & ST2 & ERR2 & AUX2 & EK1 & LBREL & ROOM & HEAP2 & SO2 & XP2 & (v2 & (MF2 & IM2 & GM2) & VLE)).
    subst K1. rewrite (unsigned_lit (bv_unsigned sp + -48)) in ST2, XP2 by lia.
    assert (HB2 := HH_blocks_below H HH _ _ _ HEAP2).
    pose proof SO2 as SO2'. destruct SO2' as ((pad2 & PL2 & HDR2) & _ & HIN2 & NC2 & CAP2 & _ & _ & DAT2).
    unfold sk_num in ROOM, NC2, CAP2, DAT2. cbn [sk_elems sk_cap sk_data sk_did sk_sorted sk_after_reserve] in ROOM, NC2, CAP2, DAT2, HIN2.
    destruct DAT2 as [[C0 _]|(D4 & DP & DDJ & DIN & AR2 & junk2 & JK2)]; [lia|].
    pose proof (HB2 _ DIN) as DBL. cbn [blk_addr blk_size fst snd] in DBL.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HEAP2 HIN2) as (_ & _ & _ & _ & AIMG). cbn [blk_addr blk_size fst snd] in AIMG. unfold SK_SIZE in AIMG.
    pose proof (HH_RHEAP_block_range H HH _ _ _ _ HEAP2 DIN) as (_ & _ & _ & _ & DIMG). cbn [blk_addr blk_size fst snd] in DIMG.
    eapply (xpres_rw_cells' _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia|].
    2:{ unfold memflag_foot, A_mem_inited, SK_foot, SK_SIZE. cbn [sk_cap sk_data sk_after_reserve].
        apply Forall_cons; [cbn; clear - SPR LO CEIL HCEILB; lia|]. apply Forall_cons; [cbn; clear - ABL SPR LO CEIL HCEILB; lia|].
        destruct (cap' =? 0); [apply Forall_nil|]. apply Forall_cons; [cbn; clear - DBL SPR LO CEIL HCEILB; lia| apply Forall_nil]. }
    (* [comment removed for export] *)
    unfold sk_after_reserve in HDR2.
    eapply (sr_evt_krel H HH); [exact KREL2| eapply pu_seg2 with (id := sk_id K);
      [exact HDR2| exact POS| clear - ABL LO CEIL; lia| lia| lia| lia| lia| exact NOC| exact DP| clear - DBL LO CEIL; lia| exact DDJ| exact PR| exact JK2| exact FR1| exact MI2]|].
    intros ms3 (a1' & a2' & a3' & m3 & -> & MU3 & WM3 & MI3 & HDR3 & EQ3 & JR3).
    apply (sr_done H HH). unfold skpush_post. cbn [cfg_ms cfg_model]. unfold sk_num.
    exists u0, u1, u2, a1', a2', a3', b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, s', LB'.
    exists (sk_after_push K p data' cap' did'), data', cap', did'.
    split; [reflexivity|]. split; [exact KREL2|]. split; [exact MP2|]. split; [exact MI3|].
    split. { apply (rw_cells_transport rsegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; clear - ABL DBL NC2 ROOM LO CEIL SPR; lia].
             apply (stk_transport_disjoint rsegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; clear - ABL DBL NC2 ROOM LO CEIL SPR; lia].
             unfold ins_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
    split. { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3| subst tp; rewrite errno_RATP; unfold RERRNO; cbn; clear - AIMG DIMG NC2 ROOM; lia]. }
    split. { eapply (HH_rauxv_frame H HH); [exact AUX2| exact MU3| exact WM3|]. unfold RAUXV_CELL.
             apply Forall_cons; [cbn; clear - ABL AIMG LO CEIL SPR SPB HCEILB; lia|]. apply Forall_cons; [cbn; clear - DBL DIMG NC2 ROOM LO CEIL SPR SPB HCEILB; lia| apply Forall_nil]. }
    split; [reflexivity|]. split; [exact LBREL|].
    split. { eapply (HH_RHEAP_frame H HH); [exact HEAP2| exact MU3| exact WM3|].
             apply Forall_cons; [right; right; exists (sk_id K, a, SK_SIZE); cbn; unfold SK_SIZE; split; [exact HIN2| lia]|].
             apply Forall_cons; [right; right; exists (did', data', 8 * cap'); cbn; split; [exact DIN| clear - NC2 ROOM; lia]| apply Forall_nil]. }
    split.
    { unfold SKobj, sk_num. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk sk_id sk_did sk_after_push].
      unfold sk_num. unfold zlength in *. rewrite length_app. cbn [length].
      split; [exists pad2; split; [exact PL2| exact HDR3]|]. split; [exact POS|]. split; [exact HIN2|].
      split; [lia|]. split; [lia|]. split; [destruct (sk_sorted K =? 1), (1 <=? Z.of_nat (length (sk_elems K))); cbn; lia|].
      split; [apply Forall_app; split; [exact EL| constructor; [lia| constructor]]|].
      right. split; [lia|]. split; [lia|]. split; [exact DDJ|]. split; [exact DIN|]. split.
      - rewrite map_app. cbn [map]. apply u64arr_snoc.
        + eapply u64arr_transport; [exact AR2| exact MU3| exact WM3|]. rewrite length_map. cbn. unfold SK_SIZE in DDJ. clear - DDJ NC2 ROOM. lia.
        + rewrite length_map. exact EQ3.
      - exists (skipn 8 junk2). replace (data' + 8 * Z.of_nat (length (sk_elems K) + 1)) with (data' + 8 * Z.of_nat (length (sk_elems K)) + 8) by lia.
        replace (Z.to_nat (8 * (cap' - Z.of_nat (length (sk_elems K) + 1)))) with (Z.to_nat (8 * (cap' - Z.of_nat (length (sk_elems K)))) - 8)%nat by lia.
        exact JR3. }
    split.
    { assert (FEQ : SK_foot a (sk_after_push K p data' cap' did') = SK_foot a (sk_after_reserve K data' cap' did')) by reflexivity. rewrite FEQ.
      eapply xpres_trans; [| eapply xpres_trans].
      - eapply xpres_of_munch; [exact MU1| exact WM1| | exact HB2]. apply Forall_cons; [left; cbn; lia| apply Forall_nil].
      - eapply xpres_weaken; [exact XP2| lia| auto| auto].
      - eapply xpres_of_munch_gen; [exact MU3| exact WM3|]. intros q Hq [HC HX]. rewrite rin_ivs_app in HX. unfold SK_foot, SK_SIZE in HX.
        cbn [sk_cap sk_data sk_after_reserve] in HX. replace (cap' =? 0) with false in HX by (symmetry; apply Z.eqb_neq; lia). cbn in HX |- *.
        clear - Hq HX NC2 ROOM. lia. }
    exists v2. split; [| exact VLE]. split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; clear - AIMG DIMG NC2 ROOM; lia| exact MF2]|].
    split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; clear - AIMG DIMG NC2 ROOM; lia| exact IM2]|].
    eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; clear - AIMG DIMG NC2 ROOM; lia| exact GM2].
  Qed.
End W.
