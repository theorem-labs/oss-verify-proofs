(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition frame_local (E : senv) (fb : Z) (FRP : mem -> Prop) : Prop :=
  forall m m', agree_on (fun a => fb <= a < e_q E) m m' -> FRP m -> FRP m'.

Definition CCUR (E : senv) (fb : Z) (FRP : mem -> Prop) (st : sbst) (m : mem) : Prop :=
  FRP m
  /\ rw_cells psegs m (e_SB E + 64) [C8 (Z_to_bv 64 (sb_buf st)); C8 (Z_to_bv 64 (sb_size st)); C8 (Z_to_bv 64 (sb_cap st))]
  /\ 0 <= sb_size st <= sb_cap st
  /\ stk psegs m (sb_buf st) (sb_buf st + sb_cap st)
  /\ stk psegs m (e_SB E) (e_SB E + 64)
  /\ mem_inv psegs m
  /\ stk psegs m (e_lo E) fb.

Definition CERM (E : senv) (fb : Z) (FRP : mem -> Prop) (st : sbst) (s : PState) (m : mem) : Prop :=
  SREF E st s m /\ CCUR E fb FRP st m.

Definition cont_Q (E : senv) : @chst bptr -> PState -> machine_state -> Prop :=
  ser_post (e_ra E) (e_q E) (e_gp E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E)
           (e_ps0 E) (e_LB0 E) (e_lo E) (e_B E) (e_SB E) (e_len E) (e_j E) (e_c' E) (e_m0 E).

Lemma CERM_intro : forall E fb FRP st s mr m size,
  senv_ok E -> SREF E st s mr -> munch (serW E st) mr m -> wmono psegs mr m ->
  FRP m ->
  rw_cells psegs m (e_SB E + 64) [C8 (Z_to_bv 64 (sb_buf st)); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 (sb_cap st))] ->
  0 <= size <= sb_cap st ->
  stk psegs m (sb_buf st) (sb_buf st + sb_cap st) -> stk psegs m (e_SB E) (e_SB E + 64) ->
  mem_inv psegs m -> stk psegs m (e_lo E) fb ->
  CERM E fb FRP (sb_resize st size) s m.
Proof.
  intros E fb FRP st s mr m size OK HR MU WM HFRP SV SZ BUFS INLS MI ST.
  split; [apply (SREF_munch E st s mr m size OK HR MU WM)|].
  unfold CCUR. destruct st as [buf sz cap blk fuel]. cbn [sb_resize sb_buf sb_size sb_cap sb_blk sb_fuel] in *.
  repeat (split; [assumption|]). assumption.
Qed.

Lemma SBINV_of_CERM : forall E fb FRP st s m, CERM E fb FRP st s m -> SBINV m (e_SB E) (e_len E) st.
Proof.
  intros E fb FRP st s m [HR HC].
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (HF & HCAP & HB)).
  destruct HC as (_ & SV & SZ & BUFS & INLS & _ & _).
  unfold SBINV. split; [exact SV|]. split; [exact SZ|].
  split. { destruct (stk_CB psegs m _ _ BUFS ltac:(lia)) as (bs & HBS). exists bs.
           replace (sb_buf st + sb_cap st - sb_buf st) with (sb_cap st) in HBS by lia. exact HBS. }
  split. { destruct (stk_CB psegs m _ _ INLS ltac:(lia)) as (bs & HBS). exists bs.
           replace (Z.to_nat (e_SB E + 64 - e_SB E)) with 64%nat in HBS by lia. exact HBS. }
  split; [exact HF|]. split; [exact HCAP| exact HB].
Qed.

Lemma DOCREP_of_SREF : forall E st s m, senv_ok E -> SREF E st s m ->
  DOCREP m (e_LB0 E) (e_DOC E) (e_TAPE E) (e_SBUF E) (e_len E) (e_tws E) (e_sbs E).
Proof.
  intros E st s m OK HR.
  destruct HR as (_ & _ & _ & TAPEB & SBUFB & DOCC & _).
  destruct OK as [WF SBS TSZ SSZ OKT OKS _ _ _ _ _ _ _ _ _].
  unfold DOCREP. split; [exact DOCC|]. split; [exact TAPEB|]. split; [exact SBUFB|]. split; [exact WF|]. split; [exact SBS|].
  split; [exact TSZ|]. split; [exact SSZ|]. split; [exact OKT| exact OKS].
Qed.

Lemma cont_ranges : forall E st s m, senv_ok E -> SREF E st s m ->
  0 < e_TAPE E /\ e_TAPE E + 8 * e_n E <= alloc_ceiling /\ 0 < e_SBUF E /\ e_SBUF E + e_sn E <= alloc_ceiling.
Proof.
  intros E st s m OK (HEAP & _). destruct OK as [_ _ _ _ (bt & Bt & Bt1 & Bt2) (bs & Bs & Bs1 & Bs2) _ _ _ _ _ _ _ _ _].
  pose proof (LH_block_range _ _ _ _ HEAP (in_or_app _ _ _ (or_intror Bt))) as (T1 & _ & T3 & T4 & _).
  pose proof (LH_block_range _ _ _ _ HEAP (in_or_app _ _ _ (or_intror Bs))) as (S1 & _ & S3 & S4 & _).
  unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in *. lia.
Qed.

Lemma cont_req_ok : forall E fb FRP st s m need, senv_ok E -> CERM E fb FRP st s m ->
  sb_cap st < need -> need <= PJ_OUTMAX (e_len E) -> chain_ok (e_len E) (sb_cap st) (Z.max (2 * sb_cap st) need) = true.
Proof.
  intros E fb FRP st s m need OK HM H1 H2.
  eapply grow_request_ok; [destruct OK; lia| eapply SBINV_of_CERM; exact HM| exact H1| exact H2].
Qed.
Lemma cont_req_ok2 : forall E fb FRP st s m, senv_ok E -> CERM E fb FRP st s m ->
  sb_cap st < PJ_OUTMAX (e_len E) -> chain_ok (e_len E) (sb_cap st) (2 * sb_cap st) = true.
Proof.
  intros E fb FRP st s m OK HM H1.
  eapply grow_request_ok2; [destruct OK; lia| eapply SBINV_of_CERM; exact HM| exact H1].
Qed.

Lemma CERM_after_call : forall E fb FRP st st' s s' m m' (errv' : word) (X : Z * Z),
  senv_ok E -> e_q E - 240 <= fb <= e_q E -> frame_local E fb FRP -> CERM E fb FRP st s m ->
  e_SB E <= fst X -> snd X = e_SB E + 88 ->
  lx_pres (e_LB0 E) fb [X] m m' ->
  RHEAP s' (sbblocks st' ++ e_LB0 E) m' -> rauxv_ok m' (e_B E) ->
  rw_cells psegs m' LX_ERRNO [C4 errv'] -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  SBINV m' (e_SB E) (e_len E) st' -> mem_inv psegs m' -> stk psegs m' (e_lo E) fb ->
  CERM E fb FRP st' s' m'.
Proof.
  intros E fb FRP st st' s s' m m' errv' X OK HFB LOC [HR HC] HX1 HX2 PRES' HEAP' AUX' ERR' FA' SO' INV' MI' ST'.
  pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _].
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof HC as (HFRP & SV & SZ & BUFS & INLS & MI & ST).
  destruct X as [x1 x2]. cbn [fst snd] in HX1, HX2. subst x2.
  pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
  assert (UP : forall a, fb <= a -> ~ (e_SB E <= a < e_SB E + 88) -> lx_client (e_LB0 E) fb [(x1, e_SB E + 88)] a).
  { intros a Ha Hn. split; [cbn [rin_ivs fst snd]; lia| left; exact Ha]. }
  assert (BL : forall a, in_block (e_LB0 E) a -> lx_client (e_LB0 E) fb [(x1, e_SB E + 88)] a).
  { intros a Ha. split; [| right; left; exact Ha].
    assert (BLa : 0 < a < alloc_ceiling).
    { eapply blocks_below; [exact HEAP|]. destruct Ha as (b0 & Hb0 & Hr). exists b0. split; [apply in_or_app; right; exact Hb0| exact Hr]. }
    unfold PJ_GROW_STACK, RMALLOC_STACK in *. cbn [rin_ivs fst snd]. lia. }
  split.
  - unfold SREF. split; [exact HEAP'|]. split; [exact AUX'|].
    split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES'| lia| intros b0 Hb0; exact Hb0|].
             intros a Ha. cbn [rin_ivs fst snd] in *. lia. }
    split. { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
             apply BL. eapply in_blocks_in_block; [exact OKT| lia]. }
    split. { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
             apply BL. eapply in_blocks_in_block; [exact OKS| lia]. }
    split. { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
    split. { exists errv'. exact ERR'. }
    split; [congruence|]. split; [congruence|]. eapply sb_pure_of_SBINV; exact INV'.
  - pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & _).
    unfold CCUR. split.
    { eapply LOC; [| exact HFRP]. eapply agree_on_mono; [exact AG|]. intros a Ha. apply UP; lia. }
    split; [exact SV'|]. split; [exact SZ'|].
    split. { pose proof (stk_of_rw_cells psegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S.
             pose proof (SBINV_cap_pos _ _ _ _ INV') as CP. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
    split. { pose proof (stk_of_rw_cells psegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S. }
    split; [exact MI'|]. exact ST'.
Qed.

Section Calls.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma cont_grow : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (fb : Z) (FRP : mem -> Prop)
         (st : sbst) (s : PState) (m : mem) (z rpc : Z) (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    senv_ok E -> e_q E - 240 <= fb <= e_q E -> frame_local E fb FRP ->
    CERM E fb FRP st s m -> chain_ok (e_len E) (sb_cap st) z = true ->
    0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
    (forall (s' : PState) (m' : mem) (b : bptr) (NEW : Z) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
        CERM E fb FRP (sb_grown st b NEW z) s' m' ->
        evt psegs (sgoal E Q (sb_ch (sb_grown st b NEW z)) s')
            (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                F (Z_to_bv 64 rpc) fc None m' (seg_rom psegs))) ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 PJ_GROW) fc None m (seg_rom psegs)).
  Proof.
    intros E Q fb FRP st s m z rpc F fc t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK HFB LOC HSM OKZ RP0 RP2 HK.
    pose proof (SBINV_of_CERM _ _ _ _ _ _ HSM) as INV.
    pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _].
    destruct (SBINV_fuel _ _ _ _ HLEN INV) as [f EF].
    destruct st as [buf size cap blk fuel]. cbn [sb_fuel] in EF. subst fuel.
    pose proof HSM as [HR HC].
    pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
    pose proof HC as (HFRP & SV & SZ & BUFS & INLS & MI & ST).
    apply evt_done. unfold sgoal, sb_ch. cbn [ch_fuel ch_cap ch_blk fst snd sb_fuel sb_cap sb_blk].
    eapply implM_pj_part_grow; [exact OKZ|].
    eapply implM_bind.
    { eapply (grow_proof HM HF) with (LB0 := e_LB0 E) (lo := e_lo E) (B := e_B E) (SB := e_SB E) (len := e_len E) (st := mkSb buf size cap blk (S f)) (errv := errv);
        [exact HEAP| exact AUX| lia| exact B63| exact ST| exact L1| exact L2| unfold PJ_GROW_STACK, RMALLOC_STACK in *; lia
        | exact ERR| exact MI| lia| exact S2| exact HLEN| exact INV| exact OKZ]. }
    cbv beta. intros b s' ms' PO. unfold grow_post in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m' & errv' & NEW
                    & -> & MI' & ST' & ERR' & AUX' & FA' & SO' & HEAP' & INV' & PRES').
    rewrite (ret_pc_even rpc RP0 RP2).
    assert (HSM' : CERM E fb FRP (sb_grown (mkSb buf size cap blk (S f)) b NEW z) s' m').
    { eapply (CERM_after_call E fb FRP _ _ s s' m m' errv' (e_SB E + 64, e_SB E + 88)); try eassumption; cbn [fst snd]; lia. }
    unfold implM. apply impl_from_evt.
    change (evt psegs (sgoal E Q (sb_ch (sb_grown (mkSb buf size cap blk (S f)) b NEW z)) s')
              (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) r5 r6 r7 s0 s1 r10 r11 r12 r13 r14 r15 r16 r17
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31)
                  F (Z_to_bv 64 rpc) fc None m' (seg_rom psegs))).
    apply HK. exact HSM'.
  Qed.

End Calls.

Lemma cont_call_ser : forall (d : nat) (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (fb : Z) (FRP : mem -> Prop)
       (st : sbst) (s : PState) (m : mem) (x x' c c1 rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  ser_stmt d ->
  senv_ok E -> e_q E - 240 <= fb <= e_q E -> frame_local E fb FRP ->
  CERM E fb FRP st s m -> frm0 fc ->
  e_lo E <= fb - ser_need d ->
  elemS (e_T E) (e_S E) (e_sn E) ck_any d x x' c c1 -> 1 <= x -> x' <= e_n E -> 0 <= c -> c1 <= e_sn E ->
  sb_acc1 st x c ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (st' : sbst) (s' : PState) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32)
          (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      CERM E fb FRP st' s' m' -> frm0 fc' -> sb_acc st' x' c1 ->
      evt psegs (sgoal E Q (sb_ch st') s')
          (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F' (Z_to_bv 64 rpc) fc' None m' (seg_rom psegs))) ->
  evt psegs (sgoal E Q (sb_ch st) s)
      (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 x) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PJ_APPEND_ELEM) fc None m (seg_rom psegs)).
Proof.
  intros d E Q fb FRP st s m x x' c c1 rpc F fc t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         SER OK HFB LOC HSM FRM STK HEL HX HX' HC HC1 ACC RP0 RP2 HK.
  pose proof (SBINV_of_CERM _ _ _ _ _ _ HSM) as INV.
  pose proof HSM as [HR HC0].
  pose proof (DOCREP_of_SREF _ _ _ _ OK HR) as DOCR.
  pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _].
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof HC0 as (HFRP & SV & SZ & BUFS & INLS & MI & ST).
  apply evt_done. unfold sgoal.
  apply implM_pj_part_seq.
  eapply implM_bind.
  { eapply (SER (Z_to_bv 64 rpc) (e_gp E) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m s (e_LB0 E) fb (e_lo E) (e_B E) errv (e_SB E) (e_len E) st (e_DOC E) (e_TAPE E) (e_SBUF E) (e_tws E) (e_sbs E) x x' c c1);
      [exact HEAP| exact AUX| lia| exact B63| exact ST| exact L1| exact L2| exact STK
      | exact ERR| exact MI| exact FRM| lia| exact S2| lia| exact D2| exact SEP| exact HLEN| exact INV| exact DOCR
      | exact HEL| exact HX| exact HX'| exact HC| exact HC1| exact ACC]. }
  cbv beta. intros ch' s' ms' PO. unfold ser_post in PO.
  destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & F' & fc' & m' & errv' & st'
                  & -> & MI' & ST' & ERR' & AUX' & FRM' & FA' & SO' & -> & HEAP' & INV' & ACC' & PRES').
  rewrite (ret_pc_even rpc RP0 RP2).
  assert (HSM' : CERM E fb FRP st' s' m').
  { eapply (CERM_after_call E fb FRP _ _ s s' m m' errv' (e_SB E, e_SB E + 88)); try eassumption; cbn [fst snd]; lia. }
  unfold implM. apply impl_from_evt.
  change (evt psegs (sgoal E Q (sb_ch st') s')
            (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) r5 r6 r7 s0 s1 r10 r11 r12 r13 r14 r15 r16 r17
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31)
                F' (Z_to_bv 64 rpc) fc' None m' (seg_rom psegs))).
  apply HK; [exact HSM'| exact FRM'| exact ACC'].
Qed.

Lemma sref_sep : forall E st s m, senv_ok E -> SREF E st s m ->
  (e_TAPE E + 8 * e_n E <= sb_buf st \/ sb_buf st + sb_cap st <= e_TAPE E)
  /\ (e_SBUF E + e_sn E <= sb_buf st \/ sb_buf st + sb_cap st <= e_SBUF E).
Proof.
  intros E st s m OK HR.
  pose proof (cont_ranges _ _ _ _ OK HR) as (T0 & T1 & S0 & S1).
  destruct HR as (HEAP & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & PB)).
  pose proof OK as [_ _ _ _ (bt & Bt & Bt1 & Bt2) (bs & Bs & Bs1 & Bs2) _ [L1 L2] [Q1 Q2] B63 [SS1 SS2] _ _ _ _].
  unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold sbblocks in HEAP. destruct (sb_blk st) as [b|].
  - cbn [app] in HEAP. destruct bt as [[pt At] nt]. destruct bs as [[ps As] ns]. cbn [blk_addr blk_size fst snd] in *.
    pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP Bt) as D1. pose proof (LH_head_sep _ _ _ _ _ _ _ _ _ HEAP Bs) as D2. lia.
  - destruct PB as (EB & EC & _). lia.
Qed.

Lemma sbuf_srcR : forall E st s m o n, senv_ok E -> SREF E st s m -> 0 <= o -> 0 <= n -> o + n <= e_sn E ->
  exists src, bytes_at psegs m (e_SBUF E + o) src /\ length src = Z.to_nat n.
Proof.
  intros E st s m o n OK HR Ho Hn Hb.
  destruct HR as (_ & _ & _ & _ & SBUFB & _).
  exists (firstn (Z.to_nat n) (skipn (Z.to_nat o) (map (Z_to_bv 8) (e_sbs E)))). split.
  - pose proof SBUFB as (B0 & B1 & BB). rewrite length_map in B1.
    split; [lia|]. split; [rewrite firstn_length, skipn_length, length_map; lia|].
    intros i Hi. rewrite firstn_length, skipn_length, length_map in Hi.
    replace (e_SBUF E + o + Z.of_nat i) with (e_SBUF E + Z.of_nat (Z.to_nat o + i)) by lia.
    rewrite BB by (rewrite length_map; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat n)) as [L|L]; [| lia]. rewrite nth_error_skipn. reflexivity.
  - rewrite firstn_length, skipn_length, length_map. lia.
Qed.

Lemma stk_src : forall (m : mem) lo hi Src n, stk psegs m lo hi -> lo <= Src -> 0 <= n -> Src + n <= hi ->
  exists src, bytes_at psegs m Src src /\ length src = Z.to_nat n.
Proof.
  intros m lo hi Src n ST H1 Hn H2.
  destruct (stk_split psegs m _ Src _ ST ltac:(lia)) as [_ S1].
  destruct (stk_split psegs m _ (Src + n) _ S1 ltac:(lia)) as [S2 _].
  destruct (stk_bytes psegs m _ _ S2 ltac:(lia)) as (bs & HL & HB).
  exists bs. split; [exact HB|]. rewrite HL. f_equal. lia.
Qed.

Lemma cont_sbuf_src : forall E fb FRP st s m o n, senv_ok E -> CERM E fb FRP st s m -> 0 <= o -> 0 <= n -> o + n <= e_sn E ->
  exists src, bytes_at psegs m (e_SBUF E + o) src /\ length src = Z.to_nat n.
Proof. intros E fb FRP st s m o n OK [HR _] Ho Hn Hb. eapply sbuf_srcR; [exact OK| exact HR| lia| lia| lia]. Qed.

Lemma cont_sep : forall E fb FRP st s m, senv_ok E -> CERM E fb FRP st s m ->
  (e_TAPE E + 8 * e_n E <= sb_buf st \/ sb_buf st + sb_cap st <= e_TAPE E)
  /\ (e_SBUF E + e_sn E <= sb_buf st \/ sb_buf st + sb_cap st <= e_SBUF E).
Proof. intros E fb FRP st s m OK [HR _]. eapply sref_sep; [exact OK| exact HR]. Qed.

Lemma cont_rangesC : forall E fb FRP st s m, senv_ok E -> CERM E fb FRP st s m ->
  0 < e_TAPE E /\ e_TAPE E + 8 * e_n E <= alloc_ceiling /\ 0 < e_SBUF E /\ e_SBUF E + e_sn E <= alloc_ceiling.
Proof. intros E fb FRP st s m OK [HR _]. eapply cont_ranges; [exact OK| exact HR]. Qed.

Lemma cont_copy : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (fb : Z) (FRP : mem -> Prop)
       (st : sbst) (s : PState) (m : mem) (fpc Src n rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  fpc = 0xca58c \/ fpc = MEMMOVE_T2 ->
  senv_ok E -> e_q E - 240 <= fb <= e_q E -> frame_local E fb FRP -> CERM E fb FRP st s m ->
  (exists src, bytes_at psegs m Src src /\ length src = Z.to_nat n) ->
  1 <= n -> sb_size st + n <= sb_cap st -> 0 <= Src -> Src + n < 2^63 ->
  (Src + n <= sb_buf st + sb_size st \/ sb_buf st + sb_size st + n <= Src) ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      CERM E fb FRP st s m' ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) xt0 xt1 xt2 s0 s1
                   (Z_to_bv 64 (sb_buf st + sb_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F (Z_to_bv 64 rpc) fc None m' (seg_rom psegs))) ->
  evt psegs (sgoal E Q (sb_ch st) s)
      (MS (mkR (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP) t0 t1 t2 s0 s1
               (Z_to_bv 64 (sb_buf st + sb_size st)) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 fpc) fc None m (seg_rom psegs)).
Proof.
  intros E Q fb FRP st s m fpc Src n rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         HPC OK HFB LOC HSM (src & SRC & LEN) N1 ROOM S0 S63 SEP RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as (HFRP & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  set (Dst := sb_buf st + sb_size st) in *.
  destruct (stk_split psegs m _ Dst _ BUFS ltac:(unfold Dst; lia)) as [BLO BREST].
  destruct (stk_split psegs m _ (Dst + n) _ BREST ltac:(unfold Dst; lia)) as [BMID BHI].
  destruct (stk_CB psegs m _ _ BMID ltac:(lia)) as (junk & DC). replace (Dst + n - Dst) with n in DC by lia.
  assert (POST : forall ms', memcpy_postZ (Z_to_bv 64 rpc) (Z_to_bv 64 fb) (e_gp E) (Z_to_bv 64 RATP)
                               s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src n src m ms' ->
                             evt psegs (sgoal E Q (sb_ch st) s) ms').
  { intros ms' PO. unfold memcpy_postZ in PO.
    destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & -> & MU' & WM' & MI' & DC' & SRC').
    rewrite (ret_pc_even rpc RP0 RP2).
    apply HK.
    assert (MUW : munch (serW E st) m m').
    { eapply munch_weaken; [| exact MU']. intros x Hx. unfold serW in Hx. cbn [outside] in Hx |- *. split; [unfold Dst; lia| exact I]. }
    pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
    assert (OUT : forall a, a < Dst \/ Dst + n <= a -> outside [(Dst, Dst + n)] a) by (intros a Ha; cbn [outside]; split; [lia| exact I]).
    assert (BUFS' : stk psegs m' (sb_buf st) (sb_buf st + sb_cap st)).
    { pose proof (stk_of_rw_cells psegs _ _ _ DC') as SM. cbn [cells_size csize Nat.add] in SM. rewrite Nat.add_0_r, Z2Nat.id in SM by lia.
      eapply stk_merge; [eapply stk_agree; [exact AG| exact BLO| intros a Ha; apply OUT; lia]| | unfold Dst; lia].
      eapply stk_merge; [exact SM| eapply stk_agree; [exact AG| exact BHI| intros a Ha; apply OUT; lia]| unfold Dst; lia]. }
    split.
    - replace st with (sb_resize st (sb_size st)) by (destruct st; reflexivity).
      apply (SREF_munch E st s m m' (sb_size st) OK HR MUW WM').
    - unfold CCUR. split.
      { eapply LOC; [| exact HFRP]. eapply agree_on_mono; [exact AG|]. intros a Ha. apply OUT. unfold Dst. lia. }
      split; [| split; [exact SZ| split; [exact BUFS'|]]].
      { eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. unfold Dst. lia. }
      split. { destruct PURE as (_ & _ & PB). destruct (sb_blk st) as [b|].
               - destruct PB as (A0 & A16 & N0 & AC & AS). unfold OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec.Malloc.MCEIL in AC.
                 eapply stk_agree; [exact AG| exact INLS|]. intros a Ha. apply OUT. unfold Dst. lia.
               - destruct PB as (EB & EC & _). rewrite EB, EC in BUFS'. exact BUFS'. }
      split; [exact MI'|].
      eapply stk_agree; [exact AG| exact ST|]. intros a Ha. apply OUT. unfold Dst. lia. }
  destruct HPC as [-> | ->].
  - eapply evt_cut; [| exact POST].
    eapply memcpy_callZ with (src := src) (junk := junk); [exact SRC| exact LEN| exact DC| fold Dst in SEP; exact SEP| lia| lia| unfold Dst; lia| exact MI].
  - eapply evt_cut; [| exact POST].
    eapply memmove_far_callZ with (src := src) (junk := junk);
      [exact SRC| exact LEN| exact DC| fold Dst in SEP; exact SEP| lia| lia| lia| unfold Dst; lia| unfold Dst; lia| exact MI].
Qed.

End WithCeiling0.

Ltac cont_open HM OK :=
  let HCUR := fresh "HCUR" in
  let SZ := fresh "SZ" in let R0 := fresh "R0" in let R1 := fresh "R1" in let R2 := fresh "R2" in let R3 := fresh "R3" in
  unfold CERM, sb_grown, sb_resize in HM; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel Nat.pred] in HM;
  destruct HM as [HREF HCUR];
  unfold CCUR in HCUR; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in HCUR;
  destruct HCUR as (HFRP & SV & SZ & BUFS & INLS & MI & ST);
  lazymatch type of HREF with
  | SREF ?E ?st ?s ?m =>
      pose proof (munch_refl (serW E st) m) as MU; pose proof (wmono_refl psegs m) as WM;
      unfold serW in MU; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in MU;
      let PU := fresh "PU" in
      assert (PU : sb_pure E st) by (apply HREF);
      pose proof (sb_pure_ranges E st OK PU) as (R0 & R1 & R2 & R3 & _);
      cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in R0, R1, R2, R3; clear PU
  end.

Ltac cont_close fb FRP HM OK :=
  match goal with
  | HREF : SREF ?E ?st ?s ?mr, MU : munch _ ?mr ?m, WM : wmono _ ?mr ?m,
    SV : rw_cells _ ?m (e_SB ?E + 64) [C8 (Z_to_bv 64 ?buf); C8 (Z_to_bv 64 ?size); C8 (Z_to_bv 64 ?cap)],
    BUFS : stk _ ?m ?buf (?buf + ?cap), INLS : stk _ ?m (e_SB ?E) (e_SB ?E + 64),
    MI : mem_inv _ ?m, ST : stk _ ?m (e_lo ?E) _ |- _ =>
      let SZ' := fresh "SZc" in
      first [ assert (SZ' : 0 <= size <= sb_cap st) by (cbn [sb_cap]; lia) | fail 100 "cont_close: cannot prove 0 <= size <= cap" ];
      let HP := fresh "HFRPc" in
      first [ assert (HP : FRP m) by assumption | fail 100 "cont_close: no frame fact FRP m" ];
      first [ pose proof (CERM_intro E fb FRP st s mr m size OK HREF MU WM HP SV SZ' BUFS INLS MI ST) as HM
            | fail 100 "cont_close: CERM_intro does not apply" ];
      unfold sb_resize in HM; cbn [sb_buf sb_size sb_cap sb_blk sb_fuel] in HM;
      clear SZ' MU WM HP; clear SV; try clear BUFS; try clear INLS; clear ST; clear MI; clear HREF;
      repeat match goal with HX : _ |- _ => let _ := constr:(HX : FRP m) in clear HX end
  | _ => fail 100 "cont_close: the open context is incomplete"
  end.
