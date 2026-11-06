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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ser_req_ok : forall E esc spill isobj st s m need, senv_ok E -> SERM E esc spill isobj st s m ->
  sb_cap st < need -> need <= PJ_OUTMAX (e_len E) -> chain_ok (e_len E) (sb_cap st) (Z.max (2 * sb_cap st) need) = true.
Proof.
  intros E esc spill isobj st s m need OK HM H1 H2.
  eapply grow_request_ok; [destruct OK; lia| eapply SBINV_of_SERM; exact HM| exact H1| exact H2].
Qed.
Lemma ser_req_ok2 : forall E esc spill isobj st s m, senv_ok E -> SERM E esc spill isobj st s m ->
  sb_cap st < PJ_OUTMAX (e_len E) -> chain_ok (e_len E) (sb_cap st) (2 * sb_cap st) = true.
Proof.
  intros E esc spill isobj st s m OK HM H1.
  eapply grow_request_ok2; [destruct OK; lia| eapply SBINV_of_SERM; exact HM| exact H1].
Qed.

Lemma ser_copy : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (esc spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (fpc Src n rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  fpc = 0xca58c \/ fpc = MEMMOVE_T2 ->
  senv_ok E -> SERM E esc spill isobj st s m ->
  (exists src, bytes_at psegs m Src src /\ length src = Z.to_nat n) ->
  1 <= n -> sb_size st + n <= sb_cap st -> 0 <= Src -> Src + n < 2^63 ->
  (Src + n <= sb_buf st + sb_size st \/ sb_buf st + sb_size st + n <= Src) ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E esc spill isobj st s m' ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 (sb_buf st + sb_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
  evt psegs (sgoal E Q (sb_ch st) s)
      (SST E fpc (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (sb_buf st + sb_size st)) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros E Q esc spill isobj st s m fpc Src n rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         HPC OK HSM (src & SRC & LEN) N1 ROOM S0 S63 SEP RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  set (Dst := sb_buf st + sb_size st) in *.

  destruct (stk_split psegs m _ Dst _ BUFS ltac:(unfold Dst; lia)) as [BLO BREST].
  destruct (stk_split psegs m _ (Dst + n) _ BREST ltac:(unfold Dst; lia)) as [BMID BHI].
  destruct (stk_CB psegs m _ _ BMID ltac:(lia)) as (junk & DC). replace (Dst + n - Dst) with n in DC by lia.
  assert (POST : forall ms', memcpy_postZ (Z_to_bv 64 rpc) (Z_to_bv 64 (e_q E + -240)) (e_gp E) (Z_to_bv 64 RATP)
                               (Z_to_bv 64 (e_DOC E)) (Z_to_bv 64 (e_SB E)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src n src m ms' ->
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
    - unfold SCUR. split.
      { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. unfold Dst. lia. }
      split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply OUT. unfold Dst. lia. }
      split; [exact FRIL|].
      split. { eapply stk_agree; [exact AG| exact FRT|]. intros a Ha. apply OUT. unfold Dst. lia. }
      split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. unfold Dst. lia. }
      split. { eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. unfold Dst. lia. }
      split; [exact SZ|]. split; [exact BUFS'|].
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

Lemma sbuf_src : forall E esc spill isobj st s m o n, senv_ok E -> SERM E esc spill isobj st s m -> 0 <= o -> 0 <= n -> o + n <= e_sn E ->
  exists src, bytes_at psegs m (e_SBUF E + o) src /\ length src = Z.to_nat n.
Proof.
  intros E esc spill isobj st s m o n OK [HR _] Ho Hn Hb.
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

Lemma frt_src : forall E esc spill isobj st s m Src n, SERM E esc spill isobj st s m ->
  e_q E + -184 <= Src -> 0 <= n -> Src + n <= e_q E + -104 ->
  exists src, bytes_at psegs m Src src /\ length src = Z.to_nat n.
Proof.
  intros E esc spill isobj st s m Src n [_ HC] H1 Hn H2.
  destruct HC as (_ & _ & _ & FRT & _).
  destruct (stk_split psegs m _ Src _ FRT ltac:(lia)) as [_ S1].
  destruct (stk_split psegs m _ (Src + n) _ S1 ltac:(lia)) as [S2 _].
  destruct (stk_bytes psegs m _ _ S2 ltac:(lia)) as (bs & HL & HB).
  exists bs. split; [exact HB|]. rewrite HL. f_equal. lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma ser_grow : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (esc spill : word) (isobj : list byte)
         (st : sbst) (s : PState) (m : mem) (z rpc : Z) (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    senv_ok E -> SERM E esc spill isobj st s m -> chain_ok (e_len E) (sb_cap st) z = true ->
    0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
    (forall (s' : PState) (m' : mem) (b : bptr) (NEW : Z) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
        SERM E esc spill isobj (sb_grown st b NEW z) s' m' ->
        evt psegs (sgoal E Q (sb_ch (sb_grown st b NEW z)) s')
            (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
    evt psegs (sgoal E Q (sb_ch st) s)
        (SST E PJ_GROW (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof.
    intros E Q esc spill isobj st s m z rpc F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK HSM OKZ RP0 RP2 HK.
    pose proof (SBINV_of_SERM _ _ _ _ _ _ _ HSM) as INV.
    pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _].
    destruct (SBINV_fuel _ _ _ _ HLEN INV) as [f EF].
    destruct st as [buf size cap blk fuel]. cbn [sb_fuel] in EF. subst fuel.
    pose proof HSM as [HR HC].
    pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
    pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
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
    assert (HSM' : SERM E esc spill isobj (sb_grown (mkSb buf size cap blk (S f)) b NEW z) s' m').
    { pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
      assert (UP : forall a, e_q E + -240 <= a -> ~ (e_SB E + 64 <= a < e_SB E + 88) -> lx_client (e_LB0 E) (e_q E + -240) [(e_SB E + 64, e_SB E + 88)] a).
      { intros a Ha Hn. split; [cbn [rin_ivs fst snd]; tauto| left; exact Ha]. }
      assert (BL : forall a, in_block (e_LB0 E) a -> lx_client (e_LB0 E) (e_q E + -240) [(e_SB E + 64, e_SB E + 88)] a).
      { intros a Ha. split; [| right; left; exact Ha].
        assert (BLa : 0 < a < alloc_ceiling).
        { eapply blocks_below; [exact HEAP|]. destruct Ha as (b0 & Hb0 & Hr). exists b0. split; [apply in_or_app; right; exact Hb0| exact Hr]. }
        unfold PJ_GROW_STACK, RMALLOC_STACK in *. cbn [rin_ivs fst snd]. lia. }
      split.
      -
        unfold SREF. split; [exact HEAP'|]. split; [exact AUX'|].
        split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact PRES'| lia| intros b0 Hb0; exact Hb0|].
                 intros a Ha. cbn [rin_ivs fst snd] in *. lia. }
        split. { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
                 apply BL. eapply in_blocks_in_block; [exact OKT| lia]. }
        split. { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
                 apply BL. eapply in_blocks_in_block; [exact OKS| lia]. }
        split. { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
        split. { exists errv'. exact ERR'. }
        split; [congruence|]. split; [congruence|]. eapply sb_pure_of_SBINV; exact INV'.
      -
        pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & _).
        unfold SCUR. split.
        { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
        split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply UP; lia. }
        split; [exact FRIL|].
        split. { eapply stk_agree; [exact AG| exact FRT|]. intros a Ha. apply UP; lia. }
        split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
        split; [exact SV'|]. split; [exact SZ'|].
        split. { pose proof (stk_of_rw_cells psegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S.
                 pose proof (SBINV_cap_pos _ _ _ _ INV') as CP. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
        split. { pose proof (stk_of_rw_cells psegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S. }
        split; [exact MI'|]. exact ST'. }
    unfold implM. apply impl_from_evt.
    change (evt psegs (sgoal E Q (sb_ch (sb_grown (mkSb buf size cap blk (S f)) b NEW z)) s')
              (SST E rpc (Z_to_bv 64 rpc) r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31 F fc m')).
    apply HK. exact HSM'.
  Qed.

End Proofs.
End WithCeiling0.
