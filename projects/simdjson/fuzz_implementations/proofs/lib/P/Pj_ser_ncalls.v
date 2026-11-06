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
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Pj_defs Pj_kit Pj_grow Pj_ser_defs Pj_ser_kit Pj_ser_calls Pj_num_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Ltac nst_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
  | |- _ => reflexivity
  end.
Ltac nst_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; nst_eq_tree
  | |- Some _ = Some _ => f_equal; nst_eq_leaf
  | |- _ => reflexivity
  end.
Ltac nst_eq :=
  cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; nst_eq_tree
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma SREF_munch_stack : forall E st s m m', senv_ok E -> SREF E st s m ->
  munch [(e_lo E, e_q E)] m m' -> wmono psegs m m' -> SREF E st s m'.
Proof.
  intros E st s m m' OK HR MU WM.
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  pose proof OK as [_ _ _ _ OKT OKS _ [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  assert (OUTB : forall a, in_block (e_LB0 E) a -> outside [(e_lo E, e_q E)] a).
  { intros a HB.
    assert (BL : 0 < a < alloc_ceiling).
    { eapply blocks_below; [exact HEAP|]. destruct HB as (b & Hb & Hr). exists b. split; [apply in_or_app; right; exact Hb| exact Hr]. }
    cbn [outside]. split; [lia| exact I]. }
  unfold SREF.
  split.
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
  split.
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split.
  { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX.
    destruct HC as [HC|[HC|HC]].
    - cbn [outside]. split; [lia| exact I].
    - apply OUTB. exact HC.
    - cbn [outside]. split; [lia| exact I]. }
  split.
  { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
    apply OUTB. eapply in_blocks_in_block; [exact OKT| lia]. }
  split.
  { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
    apply OUTB. eapply in_blocks_in_block; [exact OKS| lia]. }
  split.
  { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    cbn [outside]. split; [lia| exact I]. }
  split.
  { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    unfold LX_ERRNO, RATP in Ha. cbn [outside]. split; [lia| exact I]. }
  split; [exact FA|]. split; [exact SO|]. exact PURE.
Qed.

Lemma SCUR_after : forall E esc spill isobj st m m' W TL TH,
  senv_ok E -> sb_pure E st -> SCUR E esc spill isobj st m ->
  munch W m m' -> wmono psegs m m' -> mem_inv psegs m' ->
  (forall a, outside [(e_lo E, e_q E + -240); (TL, TH)] a -> outside W a) ->
  e_q E + -184 <= TL -> TL <= TH -> TH <= e_q E + -104 ->
  stk psegs m' TL TH -> stk psegs m' (e_lo E) (e_q E + -240) ->
  SCUR E esc spill isobj st m'.
Proof.
  intros E esc spill isobj st m m' W TL TH OK PURE HC MU WM MI' SUB T1 T2 T3 STT ST'.
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (OUT : forall a, (e_q E + -240 <= a < TL \/ TH <= a) \/ a < e_lo E -> outside W a).
  { intros a Ha. apply SUB. cbn [outside]. split; [lia|]. split; [lia| exact I]. }
  destruct (stk_split psegs m _ TL _ FRT ltac:(lia)) as [TLO TREST].
  destruct (stk_split psegs m _ TH _ TREST ltac:(lia)) as [_ THI].
  unfold SCUR. split.
  { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. lia. }
  split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply OUT. lia. }
  split; [exact FRIL|].
  split.
  { eapply stk_merge; [eapply stk_agree; [exact AG| exact TLO| intros a Ha; apply OUT; lia]| | lia].
    eapply stk_merge; [exact STT| eapply stk_agree; [exact AG| exact THI| intros a Ha; apply OUT; lia]| lia]. }
  split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. lia. }
  split. { eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT. lia. }
  split; [exact SZ|].
  split. { eapply stk_agree; [exact AG| exact BUFS|]. intros a Ha. apply OUT. lia. }
  split. { eapply stk_agree; [exact AG| exact INLS|]. intros a Ha. apply OUT. lia. }
  split; [exact MI'| exact ST'].
Qed.

Lemma ser_tochars : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (esc spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  tochars_stmt ->
  senv_ok E -> SERM E esc spill isobj st s m -> frm0 fc ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (e : Z) (F' : bvmap 5 word) (fc' : bv 32) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E esc spill isobj st s m' -> frm0 fc' -> e_q E + -164 < e <= e_q E + -164 + 27 ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 e) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F' fc' m')) ->
  evt psegs (sgoal E Q (sb_ch st) s)
      (SST E TC_ENTRY (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_q E + -164)) a1 a2 a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros E Q esc spill isobj st s m rpc F fc t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         HTC OK HSM FRM RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  set (NB := e_q E + -164) in *.
  destruct (stk_split psegs m _ NB _ FRT ltac:(unfold NB; lia)) as [_ TREST].
  destruct (stk_split psegs m _ (NB + 40) _ TREST ltac:(unfold NB; lia)) as [TMID _].
  destruct (stk_CB psegs m _ _ TMID ltac:(lia)) as (junk & NBC). replace (Z.to_nat (NB + 40 - NB)) with 40%nat in NBC by lia.
  eapply evt_cut.
  { eapply (HTC (Z_to_bv 64 rpc) (e_gp E) (Z_to_bv 64 RATP)) with (q := e_q E + -240) (lo := e_lo E) (NB := NB) (junk := junk);
      [exact ST | unfold TC_STACK; lia | unfold GLOBALS_TOP; lia | exact MI | exact FRM | unfold NB; lia | unfold NB; lia | exact NBC]. }
  cbv beta. intros ms' PO. unfold tochars_post in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & F' & fc' & m' & e & nb
                  & -> & MU' & WM' & MI' & ST' & FRM' & HE & NBC').
  rewrite (ret_pc_even rpc RP0 RP2).
  apply HK; [| exact FRM' | exact HE].
  unfold TC_STACK in MU'.
  split.
  - eapply (SREF_munch_stack E st s m m' OK HR); [| exact WM'].
    eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside] in Hx |- *. unfold NB. split; [lia|]. split; [lia| exact I].
  - eapply (SCUR_after E esc spill isobj st m m' _ NB (NB + 40) OK PURE HC MU' WM' MI'); [| unfold NB; lia | lia | unfold NB; lia | | exact ST'].
    + intros a Ha. cbn [outside] in Ha |- *. split; [lia|]. split; [lia| exact I].
    + pose proof (stk_of_rw_cells psegs _ _ _ NBC') as SM. cbn [cells_size csize Nat.add] in SM. change (Z.of_nat 40) with 40 in SM. exact SM.
Qed.

Lemma ser_frt_memcpy : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (esc spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (Dst Src n rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  senv_ok E -> SERM E esc spill isobj st s m ->
  e_q E + -184 <= Dst -> Dst + n <= e_q E + -104 -> e_q E + -184 <= Src -> Src + n <= e_q E + -104 ->
  0 <= n -> (Src + n <= Dst \/ Dst + n <= Src) ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E esc spill isobj st s m' ->
      evt psegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 Dst) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
  evt psegs (sgoal E Q (sb_ch st) s)
      (SST E 0xca58c (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros E Q esc spill isobj st s m Dst Src n rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         OK HSM D1 D2 C1 C2 N0 SEP RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  destruct (frt_src E esc spill isobj st s m Src n HSM C1 N0 C2) as (src & SRC & LEN).
  destruct (stk_split psegs m _ Dst _ FRT ltac:(lia)) as [_ TREST].
  destruct (stk_split psegs m _ (Dst + n) _ TREST ltac:(lia)) as [TMID _].
  destruct (stk_CB psegs m _ _ TMID ltac:(lia)) as (junk & DC). replace (Dst + n - Dst) with n in DC by lia.
  eapply evt_cut.
  { eapply memcpy_callZ with (src := src) (junk := junk); [exact SRC| exact LEN| exact DC| exact SEP| lia| lia| lia| exact MI]. }
  cbv beta. intros ms' PO. unfold memcpy_postZ in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & -> & MU' & WM' & MI' & DC' & SRC').
  rewrite (ret_pc_even rpc RP0 RP2).
  apply HK.
  split.
  - eapply (SREF_munch_stack E st s m m' OK HR); [| exact WM'].
    eapply munch_weaken; [| exact MU']. intros x Hx. cbn [outside] in Hx |- *. split; [lia| exact I].
  - eapply (SCUR_after E esc spill isobj st m m' _ Dst (Dst + n) OK PURE HC MU' WM' MI'); [| lia | lia | lia | | ].
    + intros a Ha. cbn [outside] in Ha |- *. split; [lia| exact I].
    + pose proof (stk_of_rw_cells psegs _ _ _ DC') as SM. cbn [cells_size csize Nat.add] in SM. rewrite Nat.add_0_r, Z2Nat.id in SM by lia. exact SM.
    + pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
      eapply stk_agree; [exact AG| exact ST|]. intros a Ha. cbn [outside]. split; [lia| exact I].
Qed.

End WithCeiling0.
