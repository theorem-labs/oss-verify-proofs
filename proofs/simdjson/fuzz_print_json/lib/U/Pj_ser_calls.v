(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel PjModel Target Prog PjImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjAlloc SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit F_memcpy F_memmove_t2 Pj_defs Pj_kit Pj_copy Pj_grow Pj_stmts Pj_ser_defs Pj_ser_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ser_req_ok : forall E e64 e72 e80 spill isobj st s m need, senv_ok E -> SERM E e64 e72 e80 spill isobj st s m ->
  sb_cap st < need -> need <= PJ_OUTMAX (e_len E) -> chain_ok (e_len E) (sb_cap st) (Z.max (2 * sb_cap st) need) = true.
Proof.
  intros E e64 e72 e80 spill isobj st s m need OK HM H1 H2.
  eapply grow_request_ok; [destruct OK; lia| eapply SBINV_of_SERM; exact HM| exact H1| exact H2].
Qed.
Lemma ser_req_ok2 : forall E e64 e72 e80 spill isobj st s m, senv_ok E -> SERM E e64 e72 e80 spill isobj st s m ->
  sb_cap st < PJ_OUTMAX (e_len E) -> chain_ok (e_len E) (sb_cap st) (2 * sb_cap st) = true.
Proof.
  intros E e64 e72 e80 spill isobj st s m OK HM H1.
  eapply grow_request_ok2; [destruct OK; lia| eapply SBINV_of_SERM; exact HM| exact H1].
Qed.

Definition refW (E : senv) (st : sbst) : list (Z * Z) :=
  [(e_lo E, e_q E); (sb_buf st, sb_buf st + sb_cap st); (e_SB E + 64, e_SB E + 88)].

Lemma refW_out_block : forall E st s m a, senv_ok E -> SREF E st s m -> in_block (e_LB0 E) a -> outside (refW E st) a.
Proof.
  intros E st s m a OK (HEAP & _ & _ & _ & _ & _ & _ & _ & _ & PURE) HB.
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  assert (BL : 0 < a < alloc_ceiling).
  { eapply blocks_below; [exact HEAP|]. destruct HB as (b & Hb & Hr). exists b. split; [apply in_or_app; right; exact Hb| exact Hr]. }
  destruct OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold PJ_GROW_STACK, RMALLOC_STACK in *.
  unfold refW. cbn [outside]. split; [lia|]. split; [| split; [lia| exact I]].
  destruct PURE as (_ & _ & PB). unfold sbblocks in HEAP. destruct (sb_blk st) as [b|].
  - cbn [app] in HEAP. pose proof (LH_head_disj _ _ _ _ _ _ HEAP a HB). lia.
  - destruct PB as (EB & EC & _). lia.
Qed.

Lemma SREF_frame : forall E st s m m' W size, senv_ok E -> SREF E st s m ->
  munch W m m' -> wmono usegs m m' -> (forall a, outside (refW E st) a -> outside W a) ->
  SREF E (sb_resize st size) s m'.
Proof.
  intros E st s m m' W size OK HR MU0 WM SUB.
  assert (MU : munch (refW E st) m m') by (eapply munch_weaken; [exact SUB| exact MU0]). clear MU0 SUB.
  pose proof HR as (HEAP & AUX & PRES & TAPEB & SBUFB & DOCC & (errv & ERR) & FA & SO & PURE).
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  pose proof OK as [_ _ _ _ OKT OKS _ [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  assert (OUTHI : forall a, e_q E <= a -> ~ (e_SB E <= a < e_SB E + 88) -> outside (refW E st) a).
  { intros a Ha Hn. unfold refW. cbn [outside]. split; [lia|]. split; [| split; [lia| exact I]].
    destruct PURE as (_ & _ & PB).
    destruct (sb_blk st) as [b|];
      [destruct PB as (A0 & A16 & N0 & AC & AS); unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in AC; lia
      | destruct PB as (EB & EC & _); lia]. }
  assert (OUTIM : forall a, 0x10000 <= a < 0x110000 -> outside (refW E st) a).
  { intros a Ha. unfold refW. cbn [outside]. split; [lia|]. split; [lia| split; [lia| exact I]]. }
  unfold SREF. rewrite sbblocks_resize.
  split.
  { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. unfold refW.
    constructor; [apply W_ok_stack; cbn; lia|]. constructor; [| constructor; [apply W_ok_stack; cbn; lia| constructor]].
    destruct PURE as (_ & _ & PB). unfold sbblocks. destruct (sb_blk st) as [b|].
    - eapply (W_ok_block _ (b, sb_buf st, sb_cap st)); [left; reflexivity| cbn; lia| cbn; lia].
    - destruct PB as (EB & EC & _). apply W_ok_stack. cbn. lia. }
  split.
  { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold refW.
    constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia|]. constructor; [cbn; unfold RAUXV_CELL; lia| constructor]. }
  split.
  { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    intros a Ha [HX HC]. cbn [rin_ivs fst snd] in HX.
    destruct HC as [HC|[HC|HC]].
    - apply OUTHI; lia.
    - eapply refW_out_block; eassumption.
    - apply OUTIM. lia. }
  split.
  { eapply bytes_at_agree; [exact AG| exact TAPEB|]. intros a Ha. rewrite u64s_length, length_map in Ha.
    eapply refW_out_block; [exact OK| exact HR|]. eapply in_blocks_in_block; [exact OKT| lia]. }
  split.
  { eapply bytes_at_agree; [exact AG| exact SBUFB|]. intros a Ha. rewrite length_map in Ha.
    eapply refW_out_block; [exact OK| exact HR|]. eapply in_blocks_in_block; [exact OKS| lia]. }
  split.
  { eapply rw_cells_agree; [exact AG| exact DOCC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUTHI; lia. }
  split.
  { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
    apply OUTIM. unfold LX_ERRNO, RATP in Ha. lia. }
  split; [exact FA|]. split; [exact SO|]. apply sb_pure_resize. exact PURE.
Qed.

Lemma SREF_munch_stack : forall E st s m m', senv_ok E -> SREF E st s m ->
  munch [(e_lo E, e_q E)] m m' -> wmono usegs m m' -> SREF E st s m'.
Proof.
  intros E st s m m' OK HR MU WM. replace st with (sb_resize st (sb_size st)) by (destruct st; reflexivity).
  eapply SREF_frame; [exact OK| exact HR| exact MU| exact WM|].
  intros a Ha. unfold refW in Ha. cbn [outside] in Ha |- *. split; [lia| exact I].
Qed.

Lemma SCUR_after : forall E e64 e72 e80 spill isobj st m m' W TL TH,
  senv_ok E -> sb_pure E st -> SCUR E e64 e72 e80 spill isobj st m ->
  munch W m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  (forall a, outside [(e_lo E, e_q E + -256); (TL, TH)] a -> outside W a) ->
  e_q E + -144 <= TL -> TL <= TH -> TH <= e_q E + -104 ->
  stk usegs m' TL TH -> stk usegs m' (e_lo E) (e_q E + -256) ->
  SCUR E e64 e72 e80 spill isobj st m'.
Proof.
  intros E e64 e72 e80 spill isobj st m m' W TL TH OK PURE HC MU WM MI' SUB T1 T2 T3 STT ST'.
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (OUT : forall a, (e_q E + -256 <= a < TL \/ TH <= a) \/ a < e_lo E -> outside W a).
  { intros a Ha. apply SUB. cbn [outside]. split; [lia|]. split; [lia| exact I]. }
  destruct (stk_split usegs m _ TL _ FRT ltac:(lia)) as [TLO TREST].
  destruct (stk_split usegs m _ TH _ TREST ltac:(lia)) as [_ THI].
  unfold SCUR. split.
  { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add ser_consts length] in Ha. apply OUT. lia. }
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

Lemma SCUR_after_buf : forall E e64 e72 e80 spill isobj st m m' W XL XH,
  senv_ok E -> sb_pure E st -> SCUR E e64 e72 e80 spill isobj st m ->
  munch W m m' -> wmono usegs m m' -> mem_inv usegs m' ->
  (forall a, outside [(e_lo E, e_q E + -256); (XL, XH)] a -> outside W a) ->
  sb_buf st <= XL -> XL <= XH -> XH <= sb_buf st + sb_cap st ->
  stk usegs m' XL XH -> stk usegs m' (e_lo E) (e_q E + -256) ->
  SCUR E e64 e72 e80 spill isobj st m'.
Proof.
  intros E e64 e72 e80 spill isobj st m m' W XL XH OK PURE HC MU WM MI' SUB T1 T2 T3 STT ST'.
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
  assert (OUT : forall a, (e_q E + -256 <= a \/ sb_buf st <= a < sb_buf st + sb_cap st) -> (a < XL \/ XH <= a) -> outside W a).
  { intros a Ha Hb. apply SUB. cbn [outside]. split; [lia|]. split; [lia| exact I]. }
  destruct (stk_split usegs m _ XL _ BUFS ltac:(lia)) as [BLO BREST].
  destruct (stk_split usegs m _ XH _ BREST ltac:(lia)) as [_ BHI].
  assert (BUFS' : stk usegs m' (sb_buf st) (sb_buf st + sb_cap st)).
  { eapply stk_merge; [eapply stk_agree; [exact AG| exact BLO| intros a Ha; apply OUT; lia]| | lia].
    eapply stk_merge; [exact STT| eapply stk_agree; [exact AG| exact BHI| intros a Ha; apply OUT; lia]| lia]. }
  unfold SCUR. split.
  { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add ser_consts length] in Ha. apply OUT; lia. }
  split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply OUT; lia. }
  split; [exact FRIL|].
  split. { eapply stk_agree; [exact AG| exact FRT|]. intros a Ha. apply OUT; lia. }
  split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT; lia. }
  split. { eapply rw_cells_agree; [exact AG| exact SV|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT; lia. }
  split; [exact SZ|]. split; [exact BUFS'|].
  split. { destruct PURE as (_ & _ & PB). destruct (sb_blk st) as [b|].
           - destruct PB as (A0 & A16 & N0 & AC & AS). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in AC.
             eapply stk_agree; [exact AG| exact INLS|]. intros a Ha. apply OUT; lia.
           - destruct PB as (EB & EC & _). rewrite EB, EC in BUFS'. exact BUFS'. }
  split; [exact MI'| exact ST'].
Qed.

Lemma ser_copy : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (Src n rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  senv_ok E -> SERM E e64 e72 e80 spill isobj st s m ->
  (exists src, bytes_at usegs m Src src /\ length src = Z.to_nat n) ->
  0 <= n -> sb_size st + n <= sb_cap st -> 0 <= Src -> Src + n < 2^63 ->
  (Src + n <= sb_buf st + sb_size st \/ sb_buf st + sb_size st + n <= Src) ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E e64 e72 e80 spill isobj st s m' ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 (sb_buf st + sb_size st)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
  evt usegs (sgoal E Q (sb_ch st) s)
      (SST E PJ_MEMCPY (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (sb_buf st + sb_size st)) (Z_to_bv 64 Src) (Z_to_bv 64 n) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros E Q e64 e72 e80 spill isobj st s m Src n rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         OK HSM (src & SRC & LEN) N0 ROOM S0 S63 SEP RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  set (Dst := sb_buf st + sb_size st) in *.
  destruct (stk_split usegs m _ Dst _ BUFS ltac:(unfold Dst; lia)) as [_ BREST].
  destruct (stk_split usegs m _ (Dst + n) _ BREST ltac:(unfold Dst; lia)) as [BMID _].
  destruct (stk_CB usegs m _ _ BMID ltac:(lia)) as (junk & DC). replace (Dst + n - Dst) with n in DC by lia.
  unfold PJ_MEMCPY. eapply evt_cut.
  { eapply memcpy_callZ with (src := src) (junk := junk); [exact SRC| exact LEN| exact DC| fold Dst in SEP; exact SEP| lia| lia| unfold Dst; lia| exact MI]. }
  cbv beta. intros ms' PO. unfold memcpy_postZ in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & -> & MU' & WM' & MI' & DC' & SRC').
  rewrite (ret_pc_even rpc RP0 RP2).
  apply HK. split.
  - replace st with (sb_resize st (sb_size st)) by (destruct st; reflexivity).
    eapply SREF_frame; [exact OK| exact HR| exact MU'| exact WM'|].
    intros a Ha. unfold refW in Ha. cbn [outside] in Ha |- *. split; [unfold Dst; lia| exact I].
  - eapply (SCUR_after_buf E e64 e72 e80 spill isobj st m m' _ Dst (Dst + n) OK PURE HC MU' WM' MI'); [| unfold Dst; lia| lia| unfold Dst; lia| |].
    + intros a Ha. cbn [outside] in Ha |- *. split; [lia| exact I].
    + pose proof (stk_of_rw_cells usegs _ _ _ DC') as SM. cbn [cells_size csize Nat.add] in SM. rewrite Nat.add_0_r, Z2Nat.id in SM by lia. exact SM.
    + eapply stk_agree; [eapply agree_on_of_munch; [exact MU'| exact WM']| exact ST|]. intros a Ha. cbn [outside]. split; [unfold Dst; lia| exact I].
Qed.

Lemma ser_copyh : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
       (st : sbst) (s : PState) (m : mem) (Src n rpc : Z) (F : bvmap 5 word) (fc : bv 32)
       (t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  senv_ok E -> SERM E e64 e72 e80 spill isobj st s m ->
  (exists src, bytes_at usegs m Src src /\ length src = Z.to_nat n) ->
  0 <= n -> sb_size st + n <= sb_cap st -> 0 < Src -> Src + n < 2^63 ->
  (Src + n <= sb_buf st + sb_size st \/ sb_buf st + sb_size st + n <= Src) ->
  (Src + n <= e_lo E \/ e_q E + -256 <= Src) ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      SERM E e64 e72 e80 spill isobj st s m' ->
      evt usegs (sgoal E Q (sb_ch st) s)
          (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 (Z_to_bv 64 (Src + n)) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
  evt usegs (sgoal E Q (sb_ch st) s)
      (SST E PJ_COPY_S (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 Src) (Z_to_bv 64 (Src + n)) (Z_to_bv 64 (sb_buf st + sb_size st)) a3 a4 a5 a6 a7
           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
Proof.
  intros E Q e64 e72 e80 spill isobj st s m Src n rpc F fc t0 t1 t2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         OK HSM (src & SRC & LEN) N0 ROOM S0 S63 SEP SLO RP0 RP2 HK.
  pose proof HSM as [HR HC].
  pose proof HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PURE).
  pose proof (sb_pure_ranges E st OK PURE) as (R0 & R1 & R2 & R3 & R4).
  pose proof HC as ((j0 & FRA) & FRI & FRIL & FRT & FRS & SV & SZ & BUFS & INLS & MI & ST).
  pose proof OK as [_ _ _ _ _ _ _ [L1 L2] [Q1 Q2] B63 [S1 S2] _ _ _ _ _]. unfold GLOBALS_TOP, PJ_GROW_STACK, RMALLOC_STACK in *.
  assert (BPOS : 0 < sb_buf st).
  { destruct PURE as (_ & _ & PB). destruct (sb_blk st) as [b|]; [destruct PB as (A0 & _); exact A0| destruct PB as (EB & _); rewrite EB; lia]. }
  set (Dst := sb_buf st + sb_size st) in *.
  destruct (stk_split usegs m _ Dst _ BUFS ltac:(unfold Dst; lia)) as [_ BREST].
  destruct (stk_split usegs m _ (Dst + n) _ BREST ltac:(unfold Dst; lia)) as [BMID _].
  destruct (stk_CB usegs m _ _ BMID ltac:(lia)) as (junk & DC). replace (Dst + n - Dst) with n in DC by lia.
  eapply evt_cut.
  { eapply (copy_spec PJ_COPY_S) with (lo := e_lo E) (src := src) (junk := junk);
      [right; reflexivity| exact ST| unfold PJ_COPY_STACK; lia| unfold GLOBALS_TOP; lia| lia| exact MI
      | exact SRC| exact LEN| exact DC| fold Dst in SEP; exact SEP| lia| lia| lia| unfold Dst; lia| unfold Dst; lia| lia| unfold Dst; lia]. }
  cbv beta. intros ms' PO. unfold copy_post in PO.
  destruct PO as (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & -> & MU' & WM' & MI' & ST' & DC' & SRC').
  rewrite (ret_pc_even rpc RP0 RP2).
  apply HK. split.
  - replace st with (sb_resize st (sb_size st)) by (destruct st; reflexivity).
    eapply SREF_frame; [exact OK| exact HR| exact MU'| exact WM'|].
    intros a Ha. unfold refW in Ha. cbn [outside] in Ha |- *. split; [lia|]. split; [unfold Dst; lia| exact I].
  - eapply (SCUR_after_buf E e64 e72 e80 spill isobj st m m' _ Dst (Dst + n) OK PURE HC MU' WM' MI'); [| unfold Dst; lia| lia| unfold Dst; lia| | exact ST'].
    + intros a Ha. cbn [outside] in Ha |- *. split; [lia|]. split; [lia| exact I].
    + pose proof (stk_of_rw_cells usegs _ _ _ DC') as SM. cbn [cells_size csize Nat.add] in SM. rewrite Nat.add_0_r, Z2Nat.id in SM by lia. exact SM.
Qed.

Lemma sbuf_src : forall E e64 e72 e80 spill isobj st s m o n, senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> 0 <= o -> 0 <= n -> o + n <= e_sn E ->
  exists src, bytes_at usegs m (e_SBUF E + o) src /\ length src = Z.to_nat n.
Proof.
  intros E e64 e72 e80 spill isobj st s m o n OK [HR _] Ho Hn Hb.
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

Lemma frt_src : forall E e64 e72 e80 spill isobj st s m Src n, SERM E e64 e72 e80 spill isobj st s m ->
  e_q E + -144 <= Src -> 0 <= n -> Src + n <= e_q E + -104 ->
  exists src, bytes_at usegs m Src src /\ length src = Z.to_nat n.
Proof.
  intros E e64 e72 e80 spill isobj st s m Src n [_ HC] H1 Hn H2.
  destruct HC as (_ & _ & _ & FRT & _).
  destruct (stk_split usegs m _ Src _ FRT ltac:(lia)) as [_ S1].
  destruct (stk_split usegs m _ (Src + n) _ S1 ltac:(lia)) as [S2 _].
  destruct (stk_bytes usegs m _ _ S2 ltac:(lia)) as (bs & HL & HB).
  exists bs. split; [exact HB|]. rewrite HL. f_equal. lia.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma ser_grow : forall (E : senv) (Q : @chst bptr -> PState -> machine_state -> Prop) (e64 e72 e80 spill : word) (isobj : list byte)
         (st : sbst) (s : PState) (m : mem) (z rpc : Z) (F : bvmap 5 word) (fc : bv 32)
         (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    senv_ok E -> SERM E e64 e72 e80 spill isobj st s m -> chain_ok (e_len E) (sb_cap st) z = true ->
    0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
    (forall (s' : PState) (m' : mem) (b : bptr) (NEW : Z) (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
        SERM E e64 e72 e80 spill isobj (sb_grown st b NEW z) s' m' ->
        evt usegs (sgoal E Q (sb_ch (sb_grown st b NEW z)) s')
            (SST E rpc (Z_to_bv 64 rpc) xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m')) ->
    evt usegs (sgoal E Q (sb_ch st) s)
        (SST E PJ_GROW (Z_to_bv 64 rpc) t0 t1 t2 (Z_to_bv 64 (e_SB E)) (Z_to_bv 64 z) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof.
    intros E Q e64 e72 e80 spill isobj st s m z rpc F fc t0 t1 t2 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK HSM OKZ RP0 RP2 HK.
    pose proof (SBINV_of_SERM _ _ _ _ _ _ _ _ _ HSM) as INV.
    pose proof OK as [_ _ _ _ OKT OKS HLEN [L1 L2] [Q1 Q2] B63 [S1 S2] [D1 D2] SEP _ _ _].
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
    assert (HSM' : SERM E e64 e72 e80 spill isobj (sb_grown (mkSb buf size cap blk (S f)) b NEW z) s' m').
    { pose proof (agree_of_lx_pres _ _ _ _ _ PRES') as AG.
      assert (UP : forall a, e_q E + -256 <= a -> ~ (e_SB E + 64 <= a < e_SB E + 88) -> lx_client (e_LB0 E) (e_q E + -256) [(e_SB E + 64, e_SB E + 88)] a).
      { intros a Ha Hn. split; [cbn [rin_ivs fst snd]; tauto| left; exact Ha]. }
      assert (BL : forall a, in_block (e_LB0 E) a -> lx_client (e_LB0 E) (e_q E + -256) [(e_SB E + 64, e_SB E + 88)] a).
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
        { exists j0. eapply rw_cells_agree; [exact AG| exact FRA|]. intros a Ha. cbn [cells_size csize Nat.add ser_consts length] in Ha. apply UP; lia. }
        split. { eapply u8arr_agree; [exact AG| exact FRI|]. intros a Ha. rewrite FRIL in Ha. apply UP; lia. }
        split; [exact FRIL|].
        split. { eapply stk_agree; [exact AG| exact FRT|]. intros a Ha. apply UP; lia. }
        split. { eapply rw_cells_agree; [exact AG| exact FRS|]. intros a Ha. unfold ser_saved in Ha. cbn [cells_size csize Nat.add] in Ha. apply UP; lia. }
        split; [exact SV'|]. split; [exact SZ'|].
        split. { pose proof (stk_of_rw_cells usegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S.
                 pose proof (SBINV_cap_pos _ _ _ _ INV') as CP. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S. }
        split. { pose proof (stk_of_rw_cells usegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S. }
        split; [exact MI'|]. exact ST'. }
    unfold implM. apply impl_from_evt.
    change (evt usegs (sgoal E Q (sb_ch (sb_grown (mkSb buf size cap blk (S f)) b NEW z)) s')
              (SST E rpc (Z_to_bv 64 rpc) r5 r6 r7 r10 r11 r12 r13 r14 r15 r16 r17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31 F fc m')).
    apply HK. exact HSM'.
  Qed.

End Proofs.
End WithCeiling0.
