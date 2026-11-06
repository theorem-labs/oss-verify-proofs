From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotHeadQ RelayRunT RelayRunF HarnessGlue
  relay_event_b_c check_shape_event_c strnlen_c memcpy_c SlotPass7D SlotMove SlotRI3 SlotNcWt SlotPass7RV.
Import ListNotations.
Local Open Scope Z_scope.

Definition op7_rb_image_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br gn dd ei N G nfd
         (mx nout cap out : word) EL res (nout' cap' out' : word),
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    0 <= EL -> fresh_block (rc := rc) B res (EL + 1) ->
    output_at (rc := rc) B L A mem nout cap out ->
    image_kept (rc := rc) B E mem ->
    globals_at B mem cl br gn dd ei N G nfd mx nout cap out ->
    rw_cells (ms_segs B) mem' G_BROKEN [C1 (Z_to_bv 8 (op7_br cl br dd EL))] ->
    rw_cells (ms_segs B) mem' G_EINTR [C1 (Z_to_bv 8 (op7_ei cl br ei EL))] ->
    rw_cells (ms_segs B) mem' G_OUTV [C8 mx; C8 nout'; C8 cap'; C8 out'] ->
    rw_cells (ms_segs B) mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    image_kept (rc := rc) B E mem'.

Definition op7_rb_stack_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd (nout cap out : word) EL res,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    0 <= EL -> fresh_block (rc := rc) B res (EL + 1) ->
    output_at (rc := rc) B L A mem nout cap out ->
    stack_mid B E mem -> stack_mid B E mem'.

Definition op7_rb_globals_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br gn dd ei N G nfd
         (mx nout cap out : word) EL res (nout' cap' out' ev' : word),
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    0 <= EL -> fresh_block (rc := rc) B res (EL + 1) ->
    output_at (rc := rc) B L A mem nout cap out ->
    globals_at B mem cl br gn dd ei N G nfd mx nout cap out ->
    rw_cells (ms_segs B) mem' G_BROKEN [C1 (Z_to_bv 8 (op7_br cl br dd EL))] ->
    rw_cells (ms_segs B) mem' G_EINTR [C1 (Z_to_bv 8 (op7_ei cl br ei EL))] ->
    rw_cells (ms_segs B) mem' G_OUTV [C8 mx; C8 nout'; C8 cap'; C8 out'] ->
    rw_cells (ms_segs B) mem' (errno_addr B) [C4 ev'] ->
    rw_cells (ms_segs B) mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    globals_at B mem' cl (op7_br cl br dd EL) gn dd (op7_ei cl br ei EL) N G nfd mx nout' cap' out'.

Definition op7_rb_output_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res
         (nout cap out nout' cap' out' : word),
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    0 <= EL ->
    (forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) ->
    output_at (rc := rc) B L A mem nout cap out ->
    (op7_live cl br dd EL = false -> nout' = nout /\ cap' = cap /\ out' = out) ->
    (op7_live cl br dd EL = true ->
       bv_unsigned nout' = EL + 1 /\ EL + 1 <= bv_unsigned cap' <= TBBYTES /\
       In (bv_unsigned out', bv_unsigned cap') (blocks L' A') /\
       fresh_block (rc := rc) B (bv_unsigned out') (bv_unsigned cap') /\
       (exists ob junk, bytes_at (ms_segs B) mem' (bv_unsigned out') (ob ++ junk) /\
          Z.of_nat (length ob) = EL + 1 /\ Z.of_nat (length junk) = bv_unsigned cap' - (EL + 1))) ->
    output_at (rc := rc) B L' A' mem' nout' cap' out'.

Definition op7_rb_driver_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res G es hj
         (nout cap out cap' out' : word),
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md -> WF A ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    0 <= EL -> fresh_block (rc := rc) B res (EL + 1) ->
    (forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) ->
    (forall q m, In (q, m) (blocks L' A') ->
       (In (q, m) (blocks L A) /\ ~ (op7_live cl br dd EL = true /\ q = bv_unsigned out)) \/
       (op7_live cl br dd EL = true /\ q = bv_unsigned out' /\ m = bv_unsigned cap')) ->
    output_at (rc := rc) B L A mem nout cap out ->
    (op7_live cl br dd EL = false -> out' = out) ->
    (op7_live cl br dd EL = true ->
       forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out -> 0 < m -> q <> bv_unsigned out') ->
    driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem ->
    driver_kept B E (target_addrs G (bv_unsigned out') es hj) L' A' mem'.

Definition op7_rb_relay_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res t nfd G es hj
         (nout cap out cap' out' : word),
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md -> WF A ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    0 <= EL -> fresh_block (rc := rc) B res (EL + 1) ->
    (forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) ->
    output_at (rc := rc) B L A mem nout cap out ->
    (op7_live cl br dd EL = false -> out' = out) ->
    (op7_live cl br dd EL = true ->
       forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out -> 0 < m -> q <> bv_unsigned out') ->
    0 <= t ->
    relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj ->
    exists es', relay_at (rc := rc) B L' A' mem' (t + 1) nfd G (bv_unsigned out') es' hj /\
      length es' = length es /\ slot_cost es' hj = slot_cost es hj /\
      target_addrs G (bv_unsigned out') es' hj = target_addrs G (bv_unsigned out') es hj /\
      map entry_nc es' = map entry_nc es /\ nc_wt es' hj = nc_wt es hj.

(* The nc blocks of the view move by the output buffer's move: out (cap bytes) stays, or it is freed (when cap <> 0)
   and (out', cap') is made; the line buffer res is made and freed inside op 7, so it is in neither state. *)
Definition op7_rb_move_stmt : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res t nfd G es es' hj
         (nout cap out cap' out' : word),
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    aa_MR (API rc) L A mem md -> WF A ->
    rmid (rc := rc) B (API rc) OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' ->
    (forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) ->
    (forall q m, In (q, m) (blocks L' A') ->
       (In (q, m) (blocks L A) /\ ~ (op7_live cl br dd EL = true /\ q = bv_unsigned out)) \/
       (op7_live cl br dd EL = true /\ q = bv_unsigned out' /\ m = bv_unsigned cap')) ->
    output_at (rc := rc) B L A mem nout cap out ->
    (op7_live cl br dd EL = false -> cap' = cap /\ out' = out) ->
    (op7_live cl br dd EL = true ->
       EL + 1 <= bv_unsigned cap' <= TBBYTES /\ In (bv_unsigned out', bv_unsigned cap') (blocks L' A') /\
       (forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out -> 0 < m -> q <> bv_unsigned out')) ->
    0 <= EL ->
    relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj ->
    map entry_nc es' = map entry_nc es ->
    nc_move (view_of G (bv_unsigned out) es hj) L A (view_of G (bv_unsigned out') es' hj) L' A'
      (out_move_dels (bv_unsigned out) (bv_unsigned cap) (bv_unsigned out') (bv_unsigned cap'))
      (out_move_adds (bv_unsigned out) (bv_unsigned cap) (bv_unsigned out') (bv_unsigned cap')).

Lemma op7_addr_kept : forall rc B API K sp Ew live out res L A mem md L' A' mem' md',
  WF A -> rmid (rc := rc) B API K sp Ew (op7_F live out res) L A mem md L' A' mem' md' ->
  (forall q m, In (q, m) (blocks L A) -> q <> res) ->
  forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> out \/ live = false -> ptr_addr L' p = ptr_addr L p.
Proof.
  intros rc B API K sp Ew live out res L A mem md L' A' mem' md' HW (_ & _ & _ & _ & _ & PA & SV & ZB & _) RS
    p n Hp Hd.
  assert (NF : ~ op7_F live out res (ptr_addr L p)).
  { intros [X|(LV & X)].
    - apply (RS (ptr_addr L p) n); [apply blocks_In; exists p; split; [reflexivity|exact Hp]|exact X].
    - destruct Hd as [Hd|Hd]; [exact (Hd X)|rewrite LV in Hd; discriminate Hd]. }
  destruct (Z.eq_dec n 0) as [->|Hn].
  - exact (proj2 (ZB p Hp)).
  - pose proof (AllocBound.ub_nonneg A HW (p, n) Hp) as Hn0. cbn [snd] in Hn0.
    exact (PA p n Hp (SV p n Hp ltac:(lia) NF) NF).
Qed.

Lemma op7_rebuild_of : forall RI,
  op7_rb_image_stmt -> op7_rb_stack_stmt -> op7_rb_globals_stmt -> op7_rb_output_stmt ->
  op7_rb_driver_stmt -> op7_rb_relay_stmt -> op7_rb_move_stmt -> op7_rebuild_stmt RI.
Proof.
  intros RI RIMG RSTK RGLB ROUT RDRV RREL RMOV B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md
    cl br gn dd ei G nfd mx nout cap out es hj c' HF HC HP.
  destruct HC as (FZ & Ht & Hk & Hn & HRG & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd &
    HOUT & HREL & Hes & Hcost & HRI).
  destruct HP as (L' & A' & regs' & mem' & md' & K' & EL & res & nout' & cap' & out' & ev' & -> & TR & HK' & HKE & HEL &
    RM & INIT' & RO' & FRB & RSEP & BLK & CBR & CEI & COUTV & CERR & CLOCK & LF & LT & HRI').
  pose proof RM as (M' & W' & B' & _ & _ & _ & _ & _ & _ & MD' & _).
  change (t + (if (0x143b4 =? TAIL_CHECK) || (0x143b4 =? TAIL_STEP) then 1 else 0)) with (t + 0) in HREL.
  rewrite Z.add_0_r in HREL.
  assert (OUTF : op7_live cl br dd EL = false -> out' = out) by (intros X; exact (proj2 (proj2 (LF X)))).
  assert (FRESH : op7_live cl br dd EL = true ->
      forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out -> 0 < m -> q <> bv_unsigned out').
  { intros X. exact (proj2 (proj2 (proj2 (proj2 (proj2 (LT X)))))). }
  destruct (RREL B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res t nfd G es hj
    nout cap out cap' out' HF HMR HWF RM (proj1 HEL) FRB RSEP HOUT OUTF FRESH (proj1 Ht) HREL)
    as (es' & REL' & LEN' & COST' & TA' & ENC' & WT').
  assert (OUTA : output_at (rc := rc) B L' A' mem' nout' cap' out').
  { apply (ROUT B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res
      nout cap out nout' cap' out' HF HMR RM (proj1 HEL) RSEP HOUT LF).
    intros X. destruct (LT X) as (Y1 & Y2 & Y3 & Y4 & Y5 & _).
    exact (conj Y1 (conj Y2 (conj Y3 (conj Y4 Y5)))). }
  assert (ND' : List.NoDup (map fst (blocks L' A'))).
  { pose proof HF as (FF & _).
    assert (ALL : forall rc fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    pose proof (ALL rc fx) as FA.
    assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
    pose proof (NDB L' A' mem' md' M') as X. first [exact X|exact (proj1 (NoDup_ListNoDup _) X)]. }
  exists K'. split; [exact HKE|]. apply MI_MIc.
  exists fx', L', A', regs', mem', md', cl, (op7_br cl br dd EL), gn, dd, (op7_ei cl br ei EL), G, nfd, mx, nout',
    cap', out', es', hj.
  split; [reflexivity|].
  split; [exact FZ|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
  split; [exact TR|].
  split; [exact M'|]. split; [exact W'|]. split; [exact B'|]. split; [exact INIT'|].
  split; [destruct HVM as (vm & ->); destruct MD' as (vm' & ->); exists vm'; apply YI04.with_vmmaps_twice|].
  split; [exact RO'|].
  split; [exact (RIMG B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br gn dd ei
    (Z.of_nat (length es)) G nfd mx nout cap out EL res nout' cap' out' HF HMR RM (proj1 HEL) FRB HOUT HIK HGL
    CBR CEI COUTV CLOCK)|].
  split; [exact (RSTK B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd nout cap out EL res
    HF HMR RM (proj1 HEL) FRB HOUT HST)|].
  split; [rewrite TA'; exact (RDRV B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res
    G es hj nout cap out cap' out' HF HMR HWF RM (proj1 HEL) FRB RSEP BLK HOUT OUTF FRESH HDK)|].
  split; [rewrite LEN'; exact (RGLB B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br gn dd ei
    (Z.of_nat (length es)) G nfd mx nout cap out EL res nout' cap' out' ev' HF HMR RM (proj1 HEL) FRB HOUT HGL
    CBR CEI COUTV CERR CLOCK)|].
  split; [change (0 <= nfd <= t + 1) in Hnfd; change (0 <= nfd <= t + 2); lia|].
  split; [exact OUTA|].
  split; [change (relay_at (rc := rc) B L' A' mem' (t + 1) nfd G (bv_unsigned out') es' hj); exact REL'|].
  split; [rewrite LEN'; exact Hes|].
  split; [rewrite COST'; lia|].
  pose proof HREL as (_ & _ & _ & _ & _ & _ & PA & _).
  assert (LES' : (length es' <= 4)%nat) by (rewrite LEN'; exact Hes).
  apply (HRI' es').
  - exact LES'.
  - rewrite <- (Forall2_length PA). exact Hes.
  - apply (RMOV B API LS SH SK ra empty rc fx j E CS L A mem md L' A' mem' md' cl br dd EL res t nfd G es es' hj
      nout cap out cap' out' HF HMR HWF RM RSEP BLK HOUT); [| |exact (proj1 HEL)|exact HREL|exact ENC'].
    + intros X. destruct (LF X) as (_ & Y2 & Y3). exact (conj Y2 Y3).
    + intros X. destruct (LT X) as (_ & Y2 & Y3 & _ & _ & Y6). exact (conj Y2 (conj Y3 Y6)).
  - intros X. destruct (LF X) as (_ & -> & ->). split; reflexivity.
  - exact (op7_addr_kept rc B (API rc) OP7_K (slot_sp E) _ (op7_live cl br dd EL) (bv_unsigned out) res
      L A mem md L' A' mem' md' HWF RM (fun q m H => proj1 (RSEP q m H))).
  - exact ND'.
  - exact (ncs_le_wt (rc := rc) B (API rc) L' A' mem' md' (t + 1) nfd G nout' cap' out' es' hj M' OUTA REL' LES'
      ND').
  - exact WT'.
Qed.
