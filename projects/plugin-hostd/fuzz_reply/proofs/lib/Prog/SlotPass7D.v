From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import Statement StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import send_line_c gesture_end_c relay_event_c
  RelayFrame RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c
  RelayRep HarnessRep ListRep CheckRep drain_b_c source_reset_c op_add_c check_bounded_c SlotInv SlotSteps SlotHead
  SlotHeadP SlotRes KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadQ RelayRunT RelayRunF HarnessGlue
  relay_event_b_c check_shape_event_c strnlen_c memcpy_c SlotWalk SlotMove SlotRI3 SlotPass7RV.
Import ListNotations.
Local Open Scope Z_scope.

Definition OP7_K : Z := RELAY_EVENT_K.

Definition op7_live (cl br dd EL : Z) : bool := send_live cl br dd (EL + 1).
Definition op7_br (cl br dd EL : Z) : Z := if send_off cl br (EL + 1) then br else dd.
Definition op7_ei (cl br ei EL : Z) : Z := if send_off cl br (EL + 1) then ei else 0.

Definition op7_E (live : bool) (OUT CAP res EL : Z) (a : Z) : Prop :=
  (res <= a < res + EL + 1) \/ event_writes live OUT CAP a.

Definition op7_F (live : bool) (OUT res : Z) (q : Z) : Prop := q = res \/ (live = true /\ q = OUT).

Definition RG7 (E : sstart) (t K s : Z) : list rentry -> list (hsrc * nat) -> Z -> bvmap 5 word -> Prop :=
  fun _ hj no regs => no = 0 /\ disp_src 7 s hj /\ disp_regs E t K s regs.

Section D7.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable E : sstart.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition MIc (RI : res_inv) (t k pc : Z)
    (RG : list rentry -> list (hsrc * nat) -> Z -> bvmap 5 word -> Prop)
    (fx' : FPState) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat)) : Prop :=
    frm_zero (@fp_csr fx') /\
    0 <= t < OPS_MAX /\ 0 <= k <= ss_n E /\ ss_n E < INPUT_MAX /\
    RG es hj (bv_unsigned nout) regs /\
    MR L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
    (exists vm, md = with_vmmaps vm (ss_md E)) /\
    ro_agree segs mem /\
    image_kept (rc := rc) B E mem /\
    stack_mid B E mem /\
    driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem /\
    globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out /\
    0 <= nfd <= t + (if (pc =? TAIL_CHECK) || (pc =? TAIL_STEP) then 2 else 1) /\
    output_at (rc := rc) B L A mem nout cap out /\
    relay_at (rc := rc) B L A mem (t + (if (pc =? TAIL_CHECK) || (pc =? TAIL_STEP) then 1 else 0)) nfd G
      (bv_unsigned out) es hj /\
    (length es <= 4)%nat /\
    slot_cost es hj <= k /\
    RI E k (view_of G (bv_unsigned out) es hj) L A.

Lemma MI_MIc : forall RI t k pc RG c,
  MI (rc := rc) B API E RI t k pc RG c <->
  exists fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj,
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md /\
    MIc RI t k pc RG fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj.
Proof. intros. unfold MI, MIc. reflexivity. Qed.

Definition op7_post (RI : res_inv) (t K : Z) (fx' : FPState)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (cl br dd ei G : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat)) (c' : config) : Prop :=
  exists (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
         (K' EL res : Z) (nout' cap' out' ev' : word),
    c' = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 TAIL_CHECK) mem' (seg_rom segs)) md' /\
    tail_regs E t K' regs' /\ K <= K' <= ss_n E /\ K' = take_end E K /\ 0 <= EL <= K' - K /\
    rmid (rc := rc) B API OP7_K (slot_sp E)
      (op7_E (op7_live cl br dd EL) (bv_unsigned out) (bv_unsigned cap) res EL)
      (op7_F (op7_live cl br dd EL) (bv_unsigned out) res) L A mem md L' A' mem' md' /\
    st_init_done A' = true /\ ro_agree segs mem' /\
    fresh_block (rc := rc) B res (EL + 1) /\
    (forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1)) /\
    (forall q m, In (q, m) (blocks L' A') ->
       (In (q, m) (blocks L A) /\ ~ (op7_live cl br dd EL = true /\ q = bv_unsigned out)) \/
       (op7_live cl br dd EL = true /\ q = bv_unsigned out' /\ m = bv_unsigned cap')) /\
    rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (op7_br cl br dd EL))] /\
    rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (op7_ei cl br ei EL))] /\
    rw_cells segs mem' G_OUTV [C8 mx; C8 nout'; C8 cap'; C8 out'] /\
    rw_cells segs mem' (errno_addr B) [C4 ev'] /\
    rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    (op7_live cl br dd EL = false -> nout' = nout /\ cap' = cap /\ out' = out) /\
    (op7_live cl br dd EL = true ->
       bv_unsigned nout' = EL + 1 /\ EL + 1 <= bv_unsigned cap' <= TBBYTES /\
       In (bv_unsigned out', bv_unsigned cap') (blocks L' A') /\
       fresh_block (rc := rc) B (bv_unsigned out') (bv_unsigned cap') /\
       (exists ob junk, bytes_at segs mem' (bv_unsigned out') (ob ++ junk) /\
          Z.of_nat (length ob) = EL + 1 /\ Z.of_nat (length junk) = bv_unsigned cap' - (EL + 1)) /\
       (forall q m, In (q, m) (blocks L A) -> q <> bv_unsigned out -> 0 < m -> q <> bv_unsigned out')) /\
    op7_RV_s RI E K' L A G (bv_unsigned out) es hj (bv_unsigned cap) (bv_unsigned cap') (op7_live cl br dd EL)
      (bv_unsigned out') L' A'.

End D7.

Definition op7_chain_stmt (F : ResFormT) (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    (forall fx0 : FPState, @malloc_contract_rt fx0 rc B (API rc) F) ->
    (forall fx0 : FPState, @free_contract_rt fx0 rc B (API rc) F) ->
    (forall fx0 : FPState, @relay_event_contract fx0 rc B (API rc) F) ->
    1 <= K ->
    MIc (rc := rc) B (API rc) E RI t K 0x13dc0 (RG7 E t K s)
      fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj ->
    SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x13dc0) mem (seg_rom (ms_segs B))) md)
      (op7_post (rc := rc) B (API rc) E RI t K fx' L A mem md cl br dd ei G mx nout cap out es hj).

Definition op7_rebuild_stmt (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj c',
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    MIc (rc := rc) B (API rc) E RI t K 0x13dc0 (RG7 E t K s)
      fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj ->
    op7_post (rc := rc) B (API rc) E RI t K fx' L A mem md cl br dd ei G mx nout cap out es hj c' ->
    exists K', K' = take_end E K /\ MI (rc := rc) B (API rc) E RI t K' TAIL_CHECK (fun _ _ _ r => tail_regs E t K' r) c'.

Lemma MI_op7 : forall F RI B API LS SH SK ra empty rc fx j E CS t K s c,
  op7_chain_stmt F RI -> op7_rebuild_stmt RI ->
  slot_frame B API LS SH SK ra empty rc fx j E CS -> check_bounded_contract ->
  (forall fx0 : FPState, @malloc_contract_rt fx0 rc B (API rc) F) ->
  (forall fx0 : FPState, @free_contract_rt fx0 rc B (API rc) F) ->
  (forall fx0 : FPState, @relay_event_contract fx0 rc B (API rc) F) ->
  1 <= K -> walk_at (ss_pl E) (t + 1) (take_end E K) ->
  MI (rc := rc) B (API rc) E RI t K 0x13dc0 (RG7 E t K s) c ->
  SR (ms_segs B) c (fun c' => exists k', LI (rc := rc) B (API rc) E RI (t + 1) k' c').
Proof.
  intros F RI B API LS SH SK ra empty rc fx j E CS t K s c HCH HRB HF CB HMA HFR HRE HK1 HW HM.
  apply MI_MIc in HM.
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & HC).
  eapply SR_bind; [exact (HCH B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx
    nout cap out es hj HF HMA HFR HRE HK1 HC)|].
  intros c' HP.
  destruct (HRB B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out
    es hj c' HF HC HP) as (K' & HKE & HT).
  eapply SR_mono; [eapply (MI_tail B API LS SH SK ra empty rc fx j E CS RI t K' (fun _ _ _ r => tail_regs E t K' r));
    [exact HF|exact CB|intros; assumption|rewrite HKE; exact HW|exact HT]|].
  intros c'' HL. exists K'. exact HL.
Qed.

Lemma pass7_of : forall F RI,
  op7_chain_stmt F RI -> op7_rebuild_stmt RI -> RI_mono RI -> check_bounded_contract ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @malloc_contract_rt fx rc B (API rc) F /\ @free_contract_rt fx rc B (API rc) F /\
     @relay_event_contract fx rc B (API rc) F) ->
  pass_ok RI 7.
Proof.
  intros F RI HCH HRB RIM CB HCT B API LS SH SK ra empty rc fx j E CS HF t k c HL Ht Hk Hop. cbv beta in Hop.
  assert (HK0 : 0 <= k).
  { destruct HL as (fx1 & L1 & A1 & regs1 & mem1 & md1 & cl1 & br1 & gn1 & dd1 & ei1 & G1 & nfd1 & mx1 & nout1 &
      cap1 & out1 & es1 & hj1 & _ & _ & _ & HK0' & _). lia. }
  eapply SR_bind; [exact (LI_dispatch B API LS SH SK ra empty rc fx j E CS RI t k c HF RIM HL Ht Hk)|].
  intros c' [(s & HM)|(k'' & HL')]; [|apply SR_ret; exists k''; exact HL'].
  rewrite Hop in HM. change (jt_target 7) with 0x13dc0 in HM.
  assert (FF : frame_facts B API LS SH SK ra empty) by exact (proj1 HF).
  apply (MI_op7 F RI B API LS SH SK ra empty rc fx j E CS t (disp_k E 7 k) s c' HCH HRB HF CB
    (fun fx0 => proj1 (HCT B API LS SH SK ra empty rc fx0 FF))
    (fun fx0 => proj1 (proj2 (HCT B API LS SH SK ra empty rc fx0 FF)))
    (fun fx0 => proj2 (proj2 (HCT B API LS SH SK ra empty rc fx0 FF)))).
  - unfold disp_k. replace (pick_op 7) with false by reflexivity. cbn [andb]. lia.
  - exact (walk_op7 E t k (LI_walk _ _ _ _ _ _ _ _ HL) (frame_len B API LS SH SK ra empty rc fx j E CS HF) Hk Hop).
  - exact HM.
Qed.
