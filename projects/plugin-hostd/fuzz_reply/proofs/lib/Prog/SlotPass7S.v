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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import SlotHeadQ RelayRunT RelayRunF TrModel
  HarnessGlue relay_event_b_c check_shape_event_c strnlen_c memcpy_c SlotPass7D SlotWalk SlotPass7RV.
Import ListNotations.
Local Open Scope Z_scope.

Lemma op7_sptr_none : forall L A a, (forall m, ~ In (a, m) (blocks L A)) -> sptr_of L A a = SP 0 0.
Proof.
  intros L A a N. unfold sptr_of.
  destruct (find (fun pb => ptr_addr L (fst pb) =? a) (user_blocks A)) as [[q m]|] eqn:Hf; [|reflexivity].
  exfalso. apply find_some in Hf as [Hq Hqa]. cbn [fst] in Hqa. apply Z.eqb_eq in Hqa.
  apply (N m). rewrite <- Hqa. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ (q, m) Hq).
Qed.

Lemma op7_known_keep : forall (L L1 : layout) (A A1 : astate) (a : Z),
  stdpp.base.NoDup (map fst (blocks L A)) -> stdpp.base.NoDup (map fst (blocks L1 A1)) ->
  (forall p n, In (p, n) (user_blocks A) -> 0 < n -> In (p, n) (user_blocks A1)) ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1) -> ptr_addr L1 p = ptr_addr L p) ->
  (exists n, 0 < n /\ In (a, n) (blocks L A)) \/
    ((forall m, ~ In (a, m) (blocks L A)) /\ (forall m, ~ In (a, m) (blocks L1 A1))) ->
  known_at L1 A1 a = known_at L A a.
Proof.
  intros L L1 A A1 a ND ND1 SV PA [(n & Hn & Hin)|(N0 & N1)]; unfold known_at; f_equal.
  - destruct (sptr_of_spec L A a n ND Hin) as (Hp & Ea).
    pose proof (SV _ _ Hp Hn) as Hp1. pose proof (PA _ _ Hp Hp1) as E1.
    transitivity (sptr_of L1 A1 (ptr_addr L1 (sptr_of L A a))).
    + rewrite E1, Ea. reflexivity.
    + exact (sptr_of_eq L1 A1 _ n ND1 Hp1).
  - rewrite (op7_sptr_none L1 A1 a N1), (op7_sptr_none L A a N0). reflexivity.
Qed.

Definition op7_rsep (L : layout) (A : astate) (res EL : Z) : Prop :=
  forall q m, In (q, m) (blocks L A) -> q <> res /\ forall i, 0 <= i < m -> ~ (res <= q + i < res + EL + 1).

Definition op7_regs1 (E : sstart) (t : Z) (R : bvmap 5 word) : Prop :=
  base_regs E R /\ getr R 21 = Z_to_bv 64 DIV10 /\ getr R 22 = Z_to_bv 64 t /\
  getr R 24 = Z_to_bv 64 (slot_sp E + 16) /\ getr R 25 = Z_to_bv 64 4 /\
  getr R 26 = Z_to_bv 64 (G_S + 4) /\ getr R 27 = Z_to_bv 64 (G_S + SRC_SIZE * SOURCES_MAX + 4).

Definition op7_P1 {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (F : ResFormT) (RI : res_inv)
    (fx' : FPState) (t K : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (cl br dd G : Z) (mx cap out : word) (es : list rentry) (hj : list (hsrc * nat)) (c : config) : Prop :=
  exists (L1 : layout) (A1 : astate) (R1 : bvmap 5 word) (m1 : word -> option byte) (md1 : Model)
         (K0 M EL res : Z) (e : list byte),
    c = mkCfg (@YK11.mkst fx' R1 (Z_to_bv 64 0x1408c) m1 (seg_rom (ms_segs B))) md1 /\
    op7_regs1 E t R1 /\
    getr R1 8 = Z_to_bv 64 (ss_p E + K0) /\ getr R1 18 = Z_to_bv 64 M /\ getr R1 19 = Z_to_bv 64 EL /\
    getr R1 23 = Z_to_bv 64 (ss_n E - K0) /\ getr R1 10 = Z_to_bv 64 res /\
    K <= K0 /\ 0 <= M /\ K0 + M <= ss_n E /\ K0 + M = take_end E K /\ 0 <= EL <= M /\
    Z.of_nat (length e) = EL /\ ~ In (Z_to_bv 8 0) e /\ bytes_at (ms_segs B) m1 (ss_p E + K0) e /\
    rmid (rc := rc) B API OP7_K (slot_sp E) (fun _ => False) (fun _ => False) L A mem md L1 A1 m1 md1 /\
    st_init_done A1 = true /\ ro_agree (ms_segs B) m1 /\
    res <> 0 /\ res mod 16 = 0 /\ fresh_block (rc := rc) B res (EL + 1) /\
    (exists b1 b2, blocks L1 A1 = b1 ++ (res, EL + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
    op7_rsep L A res EL /\
    res_tr F (op7_S2 F RI E (K0 + M) L A EL G (bv_unsigned out) es hj (bv_unsigned cap)
      (send_line_cap (op7_live cl br dd EL) (bv_unsigned mx) 0 (bv_unsigned cap) (EL + 1)) (op7_live cl br dd EL)
      (relay_event_out (op7_live cl br dd EL) (bv_unsigned mx) 0 (bv_unsigned cap) EL 0
        (known_at L A (bv_unsigned out)))) A1
      (relay_event_tr (op7_live cl br dd EL) (bv_unsigned mx) 0 (bv_unsigned cap) EL 0 (known_at L A (bv_unsigned out))).

Definition op7_P2 {rc : RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (F : ResFormT) (RI : res_inv)
    (fx' : FPState) (t K : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (cl br dd ei G : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat)) (c : config) : Prop :=
  exists (L2 : layout) (A2 : astate) (R2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model)
         (K0 M EL res : Z) (e : list byte) (nout' cap' out' ev' : word),
    let live := op7_live cl br dd EL in
    let OUT := bv_unsigned out in
    let oa := relay_event_out live (bv_unsigned mx) 0 (bv_unsigned cap) EL 0 (known_at L A OUT) in
    c = mkCfg (@YK11.mkst fx' R2 (Z_to_bv 64 0x140b8) m2 (seg_rom (ms_segs B))) md2 /\
    op7_regs1 E t R2 /\
    getr R2 8 = Z_to_bv 64 (ss_p E + K0) /\ getr R2 18 = Z_to_bv 64 (ss_p E + (K0 + M)) /\
    getr R2 9 = Z_to_bv 64 res /\ getr R2 23 = Z_to_bv 64 (ss_n E - (K0 + M)) /\
    K <= K0 /\ 0 <= M /\ K0 + M <= ss_n E /\ K0 + M = take_end E K /\ 0 <= EL <= M /\
    Z.of_nat (length e) = EL /\ ~ In (Z_to_bv 8 0) e /\ bytes_at (ms_segs B) m2 res (e ++ [Z_to_bv 8 0]) /\
    rmid (rc := rc) B API OP7_K (slot_sp E) (op7_E live OUT (bv_unsigned cap) res EL)
      (fun q => live = true /\ q = OUT) L A mem md L2 A2 m2 md2 /\
    st_init_done A2 = true /\ ro_agree (ms_segs B) m2 /\
    res <> 0 /\ res mod 16 = 0 /\ fresh_block (rc := rc) B res (EL + 1) /\ In (res, EL + 1) (blocks L2 A2) /\
    op7_rsep L A res EL /\
    (forall q m, In (q, m) (blocks L2 A2) ->
       (In (q, m) (blocks L A) /\ ~ (live = true /\ q = OUT)) \/ (q = res /\ m = EL + 1) \/
       (live = true /\ q = bv_unsigned out' /\ m = bv_unsigned cap')) /\
    rw_cells (ms_segs B) m2 G_BROKEN [C1 (Z_to_bv 8 (op7_br cl br dd EL))] /\
    rw_cells (ms_segs B) m2 G_EINTR [C1 (Z_to_bv 8 (op7_ei cl br ei EL))] /\
    rw_cells (ms_segs B) m2 G_OUTV [C8 mx; C8 nout'; C8 cap'; C8 out'] /\
    rw_cells (ms_segs B) m2 (errno_addr B) [C4 ev'] /\
    rw_cells (ms_segs B) m2 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    (live = false -> nout' = nout /\ cap' = cap /\ out' = out) /\
    (live = true ->
       bv_unsigned nout' = EL + 1 /\ EL + 1 <= bv_unsigned cap' <= TBBYTES /\
       In (bv_unsigned out', bv_unsigned cap') (blocks L2 A2) /\
       fresh_block (rc := rc) B (bv_unsigned out') (bv_unsigned cap') /\ bv_unsigned out' <> res /\
       (exists junk, bytes_at (ms_segs B) m2 (bv_unsigned out') (e ++ [Z_to_bv 8 0] ++ junk) /\
          Z.of_nat (length junk) = bv_unsigned cap' - (EL + 1)) /\
       (forall q m, In (q, m) (blocks L A) -> q <> OUT -> 0 < m -> q <> bv_unsigned out')) /\
    exists qr, (live = true -> live_at L2 A2 (resolveF qr oa) (bv_unsigned out') (bv_unsigned cap')) /\
      forall p, res_tr F (op7_S3 RI E (K0 + M) L A G OUT es hj (bv_unsigned cap) (bv_unsigned cap') live oa qr) A2
        [RFree (EL + 1) (Known p)].

Definition op7_c1_stmt (F : ResFormT) (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    strnlen_contract ->
    (forall fx0 : FPState, @malloc_contract_rt fx0 rc B (API rc) F) ->
    op7_res_s F RI -> 1 <= K ->
    MIc (rc := rc) B (API rc) E RI t K 0x13dc0 (RG7 E t K s)
      fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj ->
    SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x13dc0) mem (seg_rom (ms_segs B))) md)
      (op7_P1 (rc := rc) B (API rc) E F RI fx' t K L A mem md cl br dd G mx cap out es hj).

Definition op7_c2_stmt (F : ResFormT) (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj c,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    memcpy_contract ->
    (forall fx0 : FPState, @relay_event_contract fx0 rc B (API rc) F) ->
    MIc (rc := rc) B (API rc) E RI t K 0x13dc0 (RG7 E t K s)
      fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj ->
    op7_P1 (rc := rc) B (API rc) E F RI fx' t K L A mem md cl br dd G mx cap out es hj c ->
    SR (ms_segs B) c (op7_P2 (rc := rc) B (API rc) E F RI fx' t K L A mem md cl br dd ei G mx nout cap out es hj).

Definition op7_c3_stmt (F : ResFormT) (RI : res_inv) : Prop :=
  forall B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj c,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    check_shape_event_contract ->
    (forall fx0 : FPState, @free_contract_rt fx0 rc B (API rc) F) ->
    MIc (rc := rc) B (API rc) E RI t K 0x13dc0 (RG7 E t K s)
      fx' L A regs mem md cl br gn dd ei G nfd mx nout cap out es hj ->
    op7_P2 (rc := rc) B (API rc) E F RI fx' t K L A mem md cl br dd ei G mx nout cap out es hj c ->
    SR (ms_segs B) c (op7_post (rc := rc) B (API rc) E RI t K fx' L A mem md cl br dd ei G mx nout cap out es hj).

Lemma op7_chain_of : forall F RI,
  strnlen_contract -> memcpy_contract -> check_shape_event_contract -> op7_res_s F RI ->
  op7_c1_stmt F RI -> op7_c2_stmt F RI -> op7_c3_stmt F RI -> op7_chain_stmt F RI.
Proof.
  intros F RI SN MC CK HR C1 C2 C3 B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G
    nfd mx nout cap out es hj HF HMA HFR HRE HK HC.
  eapply SR_bind; [exact (C1 B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx
    nout cap out es hj HF SN HMA HR HK HC)|].
  intros c1 H1.
  eapply SR_bind; [exact (C2 B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx
    nout cap out es hj c1 HF MC HRE HC H1)|].
  intros c2 H2.
  exact (C3 B API LS SH SK ra empty rc fx j E CS t K s fx' L A regs mem md cl br gn dd ei G nfd mx
    nout cap out es hj c2 HF CK HFR HC H2).
Qed.
