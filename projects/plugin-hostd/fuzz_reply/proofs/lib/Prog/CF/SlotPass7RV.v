From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YO0g.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT SlotKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotInv SlotSteps SlotRes SlotMove SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import send_line_b_c relay_event_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition op7_RV_s (RI : res_inv) (E : sstart) (K : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (CAP CAP' : Z) (live : bool) (out' : Z) (L' : layout) (A' : astate) : Prop :=
  forall es',
    (length es' <= 4)%nat -> (length hj <= 4)%nat ->
    nc_move (view_of G out es hj) L A (view_of G out' es' hj) L' A' (out_move_dels out CAP out' CAP')
      (out_move_adds out CAP out' CAP') ->
    (live = false -> out' = out /\ CAP' = CAP) ->
    (forall p n, In (p, n) (user_blocks A) -> ptr_addr L p <> out \/ live = false -> ptr_addr L' p = ptr_addr L p) ->
    List.NoDup (map fst (blocks L' A')) ->
    ncs (view_of G out' es' hj) L' A' <= nc_wt es' hj -> nc_wt es' hj = nc_wt es hj ->
    RI E K (view_of G out' es' hj) L' A'.

Definition op7_S3 (RI : res_inv) (E : sstart) (K : Z) (L : layout) (A : astate) (G out : Z) (es : list rentry)
    (hj : list (hsrc * nat)) (CAP CAP' : Z) (live : bool) (oa : adrF) (qr : list sptr)
    (L' : layout) (A' : astate) (qf : list sptr) : Prop :=
  forall out', (live = true -> live_at L' A' (resolveF qr oa) out' CAP') ->
    op7_RV_s RI E K L A G out es hj CAP CAP' live out' L' A'.

Definition op7_S2 (F : ResFormT) (RI : res_inv) (E : sstart) (K : Z) (L : layout) (A : astate) (EL G out : Z)
    (es : list rentry) (hj : list (hsrc * nat)) (CAP CAP' : Z) (live : bool) (oa : adrF)
    (L2 : layout) (A2 : astate) (qr : list sptr) : Prop :=
  forall p, res_tr F (op7_S3 RI E K L A G out es hj CAP CAP' live oa qr) A2 [RFree (EL + 1) (Known p)].

Definition op7_S1 (F : ResFormT) (RI : res_inv) (E : sstart) (K : Z) (L : layout) (A : astate) (EL : Z) (live : bool)
    (mx CAP G out : Z) (es : list rentry) (hj : list (hsrc * nat)) (L1 : layout) (A1 : astate) (qm : list sptr) : Prop :=
  res_tr F (op7_S2 F RI E K L A EL G out es hj CAP (send_line_cap live mx 0 CAP (EL + 1)) live
      (relay_event_out live mx 0 CAP EL 0 (known_at L A out)))
    A1 (relay_event_tr live mx 0 CAP EL 0 (known_at L A out)).

Definition op7_res_s (F : ResFormT) (RI : res_inv) : Prop :=
  forall E K K' L A EL live mx CAP G out es hj,
    RI E K (view_of G out es hj) L A -> 1 <= K -> K <= K' <= ss_n E -> ss_n E < INPUT_MAX -> 0 <= EL <= K' - K ->
    0 <= mx <= 255 -> 0 <= CAP <= TBBYTES ->
    List.NoDup (map fst (blocks L A)) -> (0 < CAP -> In (out, CAP) (blocks L A)) ->
    (CAP = 0 -> forall m, ~ In (out, m) (blocks L A)) ->
    res_tr F (op7_S1 F RI E K' L A EL live mx CAP G out es hj) A [RMalloc (EL + 1)].
