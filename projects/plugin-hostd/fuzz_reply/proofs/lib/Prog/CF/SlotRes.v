From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack
  AllocPack AllocPack3 SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept SlotInv SlotSteps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition res_tr (F : ResFormT) (P : layout -> astate -> list sptr -> Prop) (A : astate) (tr : trF) : Prop :=
  exists bnd, rt_ok F A bnd /\ (forall qs, length qs = nretF tr -> roomF F qs bnd tr) /\
    (forall L' A' qs, length qs = nretF tr -> rt_ok F A' (runF F qs bnd tr) -> P L' A' qs).

Definition RI_start (RI : res_inv) (CS : list byte -> list Z) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall C G CAP OUT, ss_T E = kept_blocks C G CAP OUT -> (C = 0 /\ G = 0) \/ C = 16 -> 0 <= CAP <= TBBYTES ->
      (CAP = 0 -> OUT = 0) -> RI E 0 (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E).

Definition RI_end (RI : res_inv) (CS : list byte -> list Z) : Prop :=
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall k V L A T', RI E k V L A -> List.NoDup (map fst (blocks L A)) ->
      (forall t, In t (blocks L A) -> (In t (blocks (ss_L E) (ss_A E)) /\ ~ In t (ss_T E)) \/ In t T') ->
      (length T' <= 2)%nat -> (forall t, In t T' -> 0 < snd t <= TBBYTES) ->
      res_ok_pack3 A (PB3 (pb_live (TDP (ss_T E) T' (pb_of3 (ss_b E)))) (pb_bytes (TDP (ss_T E) T' (pb_of3 (ss_b E))))
        (CS (ss_pl E)) [] frame_MCAP) /\ AllocPackGSF.GSF A.

Definition RI_mono (RI : res_inv) : Prop :=
  forall E k k' V L A, RI E k V L A -> k <= k' <= ss_n E -> RI E k' V L A.
