From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep CheckRep ListTr HarnessTr TrModel.
Import ListNotations.
Local Open Scope Z_scope.

Definition SOURCE_RESET : Z := 0x145fc.
Definition SOURCE_RESET_FRAME : Z := 16.
Definition SOURCE_RESET_K : Z := SOURCE_RESET_FRAME + 32 + ALLOC_STACK.

Section SRS.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition source_reset_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (h : hsrc) (j : nat),
    let HA := G_S + SRC_SIZE * Z.of_nat j in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR SOURCE_RESET_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (j < 4)%nat ->
    getr regs 10 = Z_to_bv 64 HA ->
    src_at Bm L A mem HA h \/ rw_cells segs mem HA [CB 96%nat (nulbytes 96)] ->
    (exists pad, rw_cells segs mem (HA + 60) [CB 4%nat pad]) ->
    rt_ok F A bnd ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 SOURCE_RESET) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API SOURCE_RESET_K
           (fun a => HA <= a < HA + SRC_SIZE)
           (fun q => src_at Bm L A mem HA h /\ In q (hs_blocks h))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         ro_agree segs mem' /\
         rw_cells segs mem' HA [CB 96%nat (nulbytes 96)] /\
         (src_at Bm L A mem HA h ->
            (exists qs, length qs = nretF (source_reset_tr (known_at L A) h) /\ rt_ok F A' (runF F qs bnd (source_reset_tr (known_at L A) h))) /\
            (forall q m, In (q, m) (blocks L A) -> ~ In q (hs_blocks h) -> In (q, m) (blocks L' A')) /\
            (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (hs_blocks h))) /\
         (rw_cells segs mem HA [CB 96%nat (nulbytes 96)] ->
            rt_ok F A' bnd /\ blocks L' A' = blocks L A)).

End SRS.
