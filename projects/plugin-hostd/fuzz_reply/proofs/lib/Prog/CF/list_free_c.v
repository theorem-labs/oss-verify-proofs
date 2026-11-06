From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition LIST_FREE : Z := 0x14b6c.
Definition LIST_FREE_FRAME : Z := 32.
Definition LIST_FREE_K : Z := LIST_FREE_FRAME + ALLOC_STACK.

Section LF.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition list_free_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (l : hlist) (lines : bool),
    let LA := bv_unsigned (getr regs 10) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR LIST_FREE_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr segs (Z_to_bv 64 a) = false) ->
    list_at Bm L A mem LA l lines ->
    rt_ok F A bnd ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_FREE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md',
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API LIST_FREE_K
           (fun a => LA <= a < LA + 16)
           (fun q => In q (list_blocks l))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF (list_free_tr (sh_of (known_at L A) l)) /\ rt_ok F A' (runF F qs bnd (list_free_tr (sh_of (known_at L A) l)))) /\
         ro_agree segs mem' /\
         list_at Bm L' A' mem' LA empty_list lines /\
         (list_blocks l = [] -> blocks L' A' = blocks L A) /\
         (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (list_blocks l))).

End LF.
