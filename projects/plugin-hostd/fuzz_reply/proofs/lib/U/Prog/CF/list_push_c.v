From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep ListTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition LIST_PUSH : Z := 0x1484c.
Definition LIST_PUSH_FRAME : Z := 48.
Definition LIST_PUSH_K : Z := LIST_PUSH_FRAME + REALLOC_STACK.

Section LP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition list_push_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (l : hlist) (lines : bool) (x : list byte),
    let LA := bv_unsigned (getr regs 10) in
    let SRC := bv_unsigned (getr regs 11) in
    let n := bv_unsigned (getr regs 12) in
    let N := hl_n l in
    let CAP := hl_cap l in
    let V := hl_v l in
    let G := grow_cap N CAP in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR LIST_PUSH_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr segs (Z_to_bv 64 a) = false) ->
    LA mod 8 = 0 ->
    list_at Bm L A mem LA l lines ->
    (N = CAP -> CAP < 2 ^ 29) ->
    n < 2 ^ 64 - 1 ->
    bytes_at segs mem SRC x -> Z.of_nat (length x) = n ->
    src_home Bm L A (spZ regs) SRC n V ->
    (SRC + n <= LA \/ LA + 16 <= SRC) ->
    (lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= 6000) ->
    (lines = false -> 1 <= n) ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) -> roomF F qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_PUSH) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (l' : hlist) (d : Z),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API LIST_PUSH_K
           (fun a => LA <= a < LA + 16 \/ (N < CAP /\ V + 16 * N <= a < V + 16 * (N + 1)))
           (fun q => N = CAP /\ 0 < CAP /\ q = V)
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) /\ rt_ok F A' (runF F qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) /\ sh_real L' qs (list_push_sh 0 (sh_of (known_at L A) l) (bzs x)) l' /\ sh_live A' qs (list_push_sh 0 (sh_of (known_at L A) l) (bzs x))) /\
         ro_agree segs mem' /\
         list_at Bm L' A' mem' LA l' lines /\
         hl_recs l' = hl_recs l ++ [(d, x)] /\
         hl_cap l' = G /\
         (N < CAP -> hl_v l' = V) /\
         (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ (0 < m -> ~ In q (list_blocks l))) \/ In q (list_blocks l')) /\
         (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks l) -> ~ In q (list_blocks l'))).

End LP.
