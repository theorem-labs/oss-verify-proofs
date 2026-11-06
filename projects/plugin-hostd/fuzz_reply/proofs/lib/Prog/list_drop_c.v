From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep ListTr TrModel.
Import ListNotations.
Local Open Scope Z_scope.

Definition LIST_DROP : Z := 0x14684.
Definition LIST_DROP_FRAME : Z := 32.
Definition LIST_DROP_K : Z := LIST_DROP_FRAME + ALLOC_STACK.

Section LD.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition list_drop_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (l : hlist) (lines : bool),
    let LA := bv_unsigned (getr regs 10) in
    let i := bv_unsigned (getr regs 11) in
    let N := hl_n l in
    let V := hl_v l in
    let r := nth (Z.to_nat i) (hl_recs l) (0, []) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR LIST_DROP_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr segs (Z_to_bv 64 a) = false) ->
    list_at Bm L A mem LA l lines ->
    i < N ->
    rt_ok F A bnd ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_DROP) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (l' : hlist),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API LIST_DROP_K
           (fun a => LA + 8 <= a < LA + 12 \/ V + 16 * i <= a < V + 16 * (N - 1))
           (fun q => q = fst r)
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF (list_drop_tr (sh_of (known_at L A) l) (Z.to_nat i)) /\ rt_ok F A' (runF F qs bnd (list_drop_tr (sh_of (known_at L A) l) (Z.to_nat i))) /\ sh_real L' qs (list_drop_sh (sh_of (known_at L A) l) (Z.to_nat i)) l' /\ sh_live A' qs (list_drop_sh (sh_of (known_at L A) l) (Z.to_nat i))) /\
         ro_agree segs mem' /\
         list_at Bm L' A' mem' LA l' lines /\
         hl_v l' = V /\ hl_cap l' = hl_cap l /\
         hl_recs l' = firstn (Z.to_nat i) (hl_recs l) ++ skipn (S (Z.to_nat i)) (hl_recs l) /\
         hl_junk l' = text_rec (last (hl_recs l) (0, [])) ++ hl_junk l /\
         (exists b1 b2, blocks L A = b1 ++ (fst r, text_len r) :: b2 /\ blocks L' A' = b1 ++ b2)).

End LD.
