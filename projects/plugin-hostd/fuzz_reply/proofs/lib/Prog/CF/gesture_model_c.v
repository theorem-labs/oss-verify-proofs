From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayRunT RelayRunF RelayModel HarnessRep ListRep CheckRep ListTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import HarnessTr list_push_c list_drop_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition GESTURE_MODEL : Z := 0x1480c.
Definition GESTURE_MODEL_FRAME : Z := 32.
Definition GESTURE_MODEL_K : Z := Z.max LIST_PUSH_K LIST_DROP_K.

Section GM.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition gesture_model_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (h : hsrc) (j : nat) (ln : list byte),
    let HA := G_S + SRC_SIZE * Z.of_nat j in
    let LINE := bv_unsigned (getr regs 11) in
    let LEN := bv_unsigned (getr regs 12) in
    let H := hs_held h in
    let N := hl_n H in
    let CAP := hl_cap H in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR GESTURE_MODEL_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (j < 4)%nat ->
    getr regs 10 = Z_to_bv 64 HA ->
    src_at Bm L A mem HA h ->
    NoDup (texts H) ->
    N < 2 ^ 22 ->
    bytes_at segs mem LINE ln -> ~ In (Z_to_bv 8 0) ln ->
    Z.of_nat (length ln) = LEN -> LEN <= 6000 ->
    (exists q m, In (q, m) (blocks L A) /\ fresh_block Bm q m /\ q <= LINE /\ LINE + LEN <= q + m /\
       ~ In q (list_blocks H)) ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF (gesture_model_tr (sh_of (known_at L A) H) (bzs ln)) -> roomF F qs bnd (gesture_model_tr (sh_of (known_at L A) H) (bzs ln))) ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 GESTURE_MODEL) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (H' : hlist),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API GESTURE_MODEL_K
           (fun a => HA + 80 <= a < HA + 96 \/ (0 < CAP /\ hl_v H <= a < hl_v H + 16 * CAP))
           (fun q => In q (list_blocks H))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF (gesture_model_tr (sh_of (known_at L A) H) (bzs ln)) /\ rt_ok F A' (runF F qs bnd (gesture_model_tr (sh_of (known_at L A) H) (bzs ln))) /\ sh_real L' qs (gesture_model_sh 0 (sh_of (known_at L A) H) (bzs ln)) H' /\ sh_live A' qs (gesture_model_sh 0 (sh_of (known_at L A) H) (bzs ln))) /\
         ro_agree segs mem' /\
         src_at Bm L' A' mem' HA (set_held h H') /\
         NoDup (texts H') /\
         texts H' = upd (texts H) (bzs ln) /\
         bytes_at segs mem' LINE ln /\
         (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks H) -> In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L' A') ->
            (In (q, m) (blocks L A) /\ (0 < m -> ~ In q (list_blocks H))) \/ In q (list_blocks H')) /\
         (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks H) -> ~ In q (list_blocks H')) /\
         ((H' = H /\ L' = L /\ A' = A) \/
          (exists x d, gesture (bzs ln) = Some (GBegin, bzs x) /\ ~ In (bzs x) (texts H) /\
             hl_recs H' = hl_recs H ++ [(d, x)] /\ hl_cap H' = grow_cap N CAP /\ (N < CAP -> hl_v H' = hl_v H)) \/
          (exists i, (i < length (hl_recs H))%nat /\
             gesture (bzs ln) = Some (GEnd, nth i (texts H) []) /\
             hl_recs H' = drop_nth i (hl_recs H) /\ hl_v H' = hl_v H /\ hl_cap H' = CAP /\
             (exists b1 b2, blocks L A = b1 ++ (fst (nth i (hl_recs H) (0, [])), text_len (nth i (hl_recs H) (0, []))) :: b2 /\
                blocks L' A' = b1 ++ b2)))).

End GM.
