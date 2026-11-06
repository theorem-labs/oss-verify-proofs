From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF RelayModel HarnessRep ListRep CheckRep ListTr HarnessTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import next_line_c list_push_c list_drop_c
  gesture_model_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_NO_LOSS : Z := 0x14f0c.
Definition CHECK_NO_LOSS_FRAME : Z := 80.
Definition CHECK_NO_LOSS_K : Z := CHECK_NO_LOSS_FRAME + GESTURE_MODEL_K.
Definition G_GONE : Z := 0x318a8.

Section CN.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition check_no_loss_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (h : hsrc) (j : nat) (gone A0 : Z) (nout out : word) (ob : list byte),
    let HA := G_S + SRC_SIZE * Z.of_nat j in
    let AT := bv_unsigned (getr regs 11) in
    let NO := bv_unsigned nout in
    let OUT := bv_unsigned out in
    let E := hs_expected h in
    let H := hs_held h in
    let BE := count_begin (texts E) in
    let LB := Z.of_nat (length (bstream E)) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR CHECK_NO_LOSS_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, G_GONE <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (j < 4)%nat ->
    getr regs 10 = Z_to_bv 64 HA ->
    src_at Bm L A mem HA h ->
    NoDup (texts H) ->
    hl_n E < 2 ^ 26 ->
    hl_n H + Z.of_nat BE < 2 ^ 22 ->
    AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= 2 ^ 63 ->
    rw_cells segs mem AT [C8 (Z_to_bv 64 A0)] ->
    0 <= gone < 256 ->
    bytes_at segs mem G_GONE [Z_to_bv 8 gone] ->
    bytes_at segs mem G_NOUT (le8 nout) ->
    bytes_at segs mem G_OUT (le8 out) ->
    bytes_at segs mem OUT ob -> Z.of_nat (length ob) = NO ->
    (ob = [] \/
     exists CO, NO <= CO /\ In (OUT, CO) (blocks L A) /\ fresh_block Bm OUT CO /\ ~ In OUT (hs_blocks h)) ->
    0 <= A0 <= NO ->
    (gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream E ++ rest) ->
    rt_ok F A bnd ->
    (forall qs, length qs = nretF (check_no_loss_tr 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E))) -> roomF F qs bnd (check_no_loss_tr 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E)))) ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 CHECK_NO_LOSS) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (E' H' : hlist),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API CHECK_NO_LOSS_K
           (fun a => HA + 64 <= a < HA + 96 \/ AT <= a < AT + 8 \/
                     (0 < hl_cap E /\ hl_v E <= a < hl_v E + 16 * hl_cap E) \/
                     (0 < hl_cap H /\ hl_v H <= a < hl_v H + 16 * hl_cap H))
           (fun q => In q (map fst (hl_recs E) ++ list_blocks H))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF (check_no_loss_tr 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E))) /\ rt_ok F A' (runF F qs bnd (check_no_loss_tr 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E)))) /\ sh_real L' qs (check_no_loss_sh 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E))) H' /\ sh_live A' qs (check_no_loss_sh 0 (sh_of (known_at L A) H) (map (shr (known_at L A)) (hl_recs E)))) /\
         ro_agree segs mem' /\
         src_at Bm L' A' mem' HA (set_exp_held h E' H') /\
         hl_recs E' = [] /\ hl_v E' = hl_v E /\ hl_cap E' = hl_cap E /\
         NoDup (texts H') /\
         hl_cap H' <= Z.max 8 (Z.max (hl_cap H) (2 * (hl_n H + Z.of_nat BE))) /\
         texts H' = upds (texts H) (texts E) /\
         rw_cells segs mem' AT [C8 (Z_to_bv 64 (if gone =? 0 then A0 + LB else A0))] /\
         bytes_at segs mem' G_GONE [Z_to_bv 8 gone] /\
         bytes_at segs mem' G_NOUT (le8 nout) /\
         bytes_at segs mem' G_OUT (le8 out) /\
         bytes_at segs mem' OUT ob /\
         (forall q m, In (q, m) (blocks L A) -> ~ In q (map fst (hl_recs E) ++ list_blocks H) ->
            In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L' A') ->
            (In (q, m) (blocks L A) /\ (0 < m -> ~ In q (map fst (hl_recs E) ++ list_blocks H))) \/
            In q (list_blocks H')) /\
         (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (map fst (hl_recs E) ++ list_blocks H) ->
            ~ In q (list_blocks H'))).

End CN.
