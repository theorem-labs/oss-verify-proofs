From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF RelayModel HarnessRep ListRep CheckRep ListTr HarnessTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import next_line_c list_drop_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
Import ListNotations.
Local Open Scope Z_scope.

Definition CHECK_SHAPE_ENDS : Z := 0x14a78.
Definition CHECK_SHAPE_ENDS_FRAME : Z := 112.
Definition CHECK_SHAPE_ENDS_K : Z := CHECK_SHAPE_ENDS_FRAME + LIST_DROP_K.
Definition G_GONE : Z := 0x318a8.
Definition G_S : Z := 0x31920.

Section CE.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Let segs := ms_segs Bm.
Let MR := aa_MR API.

Definition check_shape_ends_contract : Prop :=
  forall L A regs mem md (bnd : rt_R F) (h : hsrc) (j : nat) (gone A0 : Z) (nout out : word)
         (ob P slack : list byte),
    let HA := G_S + SRC_SIZE * Z.of_nat j in
    let PF := bv_unsigned (getr regs 11) in
    let AT := bv_unsigned (getr regs 12) in
    let PLEN := Z.of_nat (length P + 1 + length slack) in
    let NO := bv_unsigned nout in
    let OUT := bv_unsigned out in
    let H := hs_held h in
    let W := want_of P (hl_recs H) in
    ms_segs Bm = rsegs ->
    call_pre_k Bm MR CHECK_SHAPE_ENDS_K L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    (forall a, G_GONE <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) ->
    (j < 4)%nat ->
    getr regs 10 = Z_to_bv 64 HA ->
    src_at Bm L A mem HA h ->
    NoDup (texts H) ->
    hl_n H < 2 ^ 26 ->
    bytes_at segs mem PF (P ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) P ->
    (- (PF + Z.of_nat (length P) + 1)) mod 8 <= Z.of_nat (length slack) ->
    ((spZ regs <= PF /\ PF + PLEN <= 2 ^ 63) \/
     (0 <= PF /\ PF + PLEN <= 2 ^ 64 /\ forall i, 0 <= i < PLEN -> ro_addr segs (Z_to_bv 64 (PF + i)) = true)) ->
    AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= 2 ^ 63 -> (AT + 8 <= PF \/ PF + PLEN <= AT) ->
    rw_cells segs mem AT [C8 (Z_to_bv 64 A0)] ->
    0 <= gone < 256 ->
    bytes_at segs mem G_GONE [Z_to_bv 8 gone] ->
    bytes_at segs mem G_NOUT (le8 nout) ->
    bytes_at segs mem G_OUT (le8 out) ->
    bytes_at segs mem OUT ob -> Z.of_nat (length ob) = NO ->
    (ob = [] \/
     exists CO, NO <= CO /\ In (OUT, CO) (blocks L A) /\ fresh_block Bm OUT CO /\ ~ In OUT (hs_blocks h)) ->
    0 <= A0 <= NO ->
    (gone = 0 -> ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) W <> None) ->
    rt_ok F A bnd ->
    SR segs (mkCfg (YK11.mkst regs (Z_to_bv 64 CHECK_SHAPE_ENDS) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (H' : hlist) (ds : list (Z * list byte)) (c : Z),
         c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         relay_post Bm API CHECK_SHAPE_ENDS_K
           (fun a => HA + 88 <= a < HA + 92 \/ AT <= a < AT + 8 \/
                     (0 < hl_cap H /\ hl_v H <= a < hl_v H + 16 * hl_cap H))
           (fun q => In q (map fst (hl_recs H)))
           L A regs mem md L' A' regs' mem' md' /\
         st_init_done A' = true /\
         (exists qs, length qs = nretF (check_shape_ends_tr (known_at L A) gone P (hl_recs H) (skipn (Z.to_nat A0) ob)) /\ rt_ok F A' (runF F qs bnd (check_shape_ends_tr (known_at L A) gone P (hl_recs H) (skipn (Z.to_nat A0) ob)))) /\
         ro_agree segs mem' /\
         src_at Bm L' A' mem' HA (set_held h H') /\
         hl_v H' = hl_v H /\ hl_cap H' = hl_cap H /\
         NoDup (texts H') /\
         ((gone <> 0 /\ hl_recs H' = filter (fun r => negb (prefixb P (snd r))) (hl_recs H) /\
           ds = filter (fun r => prefixb P (snd r)) (hl_recs H) /\ c = 0) \/
          (gone = 0 /\ ends_run P (hl_recs H) (skipn (Z.to_nat A0) ob) W = Some (hl_recs H', ds, c))) /\
         rw_cells segs mem' AT [C8 (Z_to_bv 64 (A0 + c))] /\
         bytes_at segs mem' PF (P ++ Z_to_bv 8 0 :: slack) /\
         bytes_at segs mem' G_GONE [Z_to_bv 8 gone] /\
         bytes_at segs mem' G_NOUT (le8 nout) /\
         bytes_at segs mem' G_OUT (le8 out) /\
         bytes_at segs mem' OUT ob /\
         (forall q m, In (q, m) (blocks L A) -> ~ In q (map fst ds) -> In (q, m) (blocks L' A')) /\
         (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (map fst ds))).

End CE.
