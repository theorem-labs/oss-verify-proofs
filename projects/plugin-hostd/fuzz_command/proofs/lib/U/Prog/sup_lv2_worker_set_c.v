From Stdlib Require Import String ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_LV2_WORKER_SET : Z := 0x16d24.
Definition SUP_LV2_WORKER_SET_K : Z := 12384.

Definition sup_lv2_worker_set_sizes (uri worker : option (list byte)) (t : list byte) : list Z :=
  [Z.of_nat (length (sarg uri)) + 1; Z.of_nat (length (sarg worker)) + 1; Z.of_nat (length t) + 1;
   Z.of_nat (length t) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_lv2_worker_set_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (uri worker : option (list byte))
    (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    sup_lv2_worker_set_m R uri worker = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B MR SUP_LV2_WORKER_SET_K L A regs mem md rec_area (fun a => In a (map fst O))
      L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep segs L' A' mem' R' O' /\ owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at segs mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept segs L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    Mem.bytes_at segs mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
    ro_agree segs mem' /\ f18_words segs mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (sup_lv2_worker_set_sizes uri worker t)) /\
    res_ok_slots A' (sb_shift b A A').

Definition sup_lv2_worker_set_contract : Prop :=
  forall L A regs mem md (pu pw : Z) (uri worker : option (list byte)) (R : rstate) (O : list (Z * Z)) b,
    call_pre_t B API SUP_LV2_WORKER_SET_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pu -> getr regs 11 = Z_to_bv 64 pw ->
    str_arg B L A O (spZ regs) SUP_LV2_WORKER_SET_K mem pu uri ->
    str_arg B L A O (spZ regs) SUP_LV2_WORKER_SET_K mem pw worker ->
    Mem.bytes_at segs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b (sup_lv2_worker_set_sizes uri worker (snd (sup_lv2_worker_set_m R uri worker))))
      (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_LV2_WORKER_SET) mem (seg_rom segs)) md)
      (sup_lv2_worker_set_ret L A regs mem md uri worker R O b).

End K.
