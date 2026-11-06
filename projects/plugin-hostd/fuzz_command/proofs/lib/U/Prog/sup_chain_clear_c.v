From Stdlib Require Import ZArith List Bool Lia.
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

Definition SUP_CHAIN_CLEAR : Z := 0x16fc0.
Definition SUP_CHAIN_CLEAR_K : Z := 12432.

Definition sup_chain_clear_sizes (id : Z) (t : list byte) : list Z :=
  [Z.of_nat (length (dec id)) + 1; Z.of_nat (length t) + 1; Z.of_nat (length t) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_chain_clear_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (id : Z) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    sup_chain_clear_m R id = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B MR SUP_CHAIN_CLEAR_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
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
    sb_le (sb_shift b A A') (sb_mallocs b (sup_chain_clear_sizes id t)) /\
    res_ok_slots A' (sb_shift b A A').

Definition sup_chain_clear_contract : Prop :=
  forall L A regs mem md (id : Z) (R : rstate) (O : list (Z * Z)) b,
    call_pre_t B API SUP_CHAIN_CLEAR_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
    Mem.bytes_at segs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b (sup_chain_clear_sizes id (snd (sup_chain_clear_m R id)))) 17 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_CHAIN_CLEAR) mem (seg_rom segs)) md)
      (sup_chain_clear_ret L A regs mem md id R O b).

End K.
