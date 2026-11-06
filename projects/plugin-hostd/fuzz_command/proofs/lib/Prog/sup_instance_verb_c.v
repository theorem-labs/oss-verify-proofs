From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInvP RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require rec_shape_of_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_INSTANCE_VERB : Z := 0x16330.
Definition SUP_INSTANCE_VERB_K : Z := 12384.

Definition sup_instance_verb_sizes (line : list byte) (ledger : Z) (t : list byte) : list Z :=
  [Z.of_nat (length line) + 1; Z.of_nat (length (dec ledger)) + 1; Z.of_nat (length t) + 1; Z.of_nat (length t) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_instance_verb_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (line : list byte) (ledger : Z) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    sup_instance_verb_m R line ledger = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    fp_kept fx fx' /\
    call_post_rec B MR SUP_INSTANCE_VERB_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
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
    sb_le (sb_shift b A A') (sb_mallocs b (sup_instance_verb_sizes line ledger t)) /\
    res_ok_slots A' (sb_shift b A A').

Definition sup_instance_verb_contract : Prop :=
  forall L A regs mem md (pl ledger : Z) (line : list byte) (R : rstate) (O : list (Z * Z)) b,
    call_pre_t B API SUP_INSTANCE_VERB_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 pl ->
    getr regs 11 = Z_to_bv 64 ledger -> -2 ^ 31 <= ledger < 2 ^ 31 ->
    str_arg B L A O (spZ regs) SUP_INSTANCE_VERB_K mem pl (Some line) ->
    Mem.bytes_at segs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_mallocs b (sup_instance_verb_sizes line ledger (snd (sup_instance_verb_m R line ledger))))
      (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_INSTANCE_VERB) mem (seg_rom segs)) md)
      (sup_instance_verb_ret L A regs mem md line ledger R O b).

End K.
