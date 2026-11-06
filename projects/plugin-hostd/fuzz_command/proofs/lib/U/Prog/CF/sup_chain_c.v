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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition SUP_CHAIN : Z := 0x16e1c.
Definition SUP_CHAIN_K : Z := 12512.

Definition sup_chain_sizes (id : Z) (ids : list Z) (t : list byte) : list Z :=
  [12 * Z.of_nat (length ids) + 1; Z.of_nat (length (dec id)) + 1; Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
   Z.of_nat (length (dec_list ids)) + 1; Z.of_nat (length t) + 1; Z.of_nat (length t) + 1].

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition sup_chain_contract : Prop :=
  forall L A regs mem md (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)) b,
    call_pre_t B API SUP_CHAIN_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 id -> -2 ^ 31 <= id < 2 ^ 31 ->
    getr regs 11 = Z_to_bv 64 pids -> getr regs 12 = Z_to_bv 64 (Z.of_nat (length ids)) ->
    (1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
    pids <> 0 -> pids mod 4 = 0 ->
    Mem.bytes_at segs mem pids (concat (map le32 ids)) ->
    (pids + 4 * Z.of_nat (length ids) <= spZ regs - SUP_CHAIN_K \/ spZ regs <= pids) ->
    ((spZ regs <= pids /\ pids + 4 * Z.of_nat (length ids) <= TASK_SIZE) \/
     (exists q k, In (q, k) (blocks L A) /\ ~ In q (map fst O) /\ q <= pids /\
        pids + 4 * Z.of_nat (length ids) <= q + k) \/
     (0 <= pids /\ pids + 4 * Z.of_nat (length ids) <= 2 ^ 64 /\
        forall i, 0 <= i < 4 * Z.of_nat (length ids) -> Mem.ro_addr segs (Z_to_bv 64 (pids + i)) = true)) ->
    (forall a, pids <= a < pids + 4 * Z.of_nat (length ids) -> ~ rec_area a) ->
    Mem.bytes_at segs mem rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes ->
    g_rec_rep segs L A mem R O ->
    ro_agree segs mem -> frm_zero fp_csr -> f18_words segs mem ->
    res_ok_slots A b ->
    room_ag (sb_mallocs b (sup_chain_sizes id ids (snd (sup_chain_m R id ids)))) 745 ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 SUP_CHAIN) mem (seg_rom segs)) md)
      (fun c' => exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
         sup_chain_m R id ids = (R', t) /\
         c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         fp_kept fx fx' /\
         call_post_rec B MR SUP_CHAIN_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 q /\
         g_rec_rep segs L' A' mem' R' O' /\ owns_new L A O O' /\
         In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
         ~ In q (map fst O') /\
         Mem.bytes_at segs mem' q (t ++ [Z_to_bv 8 0]) /\
         others_kept segs L A mem L' A' mem' O /\
         (forall pn, In pn (blocks L' A') ->
            (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
         (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
            ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
         Mem.bytes_at segs mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
         ro_agree segs mem' /\ f18_words segs mem' /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         sb_le (sb_shift b A A') (sb_mallocs b (sup_chain_sizes id ids t)) /\
         res_ok_slots A' (sb_shift b A A')).

End K.
