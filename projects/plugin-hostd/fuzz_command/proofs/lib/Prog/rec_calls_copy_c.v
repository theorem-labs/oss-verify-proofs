From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecKindB RecModel RecInv RecInvP
  xstrdup_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REC_CALLS_COPY : Z := 0x15698.
Definition RCC_K : Z := 80 + XSTRDUP_K.

Definition rcc_args (cs : list rcall) : list (list byte) := concat (map snd cs).

Definition rcc_b (b : sbound) (xs : list (list byte)) : sbound :=
  fold_left (fun b' x => sb_malloc b' (Z.of_nat (length x) + 1)) xs b.

Definition rcc_writes (dst : Z) (cs : list rcall) (a : Z) : Prop :=
  exists i c, nth_error cs i = Some c /\
    dst + 56 * Z.of_nat i <= a < dst + 56 * Z.of_nat i + 8 + 8 * Z.of_nat (length (snd c)).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rec_calls_copy_contract : Prop :=
  forall L A regs mem md (R : rstate) (O : list (Z * Z)) (dst : Z) b,
    call_pre_k B MR RCC_K L A regs mem md ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 dst ->
    g_rec_rep segs L A mem R O ->
    (forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) ->
       spZ regs <= dst + j < 2 ^ 64 /\ writable_at segs mem (dst + j)) ->
    res_ok_slots A b -> room_slots (rcc_b b (rcc_args (r_calls R))) (LMAX + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 REC_CALLS_COPY) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' (qs : list (list (Z * Z))),
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR RCC_K L A regs mem md (rcc_writes dst (r_calls R)) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) /\
         length qs = length (r_calls R) /\
         (forall i c P, nth_error (r_calls R) i = Some c -> nth_error qs i = Some P ->
            call_at segs (blocks L' A') mem' (dst + 56 * Z.of_nat i) c P /\
            forall a s pn, nth_error (snd c) a = Some s -> nth_error P a = Some pn ->
              snd pn = Z.of_nat (length s) + 1 /\ fresh_block B (fst pn) (snd pn)) /\
         Permutation (blocks L' A') (blocks L A ++ concat qs) /\
         NoDup (map fst (concat qs)) /\
         (forall pn q, In pn (concat qs) -> In q (blocks L A) -> fst pn + snd pn <= fst q \/ fst q + snd q <= fst pn) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
         g_rec_rep segs L' A' mem' R O /\
         (forall a, in_globals frame_G a ->
            mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
         (forall j, 0 <= j < 56 * Z.of_nat (length (r_calls R)) -> writable_at segs mem' (dst + j)) /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (rcc_b b (rcc_args (r_calls R)))).

End K.
