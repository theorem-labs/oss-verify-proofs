From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import VerbsB.
Import ListNotations.
Local Open Scope Z_scope.

Definition JOINED : Z := 0x15324.
Definition JOINED_FRAME : Z := 80.

Definition nul8 : byte := Z_to_bv 8 0.
Definition sp8 : byte := Z_to_bv 8 32.

Definition join_need (ws : list (list byte)) : Z :=
  fold_right (fun w acc => Z.of_nat (length w) + 1 + acc) 0 ws.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition in_block (L : layout) (A : astate) (a len : Z) : Prop :=
  exists p n, In (p, n) (blocks L A) /\ p <= a /\ a + len <= p + n.

Definition word_cstr (mem : word -> option byte) (p : Z) (w : list byte) : Prop :=
  ~ In nul8 w /\ le_at B mem p (w ++ [nul8]).

Definition words_place (L : layout) (A : astate) (mem : word -> option byte) (arr : Z) (wp : list Z)
    (ws : list (list byte)) : Prop :=
  in_block L A arr (8 * Z.of_nat (length ws)) /\
  forall k, (k < length ws)%nat -> in_block L A (nth k wp 0) (Z.of_nat (length (nth k ws [])) + 1).

Definition words_view (mem : word -> option byte) (W arr : Z) (wp : list Z) (ws : list (list byte)) : Prop :=
  length wp = length ws /\ Z.of_nat (length ws) < 2 ^ 31 /\
  le_at B mem (W + 24) (Mem.le4 (Z_to_bv 64 (Z.of_nat (length ws)))) /\
  le_at B mem (W + 16) (Mem.le8 (Z_to_bv 64 arr)) /\
  (forall k, (k < length ws)%nat ->
     le_at B mem (arr + 8 * Z.of_nat k) (Mem.le8 (Z_to_bv 64 (nth k wp 0))) /\ word_cstr mem (nth k wp 0) (nth k ws [])).

Definition joined_writes (res n outp : Z) (a : Z) : Prop :=
  res <= a < res + n \/ outp <= a < outp + 8.

Definition joined_contract : Prop :=
  forall L A regs mem md b (W arr outp : Z) (wp : list Z) (ws : list (list byte)),
    call_pre_k B MR (ALLOC_STACK + JOINED_FRAME) L A regs mem md ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 W -> getr regs 11 = Z_to_bv 64 outp ->
    words_view mem W arr wp ws ->
    words_place L A mem arr wp ws ->
    W mod 8 = 0 -> arr mod 8 = 0 ->
    spZ regs <= W + 16 -> W + 32 <= 2 ^ 64 ->
    join_need ws + 1 <= 2 ^ 28 ->
    spZ regs <= outp -> outp + 8 <= 2 ^ 64 -> (outp + 8 <= W + 16 \/ W + 32 <= outp) ->
    (forall i, 0 <= i < 8 -> writable_at segs mem (outp + i)) -> outp mod 8 = 0 ->
    (forall i, 0 <= i < 8 -> ~ owned B L A (outp + i) /\ ~ scratch_k B (ALLOC_STACK + JOINED_FRAME) regs (outp + i)) ->
    res_ok_slots A b -> room_slots b (join_need ws + 1) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 JOINED) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' res,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         call_post_k B MR (ALLOC_STACK + JOINED_FRAME) L A regs mem md
           (joined_writes res (join_need ws + 1) outp) L' A' regs' mem' md' /\
         getr regs' 10 = Z_to_bv 64 res /\
         res <> 0 /\ fresh_block B res (join_need ws + 1) /\
         (exists b1 b2, blocks L' A' = b1 ++ (res, join_need ws + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
         le_at B mem' res (join_sp ws ++ [nul8]) /\
         le_at B mem' outp (Mem.le8 (Z_to_bv 64 (Z.of_nat (length (join_sp ws))))) /\
         blocks_kept B L A mem mem' (fun _ => False) /\
         ro_agree segs mem' /\
         (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
         st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         res_ok_slots A' (sb_malloc b (join_need ws + 1))).

End K.
