From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecKindB.
Import ListNotations.
Local Open Scope Z_scope.

Definition XSTRDUP : Z := 0x15780.
Definition XSTRDUP_K : Z := ALLOC_STACK + 32.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition xstrdup_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (s : Z) (x : list byte) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' p,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR XSTRDUP_K L A regs mem md (fun a => p <= a < p + Z.of_nat (length x) + 1)
      L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 p /\ p <> 0 /\ p mod 16 = 0 /\ fresh_block B p (Z.of_nat (length x) + 1) /\
    (exists b1 b2, blocks L' A' = b1 ++ (p, Z.of_nat (length x) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    Mem.bytes_at segs mem' p (x ++ [Z_to_bv 8 0]) /\
    Mem.bytes_at segs mem' s (x ++ [Z_to_bv 8 0]) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (sb_malloc b (Z.of_nat (length x) + 1)).

Definition xstrdup_contract : Prop :=
  forall L A regs mem md (s : Z) (x slack : list byte) b,
    call_pre_k B MR XSTRDUP_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 s ->
    Mem.bytes_at segs mem s (x ++ Z_to_bv 8 0 :: slack) ->
    no0 x -> Z.of_nat (length x) <= LMAX ->
    (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) ->
    (s + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= spZ regs - XSTRDUP_K \/ spZ regs <= s) ->
    str_home B L A (spZ regs) s (Z.of_nat (length x) + 1) ->
    res_ok_slots A b -> room_slots (sb_malloc b (Z.of_nat (length x) + 1)) (Z.of_nat (length x) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 XSTRDUP) mem (seg_rom segs)) md) (xstrdup_ret L A regs mem md s x b).

End K.
