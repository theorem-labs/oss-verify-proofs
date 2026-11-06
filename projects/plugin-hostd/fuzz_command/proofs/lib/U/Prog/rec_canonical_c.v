From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecKindB xmalloc_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition REC_CANONICAL : Z := 0x15980.
Definition REC_CANONICAL_K : Z := 32 + XMALLOC_K.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition rec_canonical_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (text : Z) (T : list byte) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' p,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR REC_CANONICAL_K L A regs mem md (fun a => p <= a < p + Z.of_nat (length T) + 1)
      L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 p /\ p <> 0 /\ p mod 16 = 0 /\ fresh_block B p (Z.of_nat (length T) + 1) /\
    (exists b1 b2, blocks L' A' = b1 ++ (p, Z.of_nat (length T) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    Mem.bytes_at segs mem' p (canon T ++ [Z_to_bv 8 0]) /\
    Mem.bytes_at segs mem' text T /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (sb_malloc b (Z.of_nat (length T) + 1)).

Definition rec_canonical_contract : Prop :=
  forall L A regs mem md (text : Z) (T : list byte) b,
    call_pre_k B MR REC_CANONICAL_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 text -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length T)) ->
    Mem.bytes_at segs mem text T -> text <> 0 ->
    no0 T -> Z.of_nat (length T) <= LMAX ->
    (text + Z.of_nat (length T) <= spZ regs - REC_CANONICAL_K \/ spZ regs <= text) ->
    str_home B L A (spZ regs) text (Z.of_nat (length T)) ->
    res_ok_slots A b -> room_slots (sb_malloc b (Z.of_nat (length T) + 1)) (Z.of_nat (length T) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 REC_CANONICAL) mem (seg_rom segs)) md)
      (rec_canonical_ret L A regs mem md text T b).

End K.
