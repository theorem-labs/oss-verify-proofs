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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInvU RecKindB xmalloc_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition ARG_S : Z := 0x161c4.
Definition ARG_S_K : Z := 48 + XMALLOC_K.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition arg_s_src (L : layout) (A : astate) (sp : Z) (mem : word -> option byte) (s : Z)
    (v : option (list byte)) : Prop :=
  match v with
  | None => s = 0
  | Some x =>
      s <> 0 /\ no0 x /\ Z.of_nat (length x) <= LMAX /\
      exists slack, Mem.bytes_at segs mem s (x ++ Z_to_bv 8 0 :: slack) /\
        (- (s + Z.of_nat (length x) + 1)) mod 8 <= Z.of_nat (length slack) /\
        (s + Z.of_nat (length (x ++ Z_to_bv 8 0 :: slack)) <= sp - ARG_S_K \/ sp <= s) /\
        str_home B L A sp s (Z.of_nat (length x) + 1)
  end.

Definition arg_s_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (e m : Z) (x : list byte) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    (forall q k, In (q, k) (user_blocks A) -> In (q, k) (user_blocks A')) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\ f18_words segs mem' /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    ((m = 6 /\
      call_post_k B MR ARG_S_K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
      blocks L' A' = blocks L A /\ res_ok_slots A' b) \/
     (m < 6 /\ exists p,
      call_post_k B MR ARG_S_K L A regs mem md
        (fun a => e + CALL_OFF_NARGS <= a < e + CALL_OFF_NARGS + 4 \/
                  e + CALL_OFF_ARGS + 8 * m <= a < e + CALL_OFF_ARGS + 8 * m + 8 \/
                  p <= a < p + Z.of_nat (length x) + 1)
        L' A' regs' mem' md' /\
      p <> 0 /\ p mod 16 = 0 /\ fresh_block B p (Z.of_nat (length x) + 1) /\
      (exists b1 b2, blocks L' A' = b1 ++ (p, Z.of_nat (length x) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
      Mem.bytes_at segs mem' (e + CALL_OFF_NARGS) (Mem.le4 (Z_to_bv 64 (m + 1))) /\
      Mem.bytes_at segs mem' (e + CALL_OFF_ARGS + 8 * m) (Mem.le8 (Z_to_bv 64 p)) /\
      Mem.bytes_at segs mem' p (x ++ [Z_to_bv 8 0]) /\
      st_init_done A' = true /\
      res_ok_slots A' (sb_malloc b (Z.of_nat (length x) + 1)))).

Definition arg_s_contract : Prop :=
  forall L A regs mem md (e s m : Z) (v : option (list byte)) b,
    call_pre_k B MR ARG_S_K L A regs mem md ->
    getr regs 10 = Z_to_bv 64 e -> getr regs 11 = Z_to_bv 64 s ->
    e mod 8 = 0 -> REC_SC <= e -> e + CALL_SIZE <= G_REC + REC_SIZE ->
    Mem.wr_at segs mem e CALL_SIZE ->
    Mem.bytes_at segs mem (e + CALL_OFF_NARGS) (Mem.le4 (Z_to_bv 64 m)) -> 0 <= m <= 6 ->
    arg_s_src L A (spZ regs) mem s v ->
    f18_words segs mem ->
    res_ok_slots A b ->
    room_slots (sb_malloc b (Z.of_nat (length (sarg v)) + 1)) (Z.of_nat (length (sarg v)) + 1) ->
    ro_agree segs mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 ARG_S) mem (seg_rom segs)) md)
      (arg_s_ret L A regs mem md e m (sarg v) b).

End K.
