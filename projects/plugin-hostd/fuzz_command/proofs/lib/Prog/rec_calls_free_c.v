From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecKindB RecModel RecInv RecInvP.
Import ListNotations.
Local Open Scope Z_scope.

Definition REC_CALLS_FREE : Z := 0x155f0.
Definition RCF_K : Z := ALLOC_STACK + 64.

Definition freed (ps : list (list (Z * Z))) : list (Z * Z) :=
  List.filter (fun pn => negb (fst pn =? 0)) (concat ps).

Definition nargs_field (c : Z) (n : nat) (a : Z) : Prop :=
  exists i, (i < n)%nat /\ c + 56 * Z.of_nat i + 4 <= a < c + 56 * Z.of_nat i + 8.

Definition rfree_b (b : sbound) (F : list (Z * Z)) : sbound :=
  fold_left (fun b' pn => sb_free b' (snd pn)) F b.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition calls_slots (L : layout) (A : astate) (mem : word -> option byte) (c : Z)
    (ps : list (list (Z * Z))) : Prop :=
  (length ps <= 16)%nat /\
  forall i P, nth_error ps i = Some P ->
    (length P <= 6)%nat /\
    Mem.bytes_at segs mem (c + 56 * Z.of_nat i + 4) (Mem.le4 (Z_to_bv 64 (Z.of_nat (length P)))) /\
    (forall j, 0 <= j < 4 -> writable_at segs mem (c + 56 * Z.of_nat i + 4 + j)) /\
    forall a pn, nth_error P a = Some pn ->
      Mem.bytes_at segs mem (c + 56 * Z.of_nat i + 8 + 8 * Z.of_nat a) (Mem.le8 (Z_to_bv 64 (fst pn))) /\
      (fst pn = 0 \/ In pn (blocks L A)).

Definition rec_calls_free_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (c : Z) (ps : list (list (Z * Z))) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    call_post_k B MR RCF_K L A regs mem md (nargs_field c (length ps)) L' A' regs' mem' md' /\
    Permutation (blocks L A) (blocks L' A' ++ freed ps) /\
    blocks_kept B L A mem mem' (fun a => In a (map fst (freed ps))) /\
    (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) (freed ps) ->
       In (q, k) (user_blocks A')) /\
    (forall x, In x (user_blocks A') -> In x (user_blocks A)) /\
    (forall i, (i < length ps)%nat ->
       Mem.bytes_at segs mem' (c + 56 * Z.of_nat i + 4) (Mem.le4 (Z_to_bv 64 0)) /\
       forall j, 0 <= j < 4 -> writable_at segs mem' (c + 56 * Z.of_nat i + 4 + j)) /\
    (forall j, 0 <= j < 56 * Z.of_nat (length ps) -> ~ nargs_field c (length ps) (c + j) ->
       mbyte segs mem' (c + j) = mbyte segs mem (c + j)) /\
    (forall a, in_globals frame_G a -> ~ nargs_field c (length ps) a ->
       mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    (st_init_done A = true -> st_init_done A' = true) /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    (st_init_done A = false -> L' = L /\ A' = A /\ (forall lo, spZ regs <= lo -> c + 56 * Z.of_nat (length ps) <= lo ->
       auxv_pre B (ly_sec L) lo mem -> auxv_pre B (ly_sec L') lo mem')) /\
    res_ok_slots A' (rfree_b b (freed ps)).

Definition rec_calls_free_contract : Prop :=
  forall L A regs mem md (c : Z) (ps : list (list (Z * Z))) b,
    call_pre_k B MR RCF_K L A regs mem md ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 c -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length ps)) ->
    calls_slots L A mem c ps ->
    NoDup (map fst (freed ps)) ->
    0 <= c -> c + 56 * Z.of_nat (length ps) <= 2 ^ 64 ->
    (forall j, 0 <= j < 56 * Z.of_nat (length ps) -> spZ regs <= c + j \/ in_globals frame_G (c + j)) ->
    res_ok_slots A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 REC_CALLS_FREE) mem (seg_rom segs)) md)
      (rec_calls_free_ret L A regs mem md c ps b).

Definition rec_calls_free_g_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists L' A' regs' mem' md' Q,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
    rep_at segs (blocks L A) mem G_REC REC_SC R Q /\ (forall pn, In pn O <-> In pn (lay_blocks Q)) /\
    call_post_k B MR RCF_K L A regs mem md (nargs_field (G_REC + OFF_CALLS) (length (r_calls R)))
      L' A' regs' mem' md' /\
    Permutation (blocks L A) (blocks L' A' ++ concat (l_calls Q)) /\
    blocks_kept B L A mem mem' (fun a => In a (map fst (concat (l_calls Q)))) /\
    (forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) (concat (l_calls Q)) ->
       In (q, k) (user_blocks A')) /\
    (forall x, In x (user_blocks A') -> In x (user_blocks A)) /\
    (forall i, (i < length (r_calls R))%nat ->
       Mem.bytes_at segs mem' (G_REC + OFF_CALLS + 56 * Z.of_nat i + 4) (Mem.le4 (Z_to_bv 64 0)) /\
       forall j, 0 <= j < 4 -> writable_at segs mem' (G_REC + OFF_CALLS + 56 * Z.of_nat i + 4 + j)) /\
    (forall a, in_globals frame_G a -> ~ nargs_field (G_REC + OFF_CALLS) (length (r_calls R)) a ->
       mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
    ro_agree segs mem' /\ guard_kept B mem mem' /\
    (st_init_done A = true -> st_init_done A' = true) /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    (st_init_done A = false -> L' = L /\ A' = A /\ (forall lo, spZ regs <= lo ->
       auxv_pre B (ly_sec L) lo mem -> auxv_pre B (ly_sec L') lo mem')) /\
    res_ok_slots A' (rfree_b b (concat (l_calls Q))).

Definition rec_calls_free_g_contract : Prop :=
  forall L A regs mem md (R : rstate) (O : list (Z * Z)) b,
    call_pre_k B MR RCF_K L A regs mem md ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 (G_REC + OFF_CALLS) ->
    getr regs 11 = Z_to_bv 64 (Z.of_nat (length (r_calls R))) ->
    g_rec_rep segs L A mem R O ->
    res_ok_slots A b ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 REC_CALLS_FREE) mem (seg_rom segs)) md)
      (rec_calls_free_g_ret L A regs mem md R O b).

End K.
