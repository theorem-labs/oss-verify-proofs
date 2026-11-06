From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
Import ListNotations.
Local Open Scope Z_scope.

Definition TX_PUT : Z := 0x154b8.
Definition TX_REALLOC : Z := 0x19bfc.
Definition TX_STACK : Z := REALLOC_STACK + 32.

Section K.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition mbytes (mem : word -> option byte) (a : Z) (bs : list byte) : Prop :=
  forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs mem (a + i) = nth_error bs (Z.to_nat i).

(* The harness's struct text {b; n; cap; failed} at t (new fuzz_preset.c:379-384): the three words b / n / cap, and its
   int `failed` at offset 24 equal to 0. tx_put reads `failed` first and appends only while it is 0 (new :390-391); it
   sets it only when realloc returns NULL (new :395-398), the arm the rf_room premise below excludes, so it stays 0. *)
Definition text_rec (mem : word -> option byte) (t b len cap : Z) : Prop :=
  mbytes mem t (Mem.le8 (Z_to_bv 64 b) ++ Mem.le8 (Z_to_bv 64 len) ++ Mem.le8 (Z_to_bv 64 cap)) /\
  t + 28 <= 2 ^ 64 /\ mbytes mem (t + 24) (Mem.le4 (Z_to_bv 64 0)).

Definition tx_inv (L : layout) (A : astate) (mem : word -> option byte) (b len cap : Z) (txt : list byte) : Prop :=
  Z.of_nat (length txt) = len /\
  ((cap = 0 /\ b = 0 /\ len = 0) \/
   (0 < cap /\ In (b, cap) (blocks L A) /\ len < cap /\ mbytes mem b (txt ++ [Z_to_bv 8 0]) /\
    forall i, 0 <= i < cap -> ~ in_img B (b + i))).

Definition tx_writes (t b0 cap0 b1 cap1 : Z) (a : Z) : Prop :=
  t <= a < t + 24 \/ b0 <= a < b0 + cap0 \/ b1 <= a < b1 + cap1.

Definition tx_frame (stk : Z) (regs : bvmap 5 word) (E : Z -> Prop)
    (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  MR L' A' mem' md' /\ WF A' /\ bounded A' /\ layout_le A L L' /\
  (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A') -> ptr_addr L' p = ptr_addr L p) /\
  (exists vm', md' = with_vmmaps vm' md) /\
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) ->
     ~ owned B L A a -> ~ owned B L' A' a -> ~ scratch_k B stk regs a -> ~ E a ->
     mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
  (forall p k i, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A') -> 0 <= i < k ->
     ~ E (ptr_addr L p + i) -> mbyte segs mem' (ptr_addr L p + i) = mbyte segs mem (ptr_addr L p + i)) /\
  (forall a, scratch_k B stk regs a -> writable_at segs mem' a).

Variable F : ResForm.

Definition tx_put_contract : Prop :=
  forall L A regs mem md (t s n b0 len0 cap0 : Z) (txt src : list byte) (bnd : rf_R F),
    call_pre_k B MR TX_STACK L A regs mem md ->
    st_init_done A = true ->
    ro_agree segs mem ->
    getr regs 10 = Z_to_bv 64 t -> getr regs 11 = Z_to_bv 64 s -> getr regs 12 = Z_to_bv 64 n ->
    spZ regs <= t -> t + 24 <= 2 ^ 64 -> t mod 8 = 0 ->
    (forall i, 0 <= i < 24 -> writable_at segs mem (t + i)) ->
    0 <= b0 < 2 ^ 64 -> 0 <= len0 < 2 ^ 64 -> 0 <= cap0 < 2 ^ 64 ->
    text_rec mem t b0 len0 cap0 ->
    tx_inv L A mem b0 len0 cap0 txt ->
    0 <= s < 2 ^ 64 -> 0 <= n -> s + n <= 2 ^ 64 ->
    mbytes mem s src -> Z.of_nat (length src) = n ->
    (forall i, 0 <= i < n ->
       ~ (t <= s + i < t + 24) /\ ~ (spZ regs - TX_STACK <= s + i < spZ regs) /\ ~ (b0 <= s + i < b0 + cap0) /\
       (len0 + n + 1 <= cap0 \/ spZ regs <= s + i \/ Mem.ro_addr segs (Z_to_bv 64 (s + i)) = true \/
        exists a k, In (a, k) (blocks L A) /\ a <> b0 /\ a <= s + i < a + k)) ->
    len0 + n + 1 <= 2 ^ 28 ->
    rf_ok F A bnd -> (cap0 < len0 + n + 1 -> rf_room F bnd (2 * (len0 + n + 1))) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 TX_PUT) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' b1 cap1 bnd',
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         tx_frame TX_STACK regs (tx_writes t b0 cap0 b1 cap1) L A mem md L' A' mem' md' /\
         regs_preserved regs regs' /\
         blocks_kept B L A mem mem' (fun a => a = b0) /\
         text_rec mem' t b1 (len0 + n) cap1 /\
         (forall i, 0 <= i < 24 -> writable_at segs mem' (t + i)) /\
         tx_inv L' A' mem' b1 (len0 + n) cap1 (txt ++ src) /\
         mbytes mem' s src /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\ st_init_done A' = true /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         rf_ok F A' bnd' /\
         ( (len0 + n + 1 <= cap0 /\ b1 = b0 /\ cap1 = cap0 /\ L' = L /\ A' = A /\ md' = md /\ bnd' = bnd)
         \/ (cap0 < len0 + n + 1 /\ cap1 = 2 * (len0 + n + 1) /\ b1 mod 16 = 0 /\ bnd' = tx_step F bnd cap0 cap1 /\
            exists bl1 bl2 bm1 bm2, blocks L' A' = bm1 ++ (b1, cap1) :: bm2 /\ bm1 ++ bm2 = bl1 ++ bl2 /\
              ((cap0 = 0 /\ blocks L A = bl1 ++ bl2) \/ (cap0 <> 0 /\ blocks L A = bl1 ++ (b0, cap0) :: bl2))))).

End K.
