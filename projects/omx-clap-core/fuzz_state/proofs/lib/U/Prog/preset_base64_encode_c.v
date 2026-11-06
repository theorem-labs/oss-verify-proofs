From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger fuzz_malloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec.
Import ListNotations.
Local Open Scope Z_scope.

Definition PRESET_BASE64_ENCODE : Z := 0x151c0.
Definition ENC_STACK : Z := ALLOC_STACK + 64.
Definition G_B64 : Z := 0x104a4.
Definition enc_size (len : Z) : Z := (len + 2) / 3 * 4 + 1.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition enc_data_where (L : layout) (A : astate) (regs : bvmap 5 word) (data len : Z) : Prop :=
  len = 0 \/
  (exists a k, In (a, k) (blocks L A) /\ a <= data /\ data + len <= a + k) \/
  (forall i, 0 <= i < len -> Mem.ro_addr segs (Z_to_bv 64 (data + i)) = true) \/
  spZ regs <= data.

Definition enc_writes (q n a : Z) : Prop := alloc_writes q a \/ (q <> 0 /\ q <= a < q + n).

Definition preset_base64_encode_contract : Prop :=
  forall L A regs mem md data len bs b Lam peak cnt fail,
    ms_segs B = rsegs ->
    errno_addr B + 4 <= alloc_ceiling ->
    ro_agree segs mem ->
    call_pre_k B MR ENC_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 len ->
    0 <= data < 2 ^ 64 -> data + len <= 2 ^ 64 ->
    bytes_ok bs -> Z.of_nat (length bs) = len -> len <= 2 ^ 27 ->
    (forall i, 0 <= i < len -> mbyte segs mem (data + i) = Some (Z_to_bv 8 (nth (Z.to_nat i) bs 0))) ->
    enc_data_where L A regs data len ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok RF A b -> rf_room RF b (enc_size len + 16) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PRESET_BASE64_ENCODE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' q,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         call_post_k B MR ENC_STACK L A regs mem md (enc_writes q (enc_size len)) L' A' regs' mem' md' /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         getr regs' 10 = Z_to_bv 64 q /\
         keeps B L A mem mem' 0 /\ ublocks_kept L A A' (0, 0) /\
         (forall i, 0 <= i < len -> mbyte segs mem' (data + i) = mbyte segs mem (data + i)) /\
         ( (cnt = fail /\ q = 0 /\ rf_ok RF A' b /\ blocks L' A' = blocks L A /\
            ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1))
         \/ (cnt <> fail /\ q <> 0 /\ q mod 16 = 0 /\ rf_ok RF A' (rf_malloc RF b (enc_size len + 16)) /\
            (forall i, 0 <= i < enc_size len + 16 -> ~ alloc_statics (q - 16 + i)) /\
            (forall i, 0 <= i < enc_size len + 16 -> ~ in_img B (q - 16 + i)) /\ ~ In q (map fst Lam) /\
            (exists b1 b2, blocks L' A' = b1 ++ (q - 16, enc_size len + 16) :: b2 /\ blocks L A = b1 ++ b2) /\
            ledger B L' A' mem' ((q, enc_size len) :: Lam) (Z.max peak (lsum Lam + enc_size len))
              ((cnt + 1) mod 2 ^ 64) fail /\
            (forall i, 0 <= i < enc_size len ->
               mbyte segs mem' (q + i) = nth_error (map (Z_to_bv 8) (b64_enc bs ++ [0])) (Z.to_nat i))) )).

End K.
