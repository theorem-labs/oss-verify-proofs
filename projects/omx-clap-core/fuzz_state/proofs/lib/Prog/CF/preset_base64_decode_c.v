From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger WriterSpec.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import fuzz_malloc_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PRESET_BASE64_DECODE : Z := 0x14e90.
Definition DEC_STACK : Z := ALLOC_STACK + 128.
Definition dec_size (tb : list Z) : Z := Z.of_nat (length tb) / 4 * 3 + 3.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition dec_text_where (L : layout) (A : astate) (regs : bvmap 5 word) (Lam : list (Z * Z)) (text n : Z) : Prop :=
  (forall i, 0 <= i < n -> Mem.ro_addr segs (Z_to_bv 64 (text + i)) = true) \/
  spZ regs <= text \/
  (exists a k, In (a, k) Lam /\ a <= text /\ text + n <= a + k) \/
  (exists a k, In (a, k) (blocks L A) /\ a <= text /\ text + n <= a + k).

Definition dec_writes (q n lenp a : Z) : Prop :=
  alloc_statics a \/ (q <> 0 /\ q - 16 <= a < q + n) \/ lenp <= a < lenp + 8.

Definition preset_base64_decode_contract : Prop :=
  forall L A regs mem md text lenp tb slack b Lam peak cnt fail,
    ms_segs B = rsegs ->
    errno_addr B + 4 <= alloc_ceiling ->
    ro_agree segs mem ->
    call_pre_k B MR DEC_STACK L A regs mem md ->
    getr regs 10 = Z_to_bv 64 text -> getr regs 11 = Z_to_bv 64 lenp ->
    no_zero tb -> bytes_ok tb -> Z.of_nat (length tb) <= 2 ^ 28 ->
    Mem.bytes_at segs mem text (map (Z_to_bv 8) (tb ++ [0]) ++ slack) ->
    (- (text + Z.of_nat (length tb) + 1)) mod 8 <= Z.of_nat (length slack) ->
    dec_text_where L A regs Lam text (Z.of_nat (length tb) + 1) ->
    spZ regs <= lenp < 2 ^ 64 -> lenp mod 8 = 0 ->
    (forall i, 0 <= i < 8 -> writable_at segs mem (lenp + i)) ->
    lenp + 8 <= text \/ text + Z.of_nat (length tb) + 1 <= lenp ->
    ledger B L A mem Lam peak cnt fail ->
    rf_ok RF A b -> rf_room RF b (dec_size tb + 16) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PRESET_BASE64_DECODE) mem (seg_rom segs)) md)
      (fun c' => exists L' A' regs' mem' md' q,
         c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
         ro_agree segs mem' /\ guard_kept B mem mem' /\
         (st_init_done A = true -> st_init_done A' = true) /\
         call_post_k B MR DEC_STACK L A regs mem md (dec_writes q (dec_size tb) lenp) L' A' regs' mem' md' /\
         (length (st_regions A) <= length (st_regions A'))%nat /\
         keeps B L A mem mem' 0 /\
         (forall i, 0 <= i <= Z.of_nat (length tb) -> mbyte segs mem' (text + i) = mbyte segs mem (text + i)) /\
         ( (cnt = fail /\ q = 0 /\ getr regs' 10 = Z_to_bv 64 0 /\ blocks L' A' = blocks L A /\ ublocks_kept L A A' (0, 0) /\
            (forall i, 0 <= i < 8 -> mbyte segs mem' (lenp + i) = mbyte segs mem (lenp + i)) /\
            ledger B L' A' mem' Lam peak ((cnt + 1) mod 2 ^ 64) (2 ^ 64 - 1) /\
            rf_ok RF A' b)
         \/ (cnt <> fail /\ b64_dec tb = None /\ q <> 0 /\ q + dec_size tb <= alloc_ceiling /\
            (forall i, 0 <= i < dec_size tb + 16 -> ~ in_img B (q - 16 + i)) /\
            getr regs' 10 = Z_to_bv 64 0 /\ blocks L' A' = blocks L A /\
            ublocks_kept L A A' (0, 0) /\
            (forall i, 0 <= i < 8 -> mbyte segs mem' (lenp + i) = mbyte segs mem (lenp + i)) /\
            ledger B L' A' mem' Lam (Z.max peak (lsum Lam + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail /\
            rf_ok RF A' (rf_free RF (rf_malloc RF b (dec_size tb + 16)) (dec_size tb + 16)))
         \/ (exists bs, cnt <> fail /\ b64_dec tb = Some bs /\ q <> 0 /\ getr regs' 10 = Z_to_bv 64 q /\
            q mod 16 = 0 /\ ~ In q (map fst Lam) /\
            (forall i, 0 <= i < dec_size tb + 16 -> ~ alloc_statics (q - 16 + i)) /\
            (forall i, 0 <= i < dec_size tb + 16 -> ~ in_img B (q - 16 + i)) /\
            (exists b1 b2, blocks L' A' = b1 ++ (q - 16, dec_size tb + 16) :: b2 /\ blocks L A = b1 ++ b2) /\
            ublocks_kept L A A' (0, 0) /\
            ledger B L' A' mem' ((q, dec_size tb) :: Lam) (Z.max peak (lsum Lam + dec_size tb))
              ((cnt + 1) mod 2 ^ 64) fail /\
            Mem.bytes_at segs mem' q (map (Z_to_bv 8) bs) /\
            Mem.bytes_at segs mem' lenp (Mem.le8 (Z_to_bv 64 (Z.of_nat (length bs)))) /\
            rf_ok RF A' (rf_malloc RF b (dec_size tb + 16))) )).

End K.
