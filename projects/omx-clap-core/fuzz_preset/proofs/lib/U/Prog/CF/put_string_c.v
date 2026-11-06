From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import MState Mem Frame Cells Step FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import put_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PUT_STRING : Z := 0x17590.
Definition PS_K : Z := 144 + PUT_K.

Definition guard_cells (mem : word -> option byte) : Prop :=
  bytes_at rsegs mem GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ exists canary, bytes_at rsegs mem GUARD (le8 canary).

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition str_where (Lam : list (Z * Z)) (s n buf : Z) : Prop :=
  (in_img B s /\ forall i, 0 <= i < n -> ro_addr rsegs (wa (s + i)) = true) \/
  (exists x y, In (x, y) Lam /\ x <> buf /\ x <= s /\ s + n <= x + y).

Definition put_string_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (o buf : Z) (st : wst) (Lam : list (Z * Z)) (peak : Z) (b : rf_R RF) (bs : list Z) (c' : config) : Prop :=
  exists fx' : YK11.FPState,
    (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    frm0 (@fp_csr fx') /\
    guard_cells (ms_mem (cfg_ms c')) /\
    @wr_ret fx' rc B API RF PS_K L A regs mem md o buf st Lam peak b (spieces bs) c'.

Definition put_string_contract : Prop :=
  forall L A regs mem md b o s buf len cap failed (text bs : list Z) Lam peak cnt fail calls,
    segs = rsegs -> ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
    call_pre_t B API PS_K L A regs mem md ->
    ro_agree segs mem -> st_init_done A = true -> frm0 (@fp_csr fx) ->
    getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 s ->
    pj_out_ok B mem Lam o buf len cap failed text ->
    ledger B L A mem Lam peak cnt fail ->
    spZ regs <= o -> off_errno B o 32 -> off_errno B (spZ regs - PS_K) PS_K ->
    zbytes_at B mem s (bs ++ [0]) -> bytes_ok bs -> no_zero bs ->
    str_where Lam s (Z.of_nat (length bs) + 1) buf ->
    len + Z.of_nat (length (wstr bs)) + 1 <= WMAX ->
    rf_ok RF A b -> wr_rooms RF b (mkW failed text cap cnt fail calls) (spieces bs) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 PUT_STRING) mem (seg_rom segs)) md)
      (put_string_ret L A regs mem md o buf (mkW failed text cap cnt fail calls) Lam peak b bs).

End K.
