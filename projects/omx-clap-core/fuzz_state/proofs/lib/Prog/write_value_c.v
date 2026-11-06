From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Frame Cells Step FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterApp WriterValue Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct put_c WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import snprintf_c put_string_c indent_c.
Import ListNotations.
Local Open Scope Z_scope.

Definition WRITE_VALUE_PC : Z := 0x14998.
Definition WV_FR : Z := 112.
Definition WV_KMAX : Z := Z.max PUT_K (Z.max PS_K IND_K).
Definition WV_K (t : jv) : Z := WV_FR * (Z.of_nat (PjTree.depth t) + 1) + WV_KMAX.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Definition wv_lblk (Lam : list (Z * Z)) (a k : Z) : Prop := In (a, k) Lam.

Definition wv_where (regs : bvmap 5 word) (Lam : list (Z * Z)) (v buf : Z) : Prop :=
  (spZ regs <= v /\ off_errno B v 56) \/
  (exists x y, In (x, y) Lam /\ x <> buf /\ x <= v /\ v + 56 <= x + y).

Definition write_value_ret (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (o buf : Z) (st : wst) (Lam : list (Z * Z)) (peak : Z) (b : rf_R RF) (v : Z) (t : jv)
    (D : list (Z * Z)) (P : list (list Z)) (c' : config) : Prop :=
  exists fx' : YK11.FPState,
    (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    frm0 (@fp_csr fx') /\
    guard_cells (ms_mem (cfg_ms c')) /\
    pj_node rsegs (ms_mem (cfg_ms c')) (wv_lblk Lam) v t D /\
    @wr_ret fx' rc B API RF K L A regs mem md o buf st Lam peak b P c'.

Definition write_value_contract : Prop :=
  forall L A regs mem md b o v pretty d (t : jv) D buf (st : wst) Lam peak,
    ms_segs B = rsegs -> ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
    call_pre_t B API (WV_K t) L A regs mem md -> st_init_done A = true ->
    ro_agree (ms_segs B) mem -> frm0 (@fp_csr fx) ->
    getr regs 10 = Z_to_bv 64 o -> getr regs 11 = Z_to_bv 64 v ->
    getr regs 12 = Z_to_bv 64 pretty -> getr regs 13 = Z_to_bv 64 d ->
    0 <= pretty < 2 ^ 64 -> 0 <= d < 2 ^ 31 -> d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
    pj_out_ok B mem Lam o buf (Z.of_nat (length (w_text st))) (w_cap st) (w_failed st) (w_text st) ->
    ledger B L A mem Lam peak (w_cnt st) (w_fail st) ->
    spZ regs <= o -> off_errno B o 32 -> off_errno B (spZ regs - WV_K t) (WV_K t) ->
    pj_node rsegs mem (wv_lblk Lam) v t D -> wv_where regs Lam v buf ->
    (forall a k, In (a, k) D -> In (a, k) Lam /\ a <> buf) ->
    (forall x, o <= x < o + 32 -> ~ pj_foot v D x) ->
    Z.of_nat (length (w_text st)) + Z.of_nat (length (concat (wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX ->
    rf_ok RF A b -> wr_rooms RF b st (wvpieces t (negb (pretty =? 0)) d) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 WRITE_VALUE_PC) mem (seg_rom (ms_segs B))) md)
      (write_value_ret (WV_K t) L A regs mem md o buf st Lam peak b v t D (wvpieces t (negb (pretty =? 0)) d)).

End K.
