From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import MState Mem Frame Cells Step FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import WriterSpec WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import put_c WriterRet.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import snprintf_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import write_value_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition PJ_WRITE_PC : Z := 0x14d1c.
Definition PJW_FR : Z := 48.
Definition PJW_K (t : jv) : Z := PJW_FR + Z.max (WV_K t) (Z.max PUT_K ALLOC_STACK).

Section K.
Context {fx : Reusable.YK11.FPState} {rc : Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.

Definition pjw_where (regs : bvmap 5 word) (Lam : list (Z * Z)) (v : Z) : Prop :=
  (spZ regs <= v /\ off_errno B v 56) \/
  (exists x y, In (x, y) Lam /\ x <= v /\ v + 56 <= x + y).

Definition pj_write_ret (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (v : Z) (t : jv) (D : list (Z * Z)) (p : bool) (Lam : list (Z * Z)) (peak cnt fail : Z)
    (b : rf_R RF) (c' : config) : Prop :=
  let st' := putN (w0 cnt fail) (wdpieces t p) in
  let bw := wfold RF b (w0 cnt fail) (wdpieces t p) in
  exists (fx' : Reusable.YK11.FPState) L' A' regs' mem' md' Lam' peak' b',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    frm0 (@fp_csr fx') /\
    regs_preserved regs regs' /\
    aa_MR API L' A' mem' md' /\ WF A' /\ bounded A' /\ ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
    ledger B L' A' mem' Lam' peak' (w_cnt st') (w_fail st') /\ rf_ok RF A' b' /\
    layout_le A L L' /\ (length (st_regions A) <= length (st_regions A'))%nat /\
    (st_init_done A = true -> st_init_done A' = true) /\ (exists vm', md' = with_vmmaps vm' md) /\
    (forall q n, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) /\
    keeps B L A mem mem' 0 /\
    pj_node rsegs mem' (wv_lblk Lam) v t D /\
    (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
       ~ (spZ regs - K <= a < spZ regs) -> ~ errno_at B a -> ~ alloc_statics a ->
       mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
       (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
    (forall a, (spZ regs - K <= a < spZ regs \/ errno_at B a) -> writable_at (ms_segs B) mem a ->
       writable_at (ms_segs B) mem' a) /\
    ( (w_failed st' = 0 /\ exists q, getr regs' 10 = Z_to_bv 64 q /\ q <> 0 /\
         ~ In (q - 16, w_cap st' + 16) (blocks L A) /\
         Lam' = (q, w_cap st') :: Lam /\ peak' = Z.max peak (lsum Lam + w_cap st') /\
         b' = bw /\ zbytes_at B mem' q (wdoc t p ++ [0]))
    \/ (w_failed st' <> 0 /\ getr regs' 10 = Z_to_bv 64 0 /\ Lam' = Lam /\
         (w_cap st' = 0 /\ peak' = peak /\ b' = bw \/
          w_cap st' <> 0 /\ peak' = Z.max peak (lsum Lam + w_cap st') /\ b' = rf_free RF bw (w_cap st' + 16))) ).

Definition pj_write_ret_sb (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (v : Z) (t : jv) (D : list (Z * Z)) (p : bool) (Lam : list (Z * Z)) (peak cnt fail : Z)
    (b : sbound) (c' : config) : Prop :=
  let st' := putN (w0 cnt fail) (wdpieces t p) in
  exists (fx' : Reusable.YK11.FPState) L' A' regs' mem' md' Lam' peak' b',
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    (forall k : reg, bv_unsigned k <> 10 -> reg_get (@fp_regs fx') k = reg_get (@fp_regs fx) k) /\
    frm0 (@fp_csr fx') /\
    regs_preserved regs regs' /\
    aa_MR API L' A' mem' md' /\ WF A' /\ bounded A' /\ ro_agree (ms_segs B) mem' /\ guard_kept B mem mem' /\
    ledger B L' A' mem' Lam' peak' (w_cnt st') (w_fail st') /\ res_ok_slots A' b' /\
    layout_le A L L' /\ (length (st_regions A) <= length (st_regions A'))%nat /\
    (st_init_done A = true -> st_init_done A' = true) /\ (exists vm', md' = with_vmmaps vm' md) /\
    (forall q n, In (q, n) (user_blocks A) -> In (q, n) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q) /\
    keeps B L A mem mem' 0 /\
    pj_node rsegs mem' (wv_lblk Lam) v t D /\
    (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
       ~ (spZ regs - K <= a < spZ regs) -> ~ errno_at B a -> ~ alloc_statics a ->
       mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
       (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) /\
    (forall a, (spZ regs - K <= a < spZ regs \/ errno_at B a) -> writable_at (ms_segs B) mem a ->
       writable_at (ms_segs B) mem' a) /\
    ( (w_failed st' = 0 /\ exists q, getr regs' 10 = Z_to_bv 64 q /\ q <> 0 /\
         ~ In (q - 16, w_cap st' + 16) (blocks L A) /\
         Lam' = (q, w_cap st') :: Lam /\ peak' = Z.max peak (lsum Lam + w_cap st') /\
         b' = sb_malloc b (w_cap st' + 16) /\ zbytes_at B mem' q (wdoc t p ++ [0]))
    \/ (w_failed st' <> 0 /\ getr regs' 10 = Z_to_bv 64 0 /\ Lam' = Lam /\
         (w_cap st' = 0 /\ peak' = peak /\ b' = b \/
          w_cap st' <> 0 /\ peak' = Z.max peak (lsum Lam + w_cap st') /\ b' = b)) ).

Definition pj_write_contract : Prop :=
  forall L A regs mem md b v pretty (t : jv) D Lam peak cnt fail,
    ms_segs B = rsegs -> ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
    call_pre_t B API (PJW_K t) L A regs mem md -> st_init_done A = true ->
    ro_agree (ms_segs B) mem -> frm0 (@fp_csr fx) ->
    getr regs 10 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 pretty -> 0 <= pretty < 2 ^ 64 ->
    ledger B L A mem Lam peak cnt fail ->
    off_errno B (spZ regs - PJW_K t) (PJW_K t) ->
    pj_node rsegs mem (wv_lblk Lam) v t D -> pjw_where regs Lam v ->
    (forall a k, In (a, k) D -> In (a, k) Lam) ->
    Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
    Z.of_nat (length (wdoc t (negb (pretty =? 0)))) + 1 <= WMAX ->
    rf_ok RF A b -> wr_rooms RF b (w0 cnt fail) (wdpieces t (negb (pretty =? 0))) ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PJ_WRITE_PC) mem (seg_rom (ms_segs B))) md)
      (pj_write_ret (PJW_K t) L A regs mem md v t D (negb (pretty =? 0)) Lam peak cnt fail b).

Definition pj_write_contract_sb : Prop :=
  forall L A regs mem md b v pretty (t : jv) D Lam peak cnt fail,
    ms_segs B = rsegs -> ms_got_guard B = GOT_GUARD -> ms_guard B = GUARD ->
    call_pre_t B API (PJW_K t) L A regs mem md -> st_init_done A = true ->
    ro_agree (ms_segs B) mem -> frm0 (@fp_csr fx) ->
    getr regs 10 = Z_to_bv 64 v -> getr regs 11 = Z_to_bv 64 pretty -> 0 <= pretty < 2 ^ 64 ->
    ledger B L A mem Lam peak cnt fail ->
    off_errno B (spZ regs - PJW_K t) (PJW_K t) ->
    pj_node rsegs mem (wv_lblk Lam) v t D -> pjw_where regs Lam v ->
    (forall a k, In (a, k) D -> In (a, k) Lam) ->
    Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
    Z.of_nat (length (wdoc t (negb (pretty =? 0)))) + 1 <= WMAX ->
    res_ok_slots A b -> wr_room b ->
    SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 PJ_WRITE_PC) mem (seg_rom (ms_segs B))) md)
      (pj_write_ret_sb (PJW_K t) L A regs mem md v t D (negb (pretty =? 0)) Lam peak cnt fail b).

End K.
