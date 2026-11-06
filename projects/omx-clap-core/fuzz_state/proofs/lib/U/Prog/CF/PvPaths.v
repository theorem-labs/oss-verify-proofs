From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem Frame Exec Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog Require Import PvDefs PvModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import PvGlue PvMain0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U.Prog.CF Require Import CFS ContractCF KindBGlueCF FrameCF ReaderResCF.
Import ListNotations.
Local Open Scope Z_scope.
Module Frame := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Frame.
Module MState := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.MState.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Mem.
Module Cells := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Cells.
Module Step := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib.Step.

Section Paths.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable RF : ResForm.
Local Abbreviation segs := (ms_segs B).

Definition pv_items_stmt (d : nat) : Prop :=
  forall L A regs mem md Lam peak cnt fail b q text len p tb v,
  pv_pre B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v ->
  forall P m' regs' (o : bool) y,
  text <= P <= text + len -> rest_at tb text P = skip (rest_at tb text p) ->
  pj_in_ok rsegs m' q text len P (Z.of_nat d) tb -> Frame.wmono rsegs mem m' ->
  rest_at tb text P = (if o then 123 else 91) :: y ->
  Frame.munch [(spZ regs - 64, spZ regs); (q, q + 8)] mem m' ->
  Frame.stk rsegs m' (spZ regs - PARSE_VALUE_K d) (spZ regs) ->
  pj_zero rsegs m' v ->
  getr regs' 1 = getr regs 1 -> regs_preserved regs regs' ->
  getr regs' 10 = Z_to_bv 64 q -> getr regs' 11 = Z_to_bv 64 v -> getr regs' 12 = Z_to_bv 64 (if o then 1 else 0) ->
  SR segs (mkCfg (mkst regs' (Z_to_bv 64 0x155c8) m' (seg_rom segs)) md)
    (pv_post B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v).

Definition pv_lit_stmt (d : nat) : Prop :=
  forall L A regs mem md Lam peak cnt fail b q text len p tb v,
  pv_pre B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v ->
  forall P m' regs' b0 y wa ty,
  text <= P <= text + len -> rest_at tb text P = skip (rest_at tb text p) ->
  pj_in_ok rsegs m' q text len P (Z.of_nat d) tb -> Frame.wmono rsegs mem m' ->
  rest_at tb text P = b0 :: y -> lit_sel b0 wa ty ->
  Frame.munch [(spZ regs - 64, spZ regs); (q, q + 8)] mem m' ->
  Frame.stk rsegs m' (spZ regs - PARSE_VALUE_K d) (spZ regs) ->
  pj_zero rsegs m' v ->
  getr regs' 1 = getr regs 1 -> regs_preserved regs regs' ->
  getr regs' 10 = Z_to_bv 64 q -> getr regs' 11 = Z_to_bv 64 wa -> getr regs' 12 = Z_to_bv 64 ty ->
  getr regs' 13 = Z_to_bv 64 v ->
  SR segs (mkCfg (mkst regs' (Z_to_bv 64 0x15c28) m' (seg_rom segs)) md)
    (pv_post B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v).

Definition pv_str_stmt (d : nat) : Prop :=
  forall L A regs mem md Lam peak cnt fail b q text len p tb v,
  pv_pre B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v ->
  forall P m' regs' y,
  text <= P <= text + len -> rest_at tb text P = skip (rest_at tb text p) ->
  pj_in_ok rsegs m' q text len P (Z.of_nat d) tb -> Frame.wmono rsegs mem m' ->
  rest_at tb text P = 34 :: y ->
  Frame.munch [(spZ regs - 64, spZ regs); (q, q + 8); (v, v + 4)] mem m' ->
  Frame.stk rsegs m' (spZ regs - PARSE_VALUE_K d) (spZ regs - 48) ->
  Step.rw_cells rsegs m' (spZ regs - 48)
    [Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
     Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)] ->
  pj_rw rsegs m' v -> Mem.bytes_at rsegs m' v (Mem.le4 (Z_to_bv 64 4)) ->
  Mem.bytes_at rsegs m' (v + 4) (repeat (Z_to_bv 8 0) 52) ->
  getr regs' 1 = Z_to_bv 64 0x1459c -> getr regs' 2 = Z_to_bv 64 (spZ regs - 64) ->
  getr regs' 8 = Z_to_bv 64 v -> getr regs' 9 = Z_to_bv 64 q -> getr regs' 10 = Z_to_bv 64 q ->
  (forall r, r = 3 \/ r = 4 \/ 18 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SR segs (mkCfg (mkst regs' (Z_to_bv 64 0x158e4) m' (seg_rom segs)) md)
    (pv_post B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v).

Definition pv_num_stmt (d : nat) : Prop :=
  forall L A regs mem md Lam peak cnt fail b q text len p tb v,
  pv_pre B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v ->
  forall P m' regs' b0 y txt r,
  text <= P <= text + len -> rest_at tb text P = skip (rest_at tb text p) ->
  pj_in_ok rsegs m' q text len P (Z.of_nat d) tb -> Frame.wmono rsegs mem m' ->
  rest_at tb text P = b0 :: y -> other_b b0 -> num_tok (b0 :: y) = Some (txt, r) ->
  Frame.munch [(spZ regs - 64, spZ regs); (q, q + 8)] mem m' ->
  Frame.stk rsegs m' (spZ regs - PARSE_VALUE_K d) (spZ regs - 48) ->
  Step.rw_cells rsegs m' (spZ regs - 48)
    [Cells.C8 (getr regs 20); Cells.C8 (getr regs 19); Cells.C8 (getr regs 18); Cells.C8 (getr regs 9);
     Cells.C8 (getr regs 8); Cells.C8 (getr regs 1)] ->
  pj_zero rsegs m' v ->
  getr regs' 1 = Z_to_bv 64 0x146f4 -> getr regs' 2 = Z_to_bv 64 (spZ regs - 64) ->
  getr regs' 8 = Z_to_bv 64 v -> getr regs' 9 = Z_to_bv 64 q ->
  getr regs' 10 = Z_to_bv 64 (Z.of_nat (length txt) + 1) ->
  getr regs' 18 = Z_to_bv 64 (-1) -> getr regs' 19 = Z_to_bv 64 (Z.of_nat (length txt)) ->
  getr regs' 20 = Z_to_bv 64 (P + Z.of_nat (length txt)) ->
  (forall r, r = 3 \/ r = 4 \/ 21 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SR segs (mkCfg (mkst regs' (Z_to_bv 64 0x14064) m' (seg_rom segs)) md)
    (pv_post B API RF d L A regs mem md Lam peak cnt fail b q text len p tb v).

End Paths.
