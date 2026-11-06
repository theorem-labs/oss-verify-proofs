From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strlen_c strcpy_c strcat_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Theorem strcat_holds : strlen_contract -> strcpy_contract -> strcat_contract.
Proof.
  intros SLEN SCPY. unfold strcat_contract, STRCAT. intros until lo.
  intros DS DNZ DPAD DST SRC NONUL PAD SEP ST LO SEPD SEPW SEPS MI.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (bytes_at_bound _ _ _ _ DS) as DB. rewrite length_app in DB. cbn [length] in DB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB. rewrite length_app in SB. cbn [length] in SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as WB. cbn [cells_size csize Nat.add] in WB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp);
    (bv_unsigned a0 + Z.of_nat (length dstr), bv_unsigned a0 + Z.of_nat (length dstr) + Z.of_nat (length str) + 1)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 32%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 32%nat junk0 [] [8; 8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 7 step.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dstr dslack).
  1-4: first [eassumption | lia].
  cbv delta [mkR].
  apply bytes_at_app in DS. destruct DS as [DS DS2]. clear DS2.
  do 3 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply (SCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str slack junk lo);
      rewrite ?unsigned_lit by lia; first [eassumption | lia]
    | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold strcpy_post in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call rsegs mm ]
  end.
  match goal with H : stk _ _ _ _ |- _ => rename H into ST end.
  cbv delta [mkR].
  do 6 step.
  release_frame FR ST (bv_unsigned sp).
  finish.
  apply bytes_at_app. split; [exact DS|].
  match goal with H : rw_cells _ _ _ [CB _ (str ++ _)] |- _ => exact (proj1 (u8arr_of_rw_cells _ _ _ _ _ H)) end.
Qed.
