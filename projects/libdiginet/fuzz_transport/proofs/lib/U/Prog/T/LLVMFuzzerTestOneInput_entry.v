(* The entry of LLVMFuzzerTestOneInput in the ubsan image, 0x13760 .. the first loop head 0x139dc (or the exit
   0x145e8): llvm_entry_stmt of U/Prog/T/LLVMFuzzerTestOneInput_lh.v. The walk is cut into segments in CPS form:
     U/Prog/T/LLVMFuzzerTestOneInput_entry_pro.v  0x13760 .. 0x137f8  prologue, size test, flags byte
     U/Prog/T/LLVMFuzzerTestOneInput_entry_cfg.v  0x137f8 .. 0x13854  config_default, host_mac, flag fields, desk_mac
     U/Prog/T/LLVMFuzzerTestOneInput_entry_lad.v  0x13854 .. 0x138d4  the config bytes (main path and ladder)
     U/Prog/T/LLVMFuzzerTestOneInput_entry_tl.v   0x138d4 .. 0x13988  max_body, scalars, M, diginet_session_init
     U/Prog/T/LLVMFuzzerTestOneInput_entry_t2.v   0x13988 .. 0x139dc  abort test, empty cursor exit, frame slots
   The model (TModel/TOps.v:351-397) is cut the same way in U/Prog/T/LLVMFuzzerTestOneInput_entry_m.v; the premise
   on LLVMFuzzerTestOneInput_m, taken at the stream fun _ => 4096, gives config_default's and init's results (the
   prologue reads no address of the stream) and rc = SPEC_OK (abort() at 0x14824 is not reached); taken at any
   stream, it gives the loop invariant of the post. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog Require Import memcpy_c memset_c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require Import DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TImg TWorldMem TSess0 TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TImgU WMem TContract
  diginet_session_config_default_c diginet_session_init_c
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d
  LLVMFuzzerTestOneInput_entry_pro LLVMFuzzerTestOneInput_entry_cfg LLVMFuzzerTestOneInput_entry_lt
  LLVMFuzzerTestOneInput_entry_lad LLVMFuzzerTestOneInput_entry_tl LLVMFuzzerTestOneInput_entry_t2.
Import ListNotations.
Open Scope Z_scope.

Theorem llvm_entry_holds : memcpy_contract -> memset_contract -> diginet_session_config_default_contract ->
  diginet_session_init_contract -> llvm_entry_stmt.
Proof.
  intros MCPY MSET CDEF INIT. unfold llvm_entry_stmt.
  intros data D regs0 F fc m lo B E10 E11 S16 ST LO H63 HWL HDAT MI RR WM HMOD.
  destruct (fuzz_u8_m D (fuzz_in_m (Z.of_nat (length D)))) as [[o n] flags] eqn:EC1.
  pose proof (ent_c1_facts D o n flags EC1) as (Ho & Hn & Hon & Hfl & HL0 & HL1).
  assert (HD0 : D = [] -> n = 0).
  { intros HE. subst D. destruct (HL0 eq_refl) as (_ & Hn0 & _). exact Hn0. }
  pose proof ST as (Hlo & _ & _).
  pose proof (wm_len _ _ _ _ WM) as LB.
  assert (HNUM : ent_num (bv_unsigned (reg_get regs0 2) - LH_FRAME) lo).
  { unfold ent_num, LH_FRAME, LH_K in *. split; [Z.div_mod_to_equations; lia|]. lia. }
  apply (ent_pro data D regs0 F fc m lo B o n flags E10 E11 S16 ST LO H63 HWL HDAT MI RR WM EC1).
  intros HSZ ms1 HS1.
  (* the model's prologue, at the stream fun _ => 4096 *)
  assert (HA0 : lh_heap_ok (fun _ => 4096)) by (intros k Hk; lia).
  destruct (HMOD _ HA0) as (Bw0 & HM0).
  rewrite (ent_model _ _ _ _ HSZ) in HM0.
  revert HM0. destruct (diginet_session_config_default_m B) as [[B1 u]|] eqn:ECD; intros HM0;
    cbv beta iota in HM0; [|discriminate HM0].
  destruct u.
  pose proof (ent_cd_len B B1 LB ECD) as LB1.
  revert HM0.
  destruct (diginet_session_init_m (ent_B24 D B1) 0 (ti_io_send timg_ubsan) (ti_io_recv timg_ubsan)
              (ti_io_now timg_ubsan) (ti_notice timg_ubsan) 0) as [[B25 rc]|] eqn:EIN; intros HM0;
    cbv beta iota in HM0; [|discriminate HM0].
  revert HM0. destruct (rc =? SPEC_OK) eqn:ERC; intros HM0; cbn [negb] in HM0; [|discriminate HM0].
  apply Z.eqb_eq in ERC. unfold SPEC_OK in ERC. subst rc.
  destruct (ent_B24_eq D B1 o n flags EC1 Hn) as [EB24 EC10].
  (* the loop invariant, at every stream *)
  assert (HLOOP : forall A, lh_heap_ok A ->
            exists Bw', LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_ubsan B25 A D (cur o n 14) O =
                        Some (Bw', tt)).
  { intros A HA. destruct (HMOD A HA) as (Bw & HMA).
    rewrite (ent_model _ _ _ _ HSZ) in HMA. rewrite ECD in HMA. cbv beta iota in HMA.
    rewrite EIN in HMA. cbv beta iota in HMA. unfold SPEC_OK in HMA. cbn [negb Z.eqb] in HMA.
    revert HMA.
    destruct (LLVMFuzzerTestOneInput_loop_m (Z.to_nat OPS_MAX) timg_ubsan B25 A D (ent_c10 D) O)
      as [[B26 u2]|] eqn:EL; intros HMA; [|discriminate HMA].
    exists B26. destruct u2. rewrite <- EC10. exact EL. }
  rewrite EB24 in EIN.
  assert (GF : g_fail_next B25 <= 1).
  { rewrite (ent_init_gfn _ _ _ _ _ _ _ _ _ (ent_Wt_len _ _ _ (ent_W14_len _ _ (ent_W6_len _ _ LB1))) EIN).
    rewrite ent_Wt_gfn by exact (ent_W14_len _ _ (ent_W6_len _ _ LB1)). lia. }
  (* the walk *)
  apply (ent_cfg data regs0 m _ lo B B1 o n flags F fc ms1 _ MCPY CDEF HNUM Hfl ECD HS1).
  intros ms2 HS2.
  apply (ent_lad data D regs0 m _ lo B1 o n flags F fc ms2 _ I HNUM Hfl Ho Hn Hon HDAT HD0 HS2).
  intros ms3 HS3.
  apply (ent_tl1 data D regs0 m _ lo B1 o n flags F fc ms3 B25 0 _ MCPY MSET INIT HNUM Hfl Ho Hn Hon LB1 EIN HS3).
  intros ms4 HS4.
  exact (ent_tl2 data D regs0 m _ lo o n B25 F fc ms4 HNUM Ho Hn Hon HDAT HD0 RR GF HLOOP HS4).
Qed.
