(* op_read (fuzz_link.c:677-700), plain image: segment S2, from the return of text_buf (kc) to the
   call of text_buf (ac).

     0x13e50  mv   s3, a0      s3 = the kind buffer text_buf (kc) answered
     0x13e54  mv   a0, s5      a0 = ac
     0x13e58  jal  text_buf    ra = 0x13e5c

   No call and no store: the memory is the segment's start memory, so the footprint is empty.
   Every address is read from the plain image (link/ct/dis/plain/LLVMFuzzerTestOneInput.s). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC0Defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac ZBridge.
Import ListNotations.
Local Open Scope Z_scope.

Lemma c0_s2 : forall E i gp P N sel kc ac K kbs mbs gbs ms,
  lenv_ok E -> c0_ret_kc E i gp P N sel kc ac K kbs mbs gbs ms ->
  evt rsegs (eqv_cl (fun ms' => c0_cut_ac E i gp P N sel kc ac K kbs mbs gbs ms' /\
                                seg_fp (e_S E) (c0_hpK E kc K) (ms_mem ms) (ms_mem ms'))) ms.
Proof.
  intros E i gp P N sel kc ac K kbs mbs gbs ms _ HR.
  destruct HR as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6
                  & F & fc & m & wa & wk & -> & HF).
  cbn [ms_mem].
  unfold C0_RA_KC, wz.
  step. step. step.
  apply evt_done. apply c0_eqv_intro. split.
  - unfold c0_cut_ac.
    exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, s4, t3, t4, t5, t6, F, fc, m, wa, wk.
    split; [reflexivity | exact HF].
  - exists []. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x _ Hx. exfalso. apply Hx. exact I.
Qed.
