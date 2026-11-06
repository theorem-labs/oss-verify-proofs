From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells codec_main_inv LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** The epilogue (0x149ac-0x149e8): a0 = 0, the 13 saves reloaded, the frame released, ret. *)
Lemma codec_main_exit : S_exit.
Proof.
  unfold S_exit, exit_ok, st.
  intros e HE ra' t0' t1' t2' x8 x9 a0' a1' a2' a3' a4' a5' a6' a7' x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
         t3' t4' t5' t6' cs m1 HS FR (SV & ST & MU & WM & HMI).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  destruct HE as (_ & _ & _ & HLO & _). unfold LLVM_CODEC_STACK in HLO.
  pose proof ST as [Hlo0 _].
  unfold saved in SV.
  do 15 zstep.
  eapply stk_release in FR; [ | exact ST | lia ].
  rewrite HS in FR.
  replace (bv_unsigned (e_sp e) + -400 + Z.of_nat 296) with (bv_unsigned (e_sp e) + -104) in FR by lia.
  eapply stk_release in SV; [ | exact FR | lia ].
  cbn [cells_size csize Nat.add] in SV.
  replace (bv_unsigned (e_sp e) + -104 + Z.of_nat 104) with (bv_unsigned (e_sp e)) in SV by lia.
  clear ST FR.
  zstep.
  finish.
Qed.
