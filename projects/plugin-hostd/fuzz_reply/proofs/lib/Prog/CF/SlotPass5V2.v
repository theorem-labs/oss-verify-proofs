From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SlotPass5V SlotPass5V2old SlotPass5V2out SlotPass5V2chain.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.

Theorem p5v_old : p5v_old_S.
Proof. exact p5v_old_pf. Qed.

Theorem p5v_out : p5v_out_S.
Proof. exact p5v_out_pf. Qed.

Theorem p5v_chain : p5v_chain_S.
Proof. exact p5v_chain_pf. Qed.
