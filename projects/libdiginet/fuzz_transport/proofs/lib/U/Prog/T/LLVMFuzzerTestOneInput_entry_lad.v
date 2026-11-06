(* LLVMFuzzerTestOneInput (ubsan) 0x13854 .. 0x138d4 for every cursor length: the cases n = 0 .. 13 and n >= 14
   (U/Prog/T/LLVMFuzzerTestOneInput_entry_l{a,b,c}.v). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require Import TWorld TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.U.Prog.T Require Import TContract
  LLVMFuzzerTestOneInput_lh LLVMFuzzerTestOneInput_entry_m LLVMFuzzerTestOneInput_entry_d
  LLVMFuzzerTestOneInput_entry_lt LLVMFuzzerTestOneInput_entry_la LLVMFuzzerTestOneInput_entry_lb
  LLVMFuzzerTestOneInput_entry_lc.
Import ListNotations.
Open Scope Z_scope.

Lemma ent_lad : ent_lad_stmt (fun _ => True).
Proof.
  intros data D regs0 m0 Sp lo B1 o n flags F fc ms Q _ HNUM HFL Ho Hn Hon HDAT HD0 HS K.
  assert (C : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
              n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ 14 <= n) by lia.
  destruct C as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]].
  - exact (lad_n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n9 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_n13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
  - exact (lad_ge14 _ _ _ _ _ _ _ _ _ _ _ _ _ _ E HNUM HFL Ho Hn Hon HDAT HD0 HS K).
Qed.
