(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
PropExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX DrvKitA Jb0DrvEntry Jb0Drv_defs Jb0DrvRead Jb0DrvG_defs Jb0DrvC_defs Jb0DrvD_defs Jb0DrvLibL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import SX2. Import SX2S.
Open Scope Z_scope.
Definition IMG_PF_A : list (Z * Z) :=
[(0x10000, 0x136000); (0x138ac0, 0x138c98); (0x138d80, 0x139380); (0x65f090, 0x670a68); (0x670a70, 0x670ab8); (0x670ad4, 0x670ae8);
(0x670af0, 0x6912d8); (0x6916e8, 0x691f78); (0x691f80, 0x693000)].
Definition keep_pfA (so : Z) (bls : list (nat * Z)) (kn : list kentry) : list kentry := kn_keep 0 so 3232 bls [] [] IMG_PF_A IMG_RW_A kn.
Section FPX_1. Context {fx : PropExec.FPState}.
Definition PSO : Z := -288.
Definition knLr0A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLB1A.
Definition rPA := Eval vm_compute in runTA scr0 (SS 0xa7818 srLr0A [] knLr0A 134).
Definition srPA : list expr := Eval vm_compute in s_regs (fst (fst rPA)).
Definition knPA : list kentry := Eval vm_compute in kn_after rPA knLr0A.
Definition srQ0A : list expr := Eval vm_compute in sr_after_call_j srPA (map ridx c_kept) 134.
Definition knQ0A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knPA.
Definition rQtA := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xa7910 srQ0A [] knQ0A 166).
Definition rQfA := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xa7910 srQ0A [] knQ0A 166).
Definition summE (r : sym_state * list sidecond * scripts) := (s_pc (fst (fst r)), snd (fst r), s_next (fst (fst r)), length (s_log (fst (fst r)))).
Lemma loop_itinerary_okA :
summE rPA = (0x62d24, [], 134%nat, 10%nat)
/\ (nth 1 srPA (ELit 0), nth 2 srPA (ELit 0), nth 10 srPA (ELit 0), nth 11 srPA (ELit 0))
= (ELit 0xa7910, EAlu ALU_ADD (EVar 0) (ELit (-288)), ELit 85468, EAlu ALU_ADD (EVar 0) (ELit (-264)))
/\ forallb (fun K => existsb (kentry_eqb K) knPA)
[KWr (SA (EVar 0) (-8388608)) 8388608; KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1269760; KWord (SA (ELit 0) 6884096) 8 (EVar 3)] = true
/\ sr_vars_lt 134 srPA = true /\ kn_vars_lt 134 knPA = true
/\ (s_pc (fst (fst rQtA)), snd (fst rQtA), s_log (fst (fst rQtA))) = (0xa7804, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
/\ (s_pc (fst (fst rQfA)), snd (fst rQfA), s_log (fst (fst rQfA))) = (0x7918c, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
/\ (nth 1 (s_regs (fst (fst rQfA))) (ELit 0), nth 10 (s_regs (fst (fst rQfA))) (ELit 0)) = (ELit 0xa7844, EVar 83)
/\ kn_after rQtA knQ0A = knQ0A /\ kn_after rQfA knQ0A = knQ0A.
Proof. vm_compute. repeat split; reflexivity. Qed.
Definition knLH2A : list kentry := Eval vm_compute in filter (kentry_vars_lt 81) knQ0A.
Definition rLB2A := Eval vm_compute in runTA scr0 (SS 0xa7804 srLHA [] knLH2A 102).
Definition knLB2A : list kentry := Eval vm_compute in kn_after rLB2A knLH2A.
Definition knLr2A : list kentry := Eval vm_compute in keep_libA TSO LIBSTK [(48%nat, 65536)] [] knLB2A.
Definition rP2A := Eval vm_compute in runTA scr0 (SS 0xa7818 srLr0A [] knLr2A 134).
Definition knP2A : list kentry := Eval vm_compute in kn_after rP2A knLr2A.
Definition knQ2A : list kentry := Eval vm_compute in keep_pfA PSO [(48%nat, 65536)] knP2A.
Definition rSt2A := Eval vm_compute in runTA (SCR [true] [] []) (SS 0xa7910 srQ0A [] knLH2A 166).
Definition rSf2A := Eval vm_compute in runTA (SCR [false] [] []) (SS 0xa7910 srQ0A [] knLH2A 166).
Definition srSt2A : list expr := Eval vm_compute in s_regs (fst (fst rSt2A)).
Definition srSf2A : list expr := Eval vm_compute in s_regs (fst (fst rSf2A)).
Definition srF1A : list expr := Eval vm_compute in sr_after_call_j srSf2A (map ridx c_kept) 166.
Definition knF1A : list kentry := Eval vm_compute in keep_allocA TSO 4096 [(48%nat, 65536)] [] knLH2A.
Definition rT1A := Eval vm_compute in runTA scr0 (SS 0xa7844 srF1A [] knF1A 198).
Definition srM1A : list expr := Eval vm_compute in s_regs (fst (fst rT1A)).
Definition knM1A : list kentry := Eval vm_compute in kn_after rT1A knF1A.
Definition rT2fA := Eval vm_compute in runA (SCR [false] [] []) (SS 0xa75f0 srM1A [] knM1A 198).
Definition rT2tA := Eval vm_compute in runA (SCR [true] [] []) (SS 0xa75f0 srM1A [] knM1A 198).
Definition srF2A : list expr := Eval vm_compute in sr_after_call_j (s_regs (fst (fst rT2fA))) (map ridx c_kept) 198.
Definition knF2A : list kentry := Eval vm_compute in keep_allocA MSO 4096 [] [] (kn_after rT2fA knM1A).
Definition rT3A := Eval vm_compute in runA scr0 (SS 0xa7678 srF2A [] knF2A 230).
Lemma loop2_itinerary_okA :
ksubl_b knQ0A knLH2A = true /\ ksubl_b knQ2A knLH2A = true /\ kn_vars_lt 81 knLH2A = true
/\ summE rLB2A = summE rLB1A /\ s_regs (fst (fst rLB2A)) = srLBA /\ s_log (fst (fst rLB2A)) = [SE (SA (ELit 0) 0x66f094) 1 (ELit 1)]
/\ summE rP2A = (0x62d24, [], 134%nat, 10%nat) /\ s_regs (fst (fst rP2A)) = srPA
/\ forallb (fun K => existsb (kentry_eqb K) knP2A)
[KWr (SA (EVar 0) (-8388608)) 8388608; KWord (SA (EVar 0) (-264)) 8 (ELit 0); KImg 65536 1269760; KWord (SA (ELit 0) 6884096) 8 (EVar 3)] = true
/\ (s_pc (fst (fst rSt2A)), snd (fst rSt2A), s_log (fst (fst rSt2A))) = (0xa7804, [SCBr true BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
/\ (s_pc (fst (fst rSf2A)), snd (fst rSf2A), s_log (fst (fst rSf2A))) = (0x7918c, [SCBr false BC_NE (EAluw ALU_ADD (EVar 81) (ELit (-1))) (ELit 0)], [])
/\ (nth 1 srSf2A (ELit 0), nth 10 srSf2A (ELit 0), nth 21 srSt2A (ELit 0)) = (ELit 0xa7844, EVar 83, EAluw ALU_ADD (EVar 81) (ELit (-1)))
/\ kn_after rSt2A knLH2A = knLH2A /\ kn_after rSf2A knLH2A = knLH2A.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma tail_itinerary_okA :
summE rT1A = (0xa75f0, [], 198%nat, 0%nat) /\ nth 2 srM1A (ELit 0) = EAlu ALU_ADD (EVar 0) (ELit (-128))
/\ (s_pc (fst (fst rT2fA)), snd (fst rT2fA), s_log (fst (fst rT2fA))) = (0x7918c, [SCBr false BC_LT (EVar 74) (ELit 0)], [])
/\ (s_pc (fst (fst rT2tA)), snd (fst rT2tA), s_log (fst (fst rT2tA))) = (0x7918c, [SCBr true BC_LT (EVar 74) (ELit 0)], [])
/\ (nth 1 (s_regs (fst (fst rT2fA))) (ELit 0), nth 10 (s_regs (fst (fst rT2fA))) (ELit 0)) = (ELit 0xa7678, EVar 48)
/\ (nth 1 (s_regs (fst (fst rT2tA))) (ELit 0), nth 10 (s_regs (fst (fst rT2tA))) (ELit 0)) = (ELit 0xa7678, EVar 48)
/\ sr_after_call_j (s_regs (fst (fst rT2tA))) (map ridx c_kept) 198 = srF2A
/\ ksubl_b (keep_allocA MSO 4096 [] [] (kn_after rT2tA knM1A)) knF2A = true
/\ summE rT3A = (0x11575c, [], 230%nat, 0%nat)
/\ (nth 1 (s_regs (fst (fst rT3A))) (ELit 0), nth 2 (s_regs (fst (fst rT3A))) (ELit 0), nth 4 (s_regs (fst (fst rT3A))) (ELit 0), nth 10 (s_regs (fst (fst rT3A))) (ELit 0))
= (ELit 1134488, EAlu ALU_ADD (EVar 0) (ELit (-48)), ELit 6752960, ELit 0).
Proof. vm_compute. repeat split; reflexivity. Qed.
End FPX_1.
