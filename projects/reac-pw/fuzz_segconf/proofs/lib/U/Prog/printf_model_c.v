From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import printf_facts_c.
Import ListNotations.
Open Scope Z_scope.

(** The unit-level argument predicate of the printf_model contracts (vsnprintf_c.v, snprintf_m_c.v): the
    printf_facts_c.v vocabulary of snprintf_contract, widened from pf_arg to the full model's parg. A %s argument
    (PA_s) and a %d / %c argument (PA_i) are exactly pf_arg_ok's APtr / AInt cases; PA_u is an unsigned int
    (%u, %x) passed in the low 32 bits of its slot; PA_ull a 64-bit unsigned (%llu, %zu) passed as the whole
    slot. No floating-point argument (PA_g) is admitted: the snf sink leaves them unreachable. *)
Definition pm_arg_ok (m : word -> option byte) (S lo D n : Z) (r : word) (a : Printf_model.parg) : Prop :=
  match a with
  | Printf_model.PA_s s => pf_arg_ok m S lo D n r (APtr s)
  | Printf_model.PA_i v => pf_arg_ok m S lo D n r (AInt v)
  | Printf_model.PA_u u => 0 <= u < 2^32 /\ bv_unsigned r mod 2^32 = u
  | Printf_model.PA_ull u => bv_unsigned r = u
  | Printf_model.PA_g _ => False
  end.

Fixpoint pm_args_ok (m : word -> option byte) (S lo D n : Z) (rs : list word) (args : list Printf_model.parg)
    : Prop :=
  match args, rs with
  | [], _ => True
  | a :: args', r :: rs' => pm_arg_ok m S lo D n r a /\ pm_args_ok m S lo D n rs' args'
  | _ :: _, [] => False
  end.
