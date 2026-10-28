(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Step.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section ClassifierX.
Context (segs : list Segment) {AI : AsanImg segs}.

(* [comment removed for export] *)
Definition stub_at (pc : Z) : bool :=
  report_at segs pc
  || match insn_at segs pc with
     | Some (Load SZ8 _ rd _ _) => Z.eqb (zr rd) 10 && call_to segs (pc + 4) as_reports
     | _ => false
     end.
Definition report_atX (pc : Z) : bool :=
  stub_at pc
  || match insn_at segs pc with
     | Some (Jal rd off) => Z.eqb (zr rd) 0 && stub_at (pc + i21 off)
     | _ => false
     end.

(* [comment removed for export] *)
Definition skip_reload (pc : Z) : Z :=
  match insn_at segs pc with Some (Load SZ8 _ _ _ _) => pc + 4 | _ => pc end.
Definition skip_andi (pc : Z) : Z :=
  match insn_at segs pc with Some (OpImm ALU_AND _ _ i7) => if Z.eqb (i12 i7) 7 then pc + 4 else pc | _ => pc end.
Definition skip_addi (pc : Z) : Z * Z :=
  match insn_at segs pc with Some (OpImm ALU_ADD _ _ k) => (pc + 4, i12 k + 1) | _ => (pc, 1) end.
Definition slowX_at (pc t : Z) : option (Z * Z * Z) :=
  let p1 := skip_andi (skip_reload pc) in
  let '(p2, sz) := skip_addi p1 in
  match insn_at segs p2 with
  | Some (Branch c r1 r2 off) =>
      if negb (Z.eqb (zr r1) 0) && negb (Z.eqb (zr r1) t) && Z.eqb (zr r2) t then
        match c with
        | BC_LT => if report_atX (p2 + 4) then Some (zr r1, sz, p2 + i13 off) else None
        | BC_GE => if report_atX (p2 + i13 off) then Some (zr r1, sz, p2 + 4) else None
        | _ => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition chk_atX (pc : Z) : option achk :=
  match chk_at segs pc with
  | Some c => Some c
  | None =>
  match insn_at segs (pc - 4), insn_at segs pc with
  | Some (Load SZ1 sg t x i0), Some (Branch c t1 z off) =>
      if Z.eqb (zr t1) (zr t) && Z.eqb (zr z) 0 && Z.eqb (i12 i0) 0 && negb (Z.eqb (zr t) 0) then
        let T := pc + i13 off in let F := pc + 4 in
        match c with
        | BC_NE => if report_atX T then Some (AChk (zr t) sg 0 8 F false)
                   else match slowX_at T (zr t) with
                        | Some (u, s, J) => if Z.eqb J F then Some (AChk (zr t) sg u s F false) else None
                        | None => None
                        end
        | BC_EQ => if report_atX F then Some (AChk (zr t) sg 0 8 T true)
                   else match slowX_at F (zr t) with
                        | Some (u, s, J) => if Z.eqb J T then Some (AChk (zr t) sg u s T true) else None
                        | None => None
                        end
        | _ => None
        end
      else None
  | _, _ => None
  end end.

(* [comment removed for export] *)
Definition shload_atX (pc : Z) : option (Z * achk) :=
  match insn_at segs pc, chk_atX (pc + 4) with
  | Some (Load SZ1 _ t x _), Some c => Some (zr x, c)
  | _, _ => None
  end.
Definition addsh_atX (pc : Z) : bool :=
  match insn_at segs pc, shload_atX (pc + 4) with
  | Some (Op ALU_ADD d _ _), Some (x, _) => Z.eqb (zr d) x
  | _, _ => false
  end.
Definition srli_atX (pc : Z) : option Z :=
  match insn_at segs pc with
  | Some (ShiftImm ALU_SRL t a sh) => if Z.eqb (bv_unsigned sh) 3 && addsh_atX (pc + 4) then Some (zr a) else None
  | _ => None
  end.
Definition amat_atX (pc : Z) : bool :=
  match insn_at segs pc, srli_atX (pc + 4) with
  | Some (OpImm ALU_ADD d _ _), Some a => Z.eqb (zr d) a && negb (Z.eqb a 2)
  | Some (Op ALU_ADD d _ _), Some a => Z.eqb (zr d) a && negb (Z.eqb a 2)
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition kind_atX (pc : Z) : akind :=
  match kind_at segs pc with
  | AK0 =>
      match chk_atX pc with
      | Some c => AKchk c
      | None =>
      match shload_atX pc with
      | Some (_, c) => AKshload c
      | None =>
          if addsh_atX pc then AKfeed
          else match srli_atX pc with
          | Some _ => AKfeed
          | None => if amat_atX pc then AKfeed else AK0
          end
      end end
  | k => k
  end.
End ClassifierX.

(* [comment removed for export] *)
Ltac ab_kindX :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => eval vm_compute in (@kind_atX segs _ pc)
  end.
Ltac show_kindX := let k := ab_kindX in idtac k.
Ltac ab1X :=
  let k := ab_kindX in
  lazymatch k with
  | AK0 => fail
  | AKfeed => Step.step
  | AKshload (AChk _ _ _ ?s _ _) => ab_shload s
  | AKchk (AChk ?t _ ?u ?s ?J _) => ab_chk t u s J
  | AKgot => first [ Step.step | ashb; Step.step ]
  | AKshb => first [ Step.step | ashb; Step.step ]
  end.
Ltac abX := repeat ab1X.

(* [comment removed for export] *)
Ltac apre := ual; abX.
