(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr ZBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Classifier.
Context (segs : list Segment) {AI : AsanImg segs}.
Local Notation insn_at := (insn_at segs).
Local Notation report_at := (report_at segs).

(* [comment removed for export] *)
Definition jthru (q : Z) : Z :=
  match insn_at q with
  | Some (Jal rd imm) => if Z.eqb (zr rd) 0 then q + i21 imm else q
  | _ => q
  end.

Definition slow_at2 (pc t : Z) : option (Z * Z * Z) :=
  match insn_at pc with
  | Some (OpImm ALU_AND u a i7) =>
      if Z.eqb (i12 i7) 7 && negb (Z.eqb (zr u) 0) then
        match insn_at (pc + 4) with
        | Some (OpImm ALU_ADD u1 u2 k) =>
            if Z.eqb (zr u1) (zr u) && Z.eqb (zr u2) (zr u) then
              match insn_at (pc + 8) with
              | Some (Branch c r1 r2 off) =>
                  if Z.eqb (zr r1) (zr u) && Z.eqb (zr r2) t then
                    match c with
                    | BC_LT => if report_at (pc + 12) then Some (zr u, i12 k + 1, pc + 8 + i13 off) else None
                    | BC_GE => if report_at (pc + 8 + i13 off) then Some (zr u, i12 k + 1, jthru (pc + 12)) else None
                    | _ => None
                    end
                  else None
              | _ => None
              end
            else None
        | Some (Branch c r1 r2 off) =>
            if Z.eqb (zr r1) (zr u) && Z.eqb (zr r2) t then
              match c with
              | BC_LT => if report_at (pc + 8) then Some (zr u, 1, pc + 4 + i13 off) else None
              | BC_GE => if report_at (pc + 4 + i13 off) then Some (zr u, 1, jthru (pc + 8)) else None
              | _ => None
              end
            else None
        | _ => None
        end
      else None
  | _ => None
  end.

Definition chk_at2 (pc : Z) : option achk :=
  match insn_at (pc - 4), insn_at pc with
  | Some (Load SZ1 sg t x i0), Some (Branch c t1 z off) =>
      if Z.eqb (zr t1) (zr t) && Z.eqb (zr z) 0 && Z.eqb (i12 i0) 0 && negb (Z.eqb (zr t) 0) then
        let T := pc + i13 off in let F := pc + 4 in
        match c with
        | BC_NE => if report_at T then Some (AChk (zr t) sg 0 8 F false)
                   else match slow_at2 T (zr t) with
                        | Some (u, s, J) => if Z.eqb J F then Some (AChk (zr t) sg u s F false) else None
                        | None => None
                        end
        | BC_EQ => if report_at F then Some (AChk (zr t) sg 0 8 T true)
                   else match slow_at2 F (zr t) with
                        | Some (u, s, J) => if Z.eqb J T then Some (AChk (zr t) sg u s T true) else None
                        | None => None
                        end
        | _ => None
        end
      else None
  | _, _ => None
  end.
Definition shload_at2 (pc : Z) : option (Z * achk) :=
  match insn_at pc, chk_at2 (pc + 4) with
  | Some (Load SZ1 _ t x _), Some c => Some (zr x, c)
  | _, _ => None
  end.
Definition addsh_at2 (pc : Z) : bool :=
  match insn_at pc, shload_at2 (pc + 4) with
  | Some (Op ALU_ADD d _ _), Some (x, _) => Z.eqb (zr d) x
  | _, _ => false
  end.
Definition srli_at2 (pc : Z) : option Z :=
  match insn_at pc with
  | Some (ShiftImm ALU_SRL t a sh) => if Z.eqb (bv_unsigned sh) 3 && addsh_at2 (pc + 4) then Some (zr a) else None
  | _ => None
  end.
Definition amat_at2 (pc : Z) : bool :=
  match insn_at pc, srli_at2 (pc + 4) with
  | Some (OpImm ALU_ADD d _ _), Some a => Z.eqb (zr d) a && negb (Z.eqb a 2)
  | Some (Op ALU_ADD d _ _), Some a => Z.eqb (zr d) a && negb (Z.eqb a 2)
  | _, _ => false
  end.
Definition kind_at2 (pc : Z) : akind :=
  match chk_at2 pc with
  | Some c => AKchk c
  | None =>
  match shload_at2 pc with
  | Some (_, c) => AKshload c
  | None =>
      if addsh_at2 pc then AKfeed
      else match srli_at2 pc with
      | Some _ => AKfeed
      | None =>
      if amat_at2 pc then AKfeed
      else if shb1_at segs pc then AKfeed
      else if shb1_at segs (pc - 4) then AKgot
      else if shb1_at segs (pc - 8) then (match insn_at pc with Some (Load SZ8 _ _ _ lo) => if Z.eqb (i12 lo) 0 then AKshb else AK0 | _ => AK0 end)
      else if farcall_at segs pc then AKfeed
      else AK0
      end
  end end.
End Classifier.

Ltac ab_kind2 :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => eval vm_compute in (@kind_at2 segs _ pc)
  end.
Ltac show_kind2 := let k := ab_kind2 in idtac k.

(* [comment removed for export] *)
Ltac ab_j_opt J :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | J => idtac
      | _ => let i := eval vm_compute in (insn_at segs pc) in
             lazymatch i with Some (Jal _ _) => Step.step | _ => idtac end
      end
  end.

Ltac ApATac.ab_join t u J ABok ::=
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv ?m ?ro) =>
    let pt := eval vm_compute in (bv_key (Z_to_bv 5 t)) in
    let pu := eval vm_compute in (bv_key (Z_to_bv 5 u)) in
    eapply (evt_cut segs (fun ms => exists vt vu : word, ms = MS (tset pu vu (tset pt vt R)) F (Z_to_bv 64 J) fc rv m ro));
    [ lazymatch type of ABok with
      | absh_ok ?b ?X ?s =>
          let k := fresh "k" in let K1 := fresh "K1" in let K2 := fresh "K2" in let Es := fresh "Es" in let Ez := fresh "Ez" in
          destruct (absh_cases b X s ABok) as [-> | (k & K1 & K2 & Es & Ez)];
          [ rewrite ?zxb_z8, ?sxb_z8; Step.step; try first [if_false | if_true]; ab_at_join
          | rewrite ?Es, ?Ez; clear Es Ez;
            ab_branch;                                   (* [comment removed for export] *)
            Step.step; ab_addi_opt;                      (* [comment removed for export] *)
            rewrite ?ab_land7w, ?ab_land7u;
            ab_branch;                                   (* [comment removed for export] *)
            ab_j_opt J;                                  (* [comment removed for export] *)
            ab_at_join ]
      end
    | let ms1 := fresh "ms" in let vt := fresh "abt" in let vu := fresh "abu" in
      intros ms1 (vt & vu & ->); map_cbv_set; clear ABok ]
  end.

Ltac ApATac.ab1 ::=
  let k := ab_kind2 in
  lazymatch k with
  | AK0 => fail
  | AKfeed => Step.step
  | AKshload (AChk _ _ _ ?s _ _) => ab_shload s
  | AKchk (AChk ?t _ ?u ?s ?J _) => ab_chk t u s J
  | AKgot => first [ Step.step | ashb; Step.step ]
  | AKshb => first [ Step.step | ashb; Step.step ]
  end.
