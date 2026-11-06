(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Uint63.
From Stdlib Require Export PrimString.   (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint kc_tok (fuel : nat) (s : string) (i : int) (cur : Z) (neg inn : bool) (acc : list Z) : list Z :=
  let fin := if neg then Z.opp cur else cur in
  match fuel with
  | O => rev' (if inn then fin :: acc else acc)
  | S f =>
      let c := Uint63.to_Z (PrimString.get s i) in
      if Z.eqb c 32 then kc_tok f s (Uint63.succ i) 0 false false (if inn then fin :: acc else acc)
      else if Z.eqb c 45 then kc_tok f s (Uint63.succ i) 0 true false acc
      else kc_tok f s (Uint63.succ i) (cur * 10 + (c - 48)) neg true acc
  end.
Definition kc_tokens (s : string) : list Z :=
  kc_tok (Z.to_nat (Uint63.to_Z (PrimString.length s))) s 0%uint63 0 false false [].

Definition kc_alu (z : Z) : aluop :=
  match z with 0 => ALU_ADD | 1 => ALU_SUB | 2 => ALU_SLL | 3 => ALU_SLT | 4 => ALU_SLTU | 5 => ALU_XOR | 6 => ALU_SRL | 7 => ALU_SRA | 8 => ALU_OR | _ => ALU_AND end.
Definition kc_mul (z : Z) : mulop :=
  match z with 0 => M_MUL | 1 => M_MULH | 2 => M_MULHSU | 3 => M_MULHU | 4 => M_DIV | 5 => M_DIVU | 6 => M_REM | _ => M_REMU end.
Definition kc_b (z : Z) : bool := negb (Z.eqb z 0).

Fixpoint kc_expr (fuel : nat) (ts : list Z) : option (expr * list Z) :=
  match fuel with
  | O => None
  | S f =>
      match ts with
      | 0 :: z :: r => Some (ELit z, r)
      | 1 :: n :: r => Some (EVar (Z.to_nat n), r)
      | 2 :: op :: r => match kc_expr f r with Some (a, r1) => match kc_expr f r1 with Some (b, r2) => Some (EAlu (kc_alu op) a b, r2) | None => None end | None => None end
      | 3 :: op :: r => match kc_expr f r with Some (a, r1) => match kc_expr f r1 with Some (b, r2) => Some (EAluw (kc_alu op) a b, r2) | None => None end | None => None end
      | 4 :: op :: r => match kc_expr f r with Some (a, r1) => match kc_expr f r1 with Some (b, r2) => Some (EMd (kc_mul op) a b, r2) | None => None end | None => None end
      | 5 :: op :: r => match kc_expr f r with Some (a, r1) => match kc_expr f r1 with Some (b, r2) => Some (EMdw (kc_mul op) a b, r2) | None => None end | None => None end
      | 6 :: sx :: lo :: n :: r => match kc_expr f r with Some (a, r1) => Some (EExt (kc_b sx) (Z.to_nat lo) (Z.to_nat n) a, r1) | None => None end
      | 7 :: sx :: k :: i :: n :: r => Some (EBlob (kc_b sx) (Z.to_nat k) i (Z.to_nat n), r)
      | _ => None
      end
  end.
Definition kc_sa (fuel : nat) (ts : list Z) : option (saddr * list Z) :=
  match kc_expr fuel ts with Some (b, o :: r) => Some (SA b o, r) | _ => None end.
Fixpoint kc_exprs (fuel : nat) (cnt : nat) (ts : list Z) : option (list expr * list Z) :=
  match cnt with
  | O => Some ([], ts)
  | S c => match kc_expr fuel ts with
           | Some (e, r) => match kc_exprs fuel c r with Some (es, r2) => Some (e :: es, r2) | None => None end
           | None => None
           end
  end.
Definition kc_entry (fuel : nat) (ts : list Z) : option (kentry * list Z) :=
  match ts with
  | 10 :: r => match kc_sa fuel r with Some (a, w :: r1) => match kc_expr fuel r1 with Some (v, r2) => Some (KWord a (Z.to_nat w) v, r2) | None => None end | _ => None end
  | 11 :: r => match kc_sa fuel r with Some (a, r1) => match kc_expr fuel r1 with Some (n, r2) => Some (KZero a n, r2) | None => None end | None => None end
  | 12 :: r => match kc_sa fuel r with Some (a, r1) => match kc_expr fuel r1 with Some (n, k :: r2) => Some (KBlob a n (Z.to_nat k), r2) | _ => None end | None => None end
  | 13 :: lo :: hi :: r => Some (KImg lo hi, r)
  | 14 :: r => match kc_expr fuel r with Some (e, m :: r1) => Some (KAlign e m, r1) | _ => None end
  | 15 :: r => match kc_expr fuel r with Some (e, lo :: hi :: r1) => Some (KRange e lo hi, r1) | _ => None end
  | 16 :: r => match kc_sa fuel r with Some (a, r1) => match kc_expr fuel r1 with Some (n, r2) => Some (KWr a n, r2) | None => None end | None => None end
  | 17 :: r => match kc_sa fuel r with
               | Some (a1, r1) => match kc_expr fuel r1 with
                                  | Some (n1, r2) => match kc_sa fuel r2 with
                                                     | Some (a2, r3) => match kc_expr fuel r3 with Some (n2, r4) => Some (KDisj a1 n1 a2 n2, r4) | None => None end
                                                     | None => None end
                                  | None => None end
               | None => None end
  | 18 :: r => match kc_sa fuel r with Some (a, r1) => match kc_expr fuel r1 with Some (n, c :: r2) => Some (KFill a n c, r2) | _ => None end | None => None end
  | 19 :: r => match kc_sa fuel r with Some (a, r1) => match kc_expr fuel r1 with Some (n, r2) => Some (KUnk a n, r2) | None => None end | None => None end
  | 20 :: id :: cnt :: r => match kc_exprs fuel (Z.to_nat cnt) r with Some (es, r1) => Some (KInv (Z.to_nat id) es, r1) | None => None end
  | _ => None
  end.
(* [comment removed for export] *)
Fixpoint kc_list (fuel : nat) (efuel : nat) (ts : list Z) (acc : list kentry) : list kentry :=
  match fuel with
  | O => rev' acc
  | S f =>
      match ts with
      | [] => rev' acc
      | _ => match kc_entry efuel ts with
             | Some (K, r) => kc_list f efuel r (K :: acc)
             | None => rev' (KImg 1 0 :: acc)
             end
      end
  end.
Definition dec_kn (s : string) : list kentry :=
  let ts := kc_tokens s in kc_list (List.length ts) (List.length ts) ts [].
(* [comment removed for export] *)
Definition dec_exprs (s : string) : list expr :=
  let ts := kc_tokens s in
  (fix go (fuel : nat) (ts : list Z) (acc : list expr) : list expr :=
     match fuel with
     | O => rev' acc
     | S f => match ts with [] => rev' acc | _ => match kc_expr (List.length ts) ts with Some (e, r) => go f r (e :: acc) | None => rev' (ELit (-1) :: acc) end end
     end) (List.length ts) ts [].

(* [comment removed for export] *)
Definition dec_pairs (s : string) : list (expr * expr) :=
  let ts := kc_tokens s in
  (fix go (fuel : nat) (ts : list Z) (acc : list (expr * expr)) : list (expr * expr) :=
     match fuel with
     | O => rev' acc
     | S f => match ts with
              | [] => rev' acc
              | _ => match kc_expr (List.length ts) ts with
                     | Some (a, r) => match kc_expr (List.length r) r with Some (b, r2) => go f r2 ((a, b) :: acc) | None => rev' ((ELit (-1), ELit (-1)) :: acc) end
                     | None => rev' ((ELit (-1), ELit (-1)) :: acc)
                     end
              end
     end) (List.length ts) ts [].
Definition kc_kind (z : Z) : mkind :=
  match z with 0 => KRW | 1 => KRWLAZY | 2 => KNONE | 3 => KNONELAZY | 4 => KFOG | _ => KHOLE end.
Definition dec_amaps (s : string) : list amap :=
  let ts := kc_tokens s in
  (fix go (fuel : nat) (ts : list Z) (acc : list amap) : list amap :=
     match fuel with
     | O => rev' acc
     | S f => match ts with
              | [] => rev' acc
              | k :: r0 => match kc_expr (List.length r0) r0 with
                           | Some (b, r) => match kc_expr (List.length r) r with Some (n, r2) => go f r2 (AM b n (kc_kind k) :: acc) | None => rev' (AM (ELit (-1)) (ELit 0) KHOLE :: acc) end
                           | None => rev' (AM (ELit (-1)) (ELit 0) KHOLE :: acc)
                           end
              end
     end) (List.length ts) ts [].
