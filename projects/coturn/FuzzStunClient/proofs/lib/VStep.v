(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool String.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VAbs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive vresult : Type :=
| VR_next (succs : list vstate)
| VR_fail (msg : string).

(* [comment removed for export] *)
Definition rz (r : reg) : Z := bv_unsigned r.

(* [comment removed for export] *)
Definition bvs {n : N} (b : bv n) : Z :=
  match n with
  | 12%N => let z := bv_unsigned b in if Z.ltb z 2048 then z else z - 4096
  | 13%N => let z := bv_unsigned b in if Z.ltb z 4096 then z else z - 8192
  | 20%N => let z := bv_unsigned b in if Z.ltb z 524288 then z else z - 1048576
  | 21%N => let z := bv_unsigned b in if Z.ltb z 1048576 then z else z - 2097152
  | _ => bv_signed b
  end.

Lemma bvs_aux (n : N) (b : bv n) (h : Z) :
  bv_modulus n = 2 * h ->
  (let z := bv_unsigned b in if Z.ltb z h then z else z - 2 * h) = bv_signed b.
Proof.
  intros Hm. cbv zeta. pose proof (bv_unsigned_in_range _ b) as Hr. rewrite Hm in Hr.
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus. rewrite Hm.
  replace (2 * h / 2) with h by (rewrite Z.mul_comm, Z.div_mul; lia).
  destruct (Z.ltb_spec (bv_unsigned b) h).
  - rewrite Z.mod_small by lia. lia.
  - replace (bv_unsigned b + h) with ((bv_unsigned b - h) + 1 * (2 * h)) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma bvs_eq {n : N} (b : bv n) : bvs b = bv_signed b.
Proof.
  unfold bvs.
  destruct n as [|p]; [reflexivity|].
  repeat (first [ exact (bvs_aux _ b 2048 eq_refl) | exact (bvs_aux _ b 4096 eq_refl)
                | exact (bvs_aux _ b 524288 eq_refl) | exact (bvs_aux _ b 1048576 eq_refl)
                | reflexivity
                | match goal with q : positive |- _ => destruct q as [q|q|] end ]).
Qed.
#[global] Arguments bvs : simpl never.
#[global] Opaque bvs.

Definition npc_of (A : vstate) : Z := wrap64 (vs_pc A + 4).

(* [comment removed for export] *)
Definition finish (A : vstate) (rd : Z) (v : absval) : vstate :=
  set_pc (set_reg A rd v) (npc_of A).

Definition one (A : vstate) : vresult := VR_next [A].

(* [comment removed for export] *)
Definition box_empty_b (i : itv) : bool := itv_empty i.

Definition post_fork (A : vstate) (rd : Z) (r : ares) : vresult :=
  match r with
  | AR v A' => one (finish A' rd v)
  | AFork bsym v0 v1 blo A' =>
      let mk := fun (bv : Z) (v : absval) =>
        let nb := itv_meet (agetbox A' bsym) (Some bv, Some bv) in
        if itv_empty nb then []
        else
          let A1 := asetbox A' bsym nb in
          let A2 := trigger (trigger_fuel A1) A1 in
          [finish A2 rd v] in
      VR_next (mk blo v0 ++ mk (blo + 1) v1)
  end.

(* [comment removed for export] *)
Definition bcond_of (c : branch_cond) : bcond :=
  match c with
  | BC_EQ => (CK_eq, false) | BC_NE => (CK_eq, true)
  | BC_LT => (CK_lt, false) | BC_GE => (CK_lt, true)
  | BC_LTU => (CK_ltu, false) | BC_GEU => (CK_ltu, true)
  end.

Definition shop_of (op : aluop) : option shop :=
  match op with ALU_SLL => Some SH_sll | ALU_SRL => Some SH_srl | ALU_SRA => Some SH_sra | _ => None end.

Definition mop_of (op : mulop) : mop :=
  match op with
  | M_MUL => MO_mul | M_MULH => MO_mulh | M_MULHSU => MO_mulhsu | M_MULHU => MO_mulhu
  | M_DIV => MO_div | M_DIVU => MO_divu | M_REM => MO_rem | M_REMU => MO_remu
  end.

(* [comment removed for export] *)
Definition x_opimm (A : vstate) (op : aluop) (rd rs1 : Z) (imm : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  let a := get_reg A rs1 in
  match op with
  | ALU_ADD => one (finish A rd (match a with Some e => Some (anorm A (laddc e imm)) | None => None end))
  | ALU_SLT => let '(v, A') := do_slt A a (Some (lconst imm)) true in one (finish A' rd v)
  | ALU_SLTU => let '(v, A') := do_slt A a (Some (lconst (zm64 imm))) false in one (finish A' rd v)   (* [comment removed for export] *)
  | ALU_AND => post_fork A rd (do_and A a (Some (lconst imm)))
  | ALU_OR => post_fork A rd (do_or A a (Some (lconst imm)))
  | ALU_XOR => let '(v, A') := do_xor A a (Some (lconst imm)) in one (finish A' rd v)
  | _ => VR_fail "opimm: unexpected op"
  end.

Definition x_op (A : vstate) (op : aluop) (rd rs1 rs2 : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  let a := get_reg A rs1 in let b := get_reg A rs2 in
  match op with
  | ALU_ADD => one (finish A rd (match a, b with Some x, Some y => Some (anorm A (ladd x y)) | _, _ => None end))
  | ALU_SUB => one (finish A rd (match a, b with Some x, Some y => Some (anorm A (lsub x y)) | _, _ => None end))
  | ALU_SLT => let '(v, A') := do_slt A a b true in one (finish A' rd v)
  | ALU_SLTU => let '(v, A') := do_slt A a b false in one (finish A' rd v)
  | ALU_AND => post_fork A rd (do_and A a b)
  | ALU_OR => post_fork A rd (do_or A a b)
  | ALU_XOR => let '(v, A') := do_xor A a b in one (finish A' rd v)
  | ALU_SLL => let '(v, A') := do_shift A a b SH_sll 64 in one (finish A' rd v)
  | ALU_SRL => let '(v, A') := do_shift A a b SH_srl 64 in one (finish A' rd v)
  | ALU_SRA => let '(v, A') := do_shift A a b SH_sra 64 in one (finish A' rd v)
  end.

Definition x_shiftimm (A : vstate) (op : aluop) (rd rs1 : Z) (sh : Z) (width : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  match shop_of op with
  | Some sop => let '(v, A') := do_shift A (get_reg A rs1) (Some (lconst sh)) sop width in one (finish A' rd v)
  | None => VR_fail "shiftimm: unexpected op"
  end.

Definition x_opimm32 (A : vstate) (rd rs1 : Z) (imm : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  let a := match get_reg A rs1 with Some e => Some (laddc e imm) | None => None end in
  let '(v, A') := asext32 A a in one (finish A' rd v).

Definition x_op32 (A : vstate) (op : aluop) (rd rs1 rs2 : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  let a := get_reg A rs1 in let b := get_reg A rs2 in
  match op with
  | ALU_ADD => let '(v, A') := asext32 A (match a, b with Some x, Some y => Some (ladd x y) | _, _ => None end) in one (finish A' rd v)
  | ALU_SUB => let '(v, A') := asext32 A (match a, b with Some x, Some y => Some (lsub x y) | _, _ => None end) in one (finish A' rd v)
  | ALU_SLL => let '(v, A') := do_shift A a b SH_sll 32 in one (finish A' rd v)
  | ALU_SRL => let '(v, A') := do_shift A a b SH_srl 32 in one (finish A' rd v)
  | ALU_SRA => let '(v, A') := do_shift A a b SH_sra 32 in one (finish A' rd v)
  | _ => VR_fail "op32: unexpected op"
  end.

Definition x_mul (A : vstate) (op : mulop) (rd rs1 rs2 : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  match mop_of op with
  | MO_mulh | MO_mulhsu => one (finish A rd None)
  | mo => let '(v, A') := do_muldiv A mo (get_reg A rs1) (get_reg A rs2) 64 in one (finish A' rd v)
  end.

(* [comment removed for export] *)
Definition x_mul32 (A : vstate) (op : mulop) (rd rs1 rs2 : Z) : vresult :=
  if Z.eqb rd 0 then one (set_pc A (npc_of A)) else
  match mop_of op with
  | (MO_mul | MO_divu | MO_remu) as mo =>
      let '(a32, A1) := match get_reg A rs1 with Some e => azext A (Some e) 32 | None => (None, A) end in
      let '(b32, A2) := match get_reg A1 rs2 with Some e => azext A1 (Some e) 32 | None => (None, A1) end in
      let '(r, A3) := do_muldiv A2 mo a32 b32 32 in
      let '(v, A4) := asext32 A3 r in
      one (finish A4 rd v)
  | _ => let '(v, A') := afresh A s32range in one (finish A' rd v)
  end.

Definition x_branch (A : vstate) (c : branch_cond) (rs1 rs2 : Z) (imm : Z) : vresult :=
  let a := get_reg A rs1 in let b := get_reg A rs2 in
  let bc := bcond_of c in
  let tgt := wrap64 (vs_pc A + imm) in
  match eval_cond A bc a b with
  | Some true => one (set_pc A tgt)
  | Some false => one (set_pc A (npc_of A))
  | None =>
      let '(ok_t, At) := refine A bc a b in
      let '(ok_f, Af) := refine A (negc bc) a b in
      VR_next ((if ok_f then [set_pc Af (npc_of A)] else []) ++ (if ok_t then [set_pc At tgt] else []))
  end.

Definition x_jal (A : vstate) (rd : Z) (imm : Z) : vresult :=
  let tgt := wrap64 (vs_pc A + imm) in
  one (set_pc (set_reg A rd (Some (lconst (npc_of A)))) tgt).

(* [comment removed for export] *)
Definition x_jalr (A : vstate) (rd rs1 : Z) (imm : Z) : vresult :=
  match get_reg A rs1 with
  | None => VR_fail "jalr: Top target"
  | Some e =>
      let link := Some (lconst (npc_of A)) in
      if lin_is_const e then
        one (set_pc (set_reg A rd link) (wrap64 (Z.land (wrap64 (lc e) + imm) (-2))))
      else
        match enum_values A e with
        | None => VR_fail "jalr: unbounded target"
        | Some ts =>
            (* [comment removed for export] *)
            if negb (qwithin A e 0 M64) then VR_fail "jalr: target value not in word range" else
            VR_next (flat_map (fun t =>
                       let '(ok, A1) := assume_eq A e t in
                       if ok then [set_pc (set_reg A1 rd link) (wrap64 (Z.land (t + imm) (-2)))] else [])
                     ts)
        end
  end.

(* [comment removed for export] *)
Section WithMem.
  Variable x_load : vstate -> msize -> bool -> Z -> Z -> Z -> vresult.
  Variable x_store : vstate -> msize -> Z -> Z -> Z -> vresult.

  Definition vstep_core (A : vstate) (i : instr) : vresult :=
    match i with
    | Lui rd imm => if Z.eqb (rz rd) 0 then one (set_pc A (npc_of A))
                    else one (finish A (rz rd) (Some (lconst (Z.shiftl (bvs imm) 12))))   (* [comment removed for export] *)
    | Auipc rd imm => if Z.eqb (rz rd) 0 then one (set_pc A (npc_of A))
                      else one (finish A (rz rd) (Some (lconst (wrap64 (Z.shiftl (bvs imm) 12 + vs_pc A)))))
    | OpImm op rd rs1 imm => x_opimm A op (rz rd) (rz rs1) (bvs imm)
    | ShiftImm op rd rs1 sh => x_shiftimm A op (rz rd) (rz rs1) (bv_unsigned sh) 64
    | Op op rd rs1 rs2 => x_op A op (rz rd) (rz rs1) (rz rs2)
    | OpImm32 rd rs1 imm => x_opimm32 A (rz rd) (rz rs1) (bvs imm)
    | ShiftImm32 op rd rs1 sh => x_shiftimm A op (rz rd) (rz rs1) (bv_unsigned sh) 32
    | Op32 op rd rs1 rs2 => x_op32 A op (rz rd) (rz rs1) (rz rs2)
    | Mul op rd rs1 rs2 => x_mul A op (rz rd) (rz rs1) (rz rs2)
    | Mul32 op rd rs1 rs2 => x_mul32 A op (rz rd) (rz rs1) (rz rs2)
    | Branch c rs1 rs2 imm => x_branch A c (rz rs1) (rz rs2) (bvs imm)
    | Jal rd imm => x_jal A (rz rd) (bv_signed imm)
    | Jalr rd rs1 imm => x_jalr A (rz rd) (rz rs1) (bv_signed imm)
    | Load sz sg rd rs1 imm => x_load A sz sg (rz rd) (rz rs1) (bvs imm)
    | Store sz rs1 rs2 imm => x_store A sz (rz rs1) (rz rs2) (bvs imm)
    | Fence _ _ _ _ _ => VR_fail "fence: not supported (absent from F's closure)"
    | Ecall => VR_fail "TRAP: ecall"
    | Ebreak => VR_fail "TRAP: ebreak"
    | Csr _ _ _ _ | CsrI _ _ _ _ => VR_fail "TRAP: csr/unimp"
    | _ => VR_fail "unsupported instruction"
    end.
End WithMem.
