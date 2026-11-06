(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymExec3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2.

Module SXA.

Inductive vinstr : Type :=
| VReal (i : instr)
| VCas (rd rt rd2 rs1 rs2 : reg)
| VAmo (op : amoop) (wd : awidth) (rd rs1 rs2 : reg).

Definition reg_eqb (a b : reg) : bool := bv_eqb a b.

Definition fetch_dec (segs : list Segment) (p : Z) : option instr :=
  match fetch_word segs (Z_to_bv 64 p) with
  | None => None
  | Some w => if is_ecall w then None else
      match decode_any w with
      | Some (i, 4%Z) => Some i
      | _ => None
      end
  end.

Definition vdecode (segs : list Segment) (p : Z) : option vinstr :=
  match fetch_dec segs p with
  | None => None
  | Some (Lr AW aq rl rd rs1) =>
      match fetch_dec segs (p + 4), fetch_dec segs (p + 8) with
      | Some (Branch BC_NE rd' rt imm1), Some (Sc AW aq' rl' rd2 rs1' rs2) =>
          if (reg_eqb rd' rd && reg_eqb rs1' rs1 && negb (reg_eqb rd rs1) && negb (reg_eqb rd 0))%bool
          then Some (VCas rd rt rd2 rs1 rs2) else None
      | _, _ => None
      end
  | Some (Lr _ _ _ _ _) => None
  | Some (Sc _ _ _ _ _ _) => None
  | Some (Amo op wd aq rl rd rs1 rs2) =>
      match op with
      | AMO_ADD | AMO_SWAP => Some (VAmo op wd rd rs1 rs2)
      | _ => None
      end
  | Some i => Some (VReal i)
  end.

Inductive rres1 := R1Hit (v : expr) (scs : list sidecond) (hints : list bool) | R1Stop.

Definition lookup1 (segs : list Segment) (fk : list kentry) (ss : sym_state)
           (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : rres1 :=
  match log_lookup fk (s_log ss) rb rk n sx hints acc with
  | LStuck => R1Stop
  | LHit v scs hints' => R1Hit v scs hints'
  | LMiss scs hints' =>
      match know_lookupA fk segs (s_know ss) rb rk n sx hints' scs with
      | LHit v scs' hints'' => R1Hit v scs' hints''
      | _ => R1Stop
      end
  end.

Fixpoint gather (segs : list Segment) (fk : list kentry) (ss : sym_state)
         (rb : expr) (rk : Z) (k : nat) (hints : list bool) (acc : list sidecond)
  : option (list Z * list sidecond * list bool) :=
  match k with
  | O => Some ([], acc, hints)
  | S k' =>
      match lookup1 segs fk ss rb rk 1 false hints acc with
      | R1Hit v acc' hints' =>
          match conc_expr fk v with
          | ELit b =>
              match gather segs fk ss rb (rk + 1) k' hints' acc' with
              | Some (bs, acc'', hints'') => Some ((b mod 256)%Z :: bs, acc'', hints'')
              | None => None
              end
          | _ => None
          end
      | R1Stop => None
      end
  end.

Fixpoint zbytes_le (bs : list Z) : Z :=
  match bs with [] => 0 | b :: r => Z.lor b (Z.shiftl (zbytes_le r) 8) end.

Definition extz' (sx : bool) (n : nat) (u : Z) : Z :=
  if sx then bv_swrap (8 * N.of_nat n) u else u.

Inductive rres := ROk (v : expr) (scs : list sidecond) (scr : scripts) | RStop.

Definition resolve_load (segs : list Segment) (fk : list kentry) (ss : sym_state)
           (a : saddr) (n : nat) (sx : bool) (scr : scripts) : rres :=
  match lookup1 segs fk ss (a_base a) (a_off a) n sx (sc_hints scr) [] with
  | R1Hit v scs hints => ROk (extK fk v) (flat_sc fk a n ++ scs) (SCR (sc_dirs scr) (sc_reads scr) hints)
  | R1Stop =>
      match gather segs fk ss (a_base a) (a_off a) n (sc_hints scr) [] with
      | Some (bs, scs, hints) =>
          ROk (ELit (bv_unsigned (Z_to_bv 64 (extz' sx n (zbytes_le bs)))))
              (flat_sc fk a n ++ scs) (SCR (sc_dirs scr) (sc_reads scr) hints)
      | None => RStop
      end
  end.

Fixpoint kalign_of (kn : list kentry) (e : expr) : Z :=
  match kn with
  | [] => 1
  | KAlign e' m :: rest => if expr_eqb e e' then m else kalign_of rest e
  | _ :: rest => kalign_of rest e
  end.

Definition aligned_dec (fk : list kentry) (a : saddr) (m : Z) : bool :=
  match a_base a with
  | ELit z => Z.eqb ((z + a_off a) mod m) 0
  | b => let k := kalign_of fk b in (Z.ltb 0 k && Z.eqb (k mod m) 0 && Z.eqb (a_off a mod m) 0)%bool
  end.

Definition awidth_bytes (wd : awidth) : nat := match wd with AW => 4%nat | AD => 8%nat end.

Definition amo_store_expr (op : amoop) (wd : awidth) (v s : expr) : option expr :=
  match wd, op with
  | AW, AMO_SWAP => Some s
  | AW, AMO_ADD => Some (mkAluw ALU_ADD v s)
  | AD, AMO_SWAP => Some s
  | AD, AMO_ADD => Some (mkAlu ALU_ADD v s)
  | _, _ => None
  end.

Definition vstep (segs : list Segment) (vi : vinstr) (ss : sym_state) (scr : scripts) : stepres :=
  match vi with
  | VReal i =>
      match sym_step segs i ss scr with
      | SOk ss' scs scr' => SOk ss' scs scr'
      | SStop =>

          match i with
          | Load sz sx rd rs imm =>
              let fk := facts_of (s_know ss) in
              let n := msize_bytes sz in
              let sx' := match sz with SZ8 => false | _ => sx end in
              let a := to_saddrK fk (sr_get (s_regs ss) rs) (bv_signed imm) in
              match resolve_load segs fk ss a n sx' scr with
              | ROk v scs scr' => SOk (sset ss rd v (s_pc ss + 4)) scs scr'
              | RStop => SStop
              end
          | _ => SStop
          end
      end
  | VCas rd rt rd2 rs1 rs2 =>
      let fk := facts_of (s_know ss) in
      let p := s_pc ss in
      let a := to_saddrK fk (sr_get (s_regs ss) rs1) 0 in
      if negb (aligned_dec fk a 4) then SStop else
      match resolve_load segs fk ss a 4 true scr with
      | RStop => SStop
      | ROk v scs1 scr1 =>
          let sr1 := sr_upd (s_regs ss) (ridx rd) v in
          match decide_branch fk BC_NE (sr_get sr1 rd) (sr_get sr1 rt) with
          | Some false =>
              let ss3 := SS (p + 12)
                            (if bv_eqb rd2 0 then sr1 else sr_upd sr1 (ridx rd2) (ELit 0))
                            (SE a 4 (sr_get sr1 rs2) :: s_log ss) (s_know ss) (s_next ss) in
              SOk ss3 (scs1 ++ storeok_sc fk a 4) scr1
          | _ => SStop
          end
      end
  | VAmo op wd rd rs1 rs2 =>
      let fk := facts_of (s_know ss) in
      let p := s_pc ss in
      let n := awidth_bytes wd in
      let a := to_saddrK fk (sr_get (s_regs ss) rs1) 0 in
      if negb (aligned_dec fk a (Z.of_nat n)) then SStop else
      match resolve_load segs fk ss a n (match wd with AW => true | AD => false end) scr with
      | RStop => SStop
      | ROk v scs1 scr1 =>
          match amo_store_expr op wd v (sr_get (s_regs ss) rs2) with
          | None => SStop
          | Some w =>
              let sr1 := if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v in
              SOk (SS (p + 4) sr1 (SE a n w :: s_log ss) (s_know ss) (s_next ss))
                  (scs1 ++ storeok_sc fk a n) scr1
          end
      end
  end.

Section Exec.
Variable segs : list Segment.

Fixpoint sym_execA (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                   (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => (ss, acc, scr)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, acc, scr) else
      match vdecode segs (s_pc ss) with
      | None => (ss, acc, scr)
      | Some vi =>
          match vstep segs vi ss scr with
          | SOk ss' scs scr' => sym_execA f false stops scr' ss' (sc_add scs acc)
          | SStop => (ss, acc, scr)
          end
      end
  end.
End Exec.
End SXA.
