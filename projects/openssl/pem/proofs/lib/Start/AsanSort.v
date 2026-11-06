(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanSortModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module HSN.

(* [comment removed for export] *)
Definition hs_fresh : list nat := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28]%nat.
Definition NHS : nat := 11.

Definition lit1 (e : expr) : option Z := match e with ELit z => Some (z mod two64) | _ => None end.

Section Node.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable entry : Z.

(* [comment removed for export] *)
Fixpoint read_recs (k : list kentry) (a : Z) (n : nat) : option (list HSM.rec) :=
  match n with
  | O => Some []
  | S n' => match kreadZ segs k (ELit 0) a 8, kreadZ segs k (ELit 0) (a + 8) 8, read_recs k (a + 16) n' with
            | Some w0, Some w1, Some r => Some ((w0, w1) :: r)
            | _, _, _ => None
            end
  end.

Fixpoint rec_facts (a : Z) (es : list HSM.rec) : list kentry :=
  match es with
  | [] => []
  | e :: r => KWord (SA (ELit 0) a) 8 (ELit (fst e)) :: KWord (SA (ELit 0) (a + 8)) 8 (ELit (snd e)) :: rec_facts (a + 16) r
  end.

Definition ro_cov (k : list kentry) : bool :=
  forallb (fun s => seg_writable s || img_cov k (Z.of_N (seg_base s)) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.

Definition node_isort (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match lit1 (reg cs 10), lit1 (reg cs 11), lit1 (reg cs 1) with
  | Some tab, Some n, Some ra =>
    match read_recs k tab (Z.to_nat n) with
    | Some es =>
      if (fresh_ok nx0 cs && ro_cov k && Z.leb 2 n && Z.leb n (2 ^ 16) && Z.ltb 0 tab && Z.leb (img_lo A) tab && Z.leb (tab + 16 * n) (img_hi A)
          && Z.eqb (tab mod 8) 0 && Z.leb 0 ra && Z.ltb ra (2 ^ 47) && Z.eqb (ra mod 2) 0
          && forallb (fun e => Z.leb 0 (fst e) && Z.ltb (fst e) (2 ^ 64) && Z.leb 0 (snd e) && Z.ltb (snd e) (2 ^ 64)) es
          && kwritable_x k k (ELit 0) tab (ELit (16 * n)))%bool
      then
        let nx := nxt cs in
        let sr' := sr_fresh (s_regs (a_ss cs)) hs_fresh nx in
        let kh := kn_havocM (kimg_cut k tab (16 * n)) (ELit 0) tab (ELit (16 * n)) in
        Some (with_ss cs (mk_ss ra sr' (rec_facts tab (HSM.hsort es) ++ kh) (nx + NHS)))
      else None
    | None => None
    end
  | _, _, _ => None
  end.

End Node.
End HSN.
