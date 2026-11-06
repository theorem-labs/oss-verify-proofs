(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanNodesLib.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRehashModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Module RHN.

(* [comment removed for export] *)
Record rtab := RT { r_entry : Z; r_map : Z }.

(* [comment removed for export] *)
Definition rh_fresh : list nat := [5; 6; 7; 11; 13; 14; 15; 16; 17; 28; 29; 30]%nat.
Definition NRH : nat := 12.

Fixpoint zmem (x : Z) (l : list Z) : bool := match l with [] => false | y :: r => if Z.eqb x y then true else zmem x r end.
Fixpoint znodup (l : list Z) : bool := match l with [] => true | x :: r => if zmem x r then false else znodup r end.

Section Node.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable T : rtab.

(* [comment removed for export] *)
Fixpoint read_keys (k : list kentry) (b : expr) (o : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match kreadZ segs k b o 8, read_keys k b (o + 32) n' with
            | Some key, Some r => Some (key :: r)
            | _, _ => None
            end
  end.

Fixpoint key_facts (b : expr) (o : Z) (ks : list Z) : list kentry :=
  match ks with
  | [] => []
  | key :: r => KWord (SA b o) 8 (ELit key) :: key_facts b (o + 32) r
  end.

(* [comment removed for export] *)
Fixpoint havs (k : list kentry) (rs : list (expr * Z * Z)) : list kentry :=
  match rs with
  | [] => k
  | (b, o, n) :: rest => havs (kn_havocM (match b with ELit 0 => kimg_cut k o n | _ => k end) b o (ELit n)) rest
  end.

(* [comment removed for export] *)
Fixpoint collect (k : list kentry) (nb : expr) : list (Z * Z) :=
  match k with
  | [] => []
  | KWord (SA b o) w (ELit v) :: r => if (Nat.eqb w 8 && expr_eqb b nb)%bool then (o, v mod two64) :: collect r nb else collect r nb
  | _ :: r => collect r nb
  end.
Fixpoint alookup (l : list (Z * Z)) (o : Z) : option Z :=
  match l with [] => None | (o', v) :: r => if Z.eqb o o' then Some v else alookup r o end.
Fixpoint keys_of (l : list (Z * Z)) (o : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match alookup l o, keys_of l (o + 32) n' with Some v, Some r => Some (v :: r) | _, _ => None end
  end.

(* [comment removed for export] *)
Definition ro_cov (k : list kentry) : bool :=
  forallb (fun s => seg_writable s || img_cov k (Z.of_N (seg_base s)) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool segs.

Definition lit1 (e : expr) : option Z := match e with ELit z => Some (z mod two64) | _ => None end.

Definition node_rehash (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (r_entry T)) then None else
  let eo := reg cs 11 in let eend := reg cs 12 in let sp := reg cs 2 in let es := eaddz sp (-16) in
  let '(ob, oo) := split_lit eo in let '(sb, so) := split_lit es in
  match lit1 (reg cs 10), lit1 (reg cs 1), kread8e segs k (ELit 0) (r_map T), kreadZ segs k (ELit 0) (r_map T + 8) 4,
        kreadZ segs k (ELit 0) (r_map T + 12) 4, kreadZ segs k (ELit 0) (r_map T + 16) 4,
        xlo k (esub eend eo), xhi k (esub eend eo) with
  | Some mapv, Some ra, Some B, Some _, Some _, Some N, Some dlo, Some dhi =>
    let No := dlo / 32 in
    let '(nb, no) := split_lit B in
    match keys_of (collect k ob) oo (Z.to_nat No), xlo k eo, xhi k eo, xlo k B, xhi k B, xlo k sp, xhi k sp with
    | Some olds, Some olo, Some ohi, Some blo, Some bhi, Some splo, Some sphi =>
      match RHM.rehash0 N olds with
      | Some (ks', pl) =>
        if (fresh_ok nx0 cs && ro_cov k && AP.expr_vars_lt (nxt cs) B && Z.eqb mapv (r_map T) && Z.eqb dlo dhi && Z.eqb (dlo mod 32) 0 && Z.leb 1 No && Z.leb No (2 ^ 20)
            && Z.leb 64 N && Z.leb N (2 ^ 20) && Z.eqb (Z.land (N - 1) N) 0
            && Z.leb 0 ra && Z.ltb ra (2 ^ 47) && Z.eqb (ra mod 4) 0
            && znodup (List.filter RHM.is_live olds) && forallb (fun key => Z.leb 0 key && Z.ltb key (2 ^ 64)) olds
            && Z.ltb 0 olo && Z.leb (ohi + 32 * No) (2 ^ 47) && Z.leb 3 (ealign k eo) && LBN.ovl_ok A k eo (ELit (32 * No))
            && Z.ltb 0 blo && Z.leb (bhi + 32 * N) (2 ^ 47) && Z.leb 3 (ealign k B) && LBN.ovl_ok A k B (ELit (32 * N))
            && Z.leb 4 (ealign k sp) && Z.leb (img_hi A + 16) splo && Z.ltb sphi (2 ^ 47) && LBN.ovl_ok A k es (ELit 16)
            && ranges_apart_x k ob oo (ELit (32 * No)) nb no (ELit (32 * N))
            && ranges_apart_x k sb so (ELit 16) ob oo (ELit (32 * No))
            && ranges_apart_x k sb so (ELit 16) nb no (ELit (32 * N))
            && Z.leb (img_lo A) (r_map T) && Z.leb (r_map T + 20) (img_hi A) && kwritable_x k k (ELit 0) (r_map T) (ELit 20))%bool
        then
          let nx := nxt cs in
          let sr' := sr_fresh (s_regs (a_ss cs)) rh_fresh nx in
          let kh := havs k [(nb, no, 32 * N); (ELit 0, r_map T + 8, 8); (sb, so, 16)] in
          let k' := KWord (SA (ELit 0) (r_map T + 8)) 4 (ELit (Z.of_nat (length pl))) :: KWord (SA (ELit 0) (r_map T + 12)) 4 (ELit 0)
                    :: key_facts nb no ks' ++ kh in
          Some (with_ss cs (mk_ss ra sr' k' (nx + NRH)))
        else None
      | None => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _, _, _, _, _, _, _ => None
  end.

End Node.
End RHN.
