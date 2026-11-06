(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import APC.
Open Scope Z_scope.

Module DPN.
Definition PUT_ENTRY : Z := 0xf546c.    
Definition put_entry_of (IH : Z) : Z := if Z.eqb IH 0x608000 then 0x74d04 else 0x74cf4.
(* [comment removed for export] *)
Definition PUT_REGS : list nat := [10; 5; 6; 11; 12; 13; 14; 15; 16]%nat.
(* [comment removed for export] *)
Definition SCRATCH : Z := 224.

Section WithSegs.
Variable segs : list Segment.
Variable nx0 : N.
(* [comment removed for export] *)
Variables DP SB IH : Z.

Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.

(* [comment removed for export] *)
Definition tok_lits (args : list expr) : option (Z * Z * Z * Z * Z) :=
  match args with
  | [_; _; ELit nc; ELit fc; ELit dp; ELit sb; ELit ih] => Some (nc, fc, dp, sb, ih)
  | _ => None
  end.

Fixpoint find_token (k : list kentry) : option (list (saddr * expr) * list expr * Z * Z * Z) :=
  match k with
  | [] => None
  | KPriv O rs args kk :: rest =>
      match rs, tok_lits args with
      | [_; _; _; _], Some (nc, fc, dp, sb, ih) =>
          if (Z.eqb dp DP && Z.eqb sb SB && Z.eqb ih IH)%bool then Some (rs, args, nc, fc, kk)
          else find_token rest
      | _, _ => find_token rest
      end
  | _ :: rest => find_token rest
  end.

(* [comment removed for export] *)
Definition drop_tokens (k : list kentry) : list kentry := List.filter (fun K => negb (kpriv_b K)) k.

(* [comment removed for export] *)
Fixpoint havoc_rs (k : list kentry) (rs : list (saddr * expr)) : list kentry :=
  match rs with
  | [] => k
  | r :: rest => havoc_rs (kn_havoc k (a_base (fst r)) (a_off (fst r)) (snd r)) rest
  end.

(* [comment removed for export] *)
Definition apart_rs (k : list kentry) (b : expr) (off : Z) (n : expr) (rs : list (saddr * expr)) : bool :=
  forallb (fun r : saddr * expr => ranges_apart_x k b off n (a_base (fst r)) (a_off (fst r)) (snd r)) rs.

(* [comment removed for export] *)
Definition put_tests (cs : acs)
  : option (list bool * (list (saddr * expr) * list expr * Z * Z * Z) * Z * (expr * Z)) :=
  let k := kn cs in
  match reg cs 1, find_token k with
  | ELit ret, Some ((rs, args, nc, fc, kk) as tok) =>
      let (sb, so) := split_lit (reg cs 2) in
      let (tb, to) := split_lit (reg cs 10) in
      match xlo k (reg cs 2), xlo k (reg cs 10), xhi k (reg cs 10), xlo k (reg cs 11), xhi k (reg cs 11) with
      | Some slo, Some tlo, Some thi, Some zlo, Some zhi =>
          Some ([ Z.eqb (pc cs) (put_entry_of IH)
                ; Z.leb 0 ret; Z.ltb ret two64; Z.eqb (ret mod 2) 0
                ; Z.leb 1 kk
                ; (Z.leb 2 nc && Z.leb nc 65536)%bool; (Z.leb 257 fc && Z.leb fc 1048576)%bool
                ; Z.leb (two32z + SCRATCH) slo
                ; kwritable k k sb (so - SCRATCH) SCRATCH
                ; Z.leb two32z tlo; Z.ltb (thi + 8 * zhi) two64
                ; Z.leb 1 zlo; Z.leb zhi 255
                ; kwritable k k tb to (8 * zhi)
                ; ranges_apart_x k tb to (ELit (8 * zhi)) sb (so - SCRATCH) (ELit SCRATCH)
                ; apart_rs k sb (so - SCRATCH) (ELit SCRATCH) rs
                ; apart_rs k tb to (ELit (8 * zhi)) rs
                ; expr_vars_lt (nxt cs) sb; kentry_vars_lt (nxt cs) (KPriv 0 rs args kk)
                ; fresh_ok nx0 cs ]%bool, tok, ret, (sb, so))
      | _, _, _, _, _ => None
      end
  | _, _ => None
  end.

Definition put_kn (k : list kentry) (sb : expr) (so : Z) (rs : list (saddr * expr)) (args : list expr)
           (kk nc : Z) (nx : N) : list kentry :=
  KPriv 0 rs args (kk - 1)
  :: KRange (EVar nx) 0 (nc - 1)
  :: havoc_rs (drop_tokens k) ((SA sb (so - SCRATCH), ELit SCRATCH) :: rs).

Definition node_put (cs : acs) (args0 : list expr) : option acs :=
  match args0 with
  | [] =>
    match put_tests cs with
    | Some (ts, (rs, args, nc, fc, kk), ret, (sb, so)) =>
        if forallb (fun b : bool => b) ts then
          let nx := nxt cs in
          Some (with_ss cs (mk_ss ret (sr_fresh (s_regs (a_ss cs)) PUT_REGS nx)
                                  (put_kn (kn cs) sb so rs args kk nc nx) (nx + 9)%N))
        else None
    | None => None
    end
  | _ => None
  end.

Definition diag_put (cs : acs) (args0 : list expr) : nat :=
  match put_tests cs with Some (ts, _, _, _) => first_false 1 ts | None => 100%nat end.

(* [comment removed for export] *)
Definition TABSZ : Z := 4194304.

(* [comment removed for export] *)
Definition kreadn (k : list kentry) (b : expr) (off : Z) (n : nat) : option expr :=
  match know_lookup segs k b off n false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.
Definition klit (k : list kentry) (b : expr) (off : Z) (n : nat) : option Z :=
  match kreadn k b off n with Some (ELit z) => Some z | _ => None end.

(* [comment removed for export] *)
Definition tab_pieces (k : list kentry) : list (Z * Z * option Z) :=
  flat_map (fun K => match K with
    | KImg lo hi => if (Z.ltb lo (DP + TABSZ) && Z.ltb DP hi)%bool then [(Z.max lo DP, Z.min hi (DP + TABSZ), @None Z)] else []
    | KWord (SA (ELit 0) o) w (ELit v) =>
        if (Nat.eqb w 4 && Z.leb DP o && Z.leb (o + 4) (DP + TABSZ))%bool then [(o, o + 4, Some v)] else []
    | _ => []
    end) k.
Definition piece_ok (n0 : Z) (p : Z * Z * option Z) : bool :=
  match p with (s, e, v) =>
    (Z.eqb ((s - DP) mod 4) 0 && Z.eqb ((e - DP) mod 4) 0 && Z.ltb s e &&
     match v with None => true | Some v => Z.leb 0 v && Z.leb v n0 end)%bool
  end.
(* [comment removed for export] *)
Fixpoint reach (ps : list (Z * Z * option Z)) (cur : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb (DP + TABSZ) cur then true else
           match find (fun p : Z * Z * option Z => match p with (s, e, _) => (Z.leb s cur && Z.ltb cur e)%bool end) ps with
           | Some (_, e, _) => reach ps e f
           | None => false
           end
  end.
Definition tab_ok (k : list kentry) (n0 : Z) : bool :=
  let ps := tab_pieces k in (forallb (piece_ok n0) ps && reach ps DP (S (length ps)))%bool.

(* [comment removed for export] *)
Definition zids (n0 : Z) : list Z := map Z.of_nat (seq 1 (Z.to_nat n0)).
Definition node_okb (k : list kentry) (eB : expr) (id : Z) : bool :=
  match klit k eB (16 * id + 8) 4, kreadn k eB (16 * id) 8 with
  | Some l, Some _ => (Z.leb 0 l && Z.ltb l id)%bool
  | _, _ => false
  end.

(* [comment removed for export] *)
Definition init_cells (cs : acs) : option (Z * expr * Z * expr * Z) :=
  let k := kn cs in
  match klit k (ELit 0) (DP + 4194304) 4, kreadn k (ELit 0) (DP + 4194320) 8,
        klit k (ELit 0) SB 8, kreadn k (ELit 0) (SB + 16) 8, klit k (ELit 0) (SB + 24) 4 with
  | Some n0, Some eB, Some tf0, Some eP, Some st0 => Some (n0, eB, tf0, eP, st0)
  | _, _, _, _, _ => None
  end.

Definition init_tests (cs : acs) (n0 : Z) (eB : expr) (tf0 : Z) (eP : expr) (st0 : Z) (nc fc k0 : Z) : option (list bool) :=
  let k := kn cs in
  match xlo k eB, xhi k eB, xlo k eP, xhi k eP with
  | Some blo, Some bhi, Some plo, Some phi =>
      Some [ (Z.leb 2 nc && Z.leb nc 65536)%bool; (Z.leb 257 fc && Z.leb fc 1048576)%bool
           ; Z.leb 0 k0
           ; (Z.leb 0 n0 && Z.ltb (n0 + k0) nc)%bool
           ; (Z.leb 0 tf0 && Z.leb (tf0 + 257 * k0) fc)%bool
           ; (Z.leb 0 st0 && Z.ltb (st0 + 257 * k0) 1048576)%bool
           ; Z.leb IH blo; Z.ltb (bhi + 16 * 65536) two64; Z.leb IH plo; Z.ltb (phi + 8 * 1048576) two64
           ; ranges_apart_x k eB 0 (ELit (16 * nc)) eP 0 (ELit (8 * fc))
           ; kwritable k k eB 0 (16 * nc); kwritable k k eP 0 (8 * fc)
           ; tab_ok k n0
           ; forallb (node_okb k eB) (zids n0) ]%bool
  | _, _, _, _ => None
  end.

Definition init_rs (eB eP : expr) (nc fc : Z) : list (saddr * expr) :=
  [(SA (ELit 0) DP, ELit 4194328); (SA eB 0, ELit (16 * nc)); (SA (ELit 0) SB, ELit 28); (SA eP 0, ELit (8 * fc))].

Definition init_args (args : list expr) : option (Z * Z * Z) :=
  match args with
  | [ELit nc; ELit fc; ELit k0] => Some (nc, fc, k0)
  | _ => None
  end.

Definition node_init (cs : acs) (args : list expr) : option acs :=
  match init_args args, init_cells cs with
  | Some (nc, fc, k0), Some (n0, eB, tf0, eP, st0) =>
      match init_tests cs n0 eB tf0 eP st0 nc fc k0 with
      | Some ts => if forallb (fun b : bool => b) ts
                   then Some (add_kn cs [KPriv 0 (init_rs eB eP nc fc) [eB; eP; ELit nc; ELit fc; ELit DP; ELit SB; ELit IH] k0])
                   else None
      | None => None
      end
  | _, _ => None
  end.

Definition diag_init (cs : acs) (args : list expr) : nat :=
  match init_args args, init_cells cs with
  | Some (nc, fc, k0), Some (n0, eB, tf0, eP, st0) =>
      match init_tests cs n0 eB tf0 eP st0 nc fc k0 with Some ts => first_false 1 ts | None => 99%nat end
  | Some _, None => 100%nat
  | None, _ => 101%nat
  end.

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 113 then node_put cs args
  else if Nat.eqb id 114 then node_init cs args
  else None.
End WithSegs.
End DPN.
