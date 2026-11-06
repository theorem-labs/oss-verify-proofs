(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxHandoff FxDrive.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv BrMem BrPure BrLedger BrMain.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Infer.
Variable IM : fimage.
Variable F : fstate.
Variable L : fledger.
Variable CS : CAP.acs.
Variable XT : list (int * AX2.lin).   (* [comment removed for export] *)
Variable TEQ : list teq.     (* [comment removed for export] *)

Local Notation M := (f_mem F).

Definition st : Type := (vtab * ttab)%type.
Definition teq_has (t : int) : bool :=
  match teq_get TEQ t with Some _ => true | None => existsb (fun p => (fst p =? t)%uint63) XT end.

Definition vt_has (VT : vtab) (v : nat) : bool := match vt_get VT v with Some _ => true | None => false end.
Definition tl_has (TL : ttab) (t : int) : bool := match tl_get TL t with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition infer_stack (pins : vtab) : option (int * Z * st) :=
  match FxState.rget F 2 with
  | FV t w =>
      let l := AX2.lin_of (nth 2 (AX2.s_regs (CAP.a_ss CS)) (AX2.ELit 0)) in
      if is_plain t && terms_eqb (snd l) (snd (AX2.lin_of CAP.e_spw)) then
        let tc := wZ w - fst l in
        Some (t, tc, ((0%nat, VDiv t tc 32768 0) :: (10%nat, VDiv t tc 4096 32768) :: (6%nat, VDiv t tc 16 4096) :: pins,
                      [(t, TD tc [(32768, 0%nat); (4096, 10%nat); (16, 6%nat)])]))
      else None
  end.

(* [comment removed for export] *)
Definition infer_amap (s : st) (m : CAP.amap) (e : fent) : st :=
  let '(t, off, _) := e in
  let l := AX2.lin_of (CAP.am_base m) in
  match snd l with
  | [(4096, AX2.EVar v)] =>
      if vt_has (fst s) v || tl_has (snd s) t then s
      else let c := to_Z off - fst l in ((v, VDiv t c 4096 0) :: fst s, (t, TD c [(4096, v)]) :: snd s)
  | _ => s
  end.

Fixpoint infer_maps (s : st) (ms : list CAP.amap) (es : list fent) : st :=
  match ms, es with
  | m :: ms', e :: es' => infer_maps (infer_amap s m e) ms' es'
  | _, _ => s
  end.

(* [comment removed for export] *)
Definition add_opaque (s : st) (v : nat) (fv : fval) : st :=
  if vt_has (fst s) v then s
  else match fv with
       | FV t w =>
           if is_plain t && negb (t =? 0)%uint63 && (wZ w =? 0) && negb (teq_has t)
              && negb (tl_has (snd s) t) && match iget t M with None => true | Some _ => false end
           then ((v, VDiv t 0 1 0) :: fst s, (t, TD 0 [(1, v)]) :: snd s)
           else ((v, VVal fv) :: fst s, snd s)
       end.

(* [comment removed for export] *)
Fixpoint ins_desc (dx : Z * nat) (l : list (Z * nat)) : list (Z * nat) :=
  match l with
  | [] => [dx]
  | h :: r => if fst h <? fst dx then dx :: l else h :: ins_desc dx r
  end.

Fixpoint terms_vars (ts : list (Z * AX2.expr)) : option (list (Z * nat)) :=
  match ts with
  | [] => Some []
  | (d, AX2.EVar x) :: r => match terms_vars r with Some l => Some (ins_desc (d, x) l) | None => None end
  | _ => None
  end.

Fixpoint digit_defs (t : int) (m : Z) (ds : list (Z * nat)) : vtab :=
  match ds with
  | [] => []
  | (d, x) :: r => (x, VDiv t 0 d m) :: digit_defs t d r
  end.

Definition add_digits (s : st) (e : AX2.expr) (fv : fval) : st :=
  match fv with
  | FV t w =>
      let l := AX2.lin_of e in
      match terms_vars (snd l) with
      | Some ds =>
          if (fst l =? 0) && (1 <? Z.of_nat (List.length ds)) && is_plain t && negb (t =? 0)%uint63 && (wZ w =? 0)
             && negb (teq_has t) && negb (tl_has (snd s) t) && match iget t M with None => true | Some _ => false end
             && forallb (fun dx => negb (vt_has (fst s) (snd dx))) ds
          then (digit_defs t 0 ds ++ fst s, (t, TD 0 ds) :: snd s)
          else s
      | None => s
      end
  end.

Definition infer_reg (s : st) (i : nat) : st :=
  match nth i (AX2.s_regs (CAP.a_ss CS)) (AX2.ELit 0) with
  | AX2.EVar v => add_opaque s v (FxState.rget F (of_Z (Z.of_nat i)))
  | AX2.ELit _ => s
  | e => add_digits s e (FxState.rget F (of_Z (Z.of_nat i)))
  end.

Definition first_sv (sls : slots) (bi : Z) : option fval :=
  match sget (of_Z bi) sls with SV fv _ => Some fv | _ => None end.

Definition infer_kentry (s : st) (k : AX2.kentry) : st :=
  match k with
  | AX2.KWord a w (AX2.EVar v) =>
      if vt_has (fst s) v then s
      else match aview (fst s) M (snd s) XT a with
           | Some (t, o) =>
               match (if Nat.eqb w 8 then cell_lookup IM M t o else None) with
               | Some fv => add_opaque s v fv
               | None => match slots_lookup IM M t o with
                         | Some sls =>
                             match first_sv sls (o mod 8) with
                             | Some fv =>
                                 (* [comment removed for export] *)
                                 if (Nat.leb w 4 && (vkind (vtag fv) =? 2)%uint63)%bool
                                 then add_opaque s v (FV (vbase (vtag fv)) (vw fv))
                                 else add_opaque s v fv
                             | None => s
                             end
                         | None => s
                         end
               end
           | None => s
           end
  | AX2.KRange (AX2.EVar v) lo hi =>
      if vt_has (fst s) v || negb (lo =? hi) || negb (0 <=? lo) || negb (lo <? 2 ^ 64) then s
      else ((v, VVal (FV 0 (w_of_Z lo))) :: fst s, snd s)
  | _ => s
  end.

(* [comment removed for export] *)
Definition infer_consts (s : st) (k : AX2.kentry) : st :=
  match k with AX2.KRange (AX2.EVar _) _ _ => infer_kentry s k | _ => s end.

Definition br_infer (TB : list (int * Z * Z)) (ah : Z) (resid : list nat) (pins : vtab) : option bdata :=
  match infer_stack pins with
  | Some (ts, tc, s0) =>
      let sc := fold_left infer_consts (AX2.s_know (CAP.a_ss CS)) s0 in
      let s1 := infer_maps sc (CAP.a_maps CS) (fl_maps L) in
      let s2 := fold_left infer_reg (seq 1 31) s1 in
      let s3 := fold_left infer_kentry (AX2.s_know (CAP.a_ss CS)) s2 in
      Some (BD (fst s3) (snd s3) XT TEQ TB ts tc ah resid)
  | None => None
  end.

End Infer.

(* [comment removed for export] *)
Section Auto.
Variable IM : fimage.
Variable A : CAP.atable.
Variable keep : list int.
Variable KF : list FxHandoff.hfact.
Variable F : fstate.
Variable L : fledger.
Variable CS : CAP.acs.

Fixpoint fail_pos (bd : bdata) (i : nat) (kn : list AX2.kentry) : list nat :=
  match kn with
  | [] => []
  | k :: r => if kentry_check IM A bd keep KF F L k then fail_pos bd (Datatypes.S i) r else i :: fail_pos bd (Datatypes.S i) r
  end.

Definition br_infer_auto (XT : list (int * AX2.lin)) (TEQ : list teq) (TB : list (int * Z * Z)) (ah : Z) (pins : vtab) : option bdata :=
  match br_infer IM F L CS XT TEQ TB ah [] pins with
  | Some bd => Some (BD (bd_vt bd) (bd_tl bd) (bd_xt bd) (bd_teq bd) (bd_tb bd) (bd_ts bd) (bd_tc bd) (bd_ah bd)
                        (fail_pos bd 0 (AX2.s_know (CAP.a_ss CS))))
  | None => None
  end.
End Auto.

(* [comment removed for export] *)
Definition kit_pins : vtab :=
  [(1%nat, VVal (FV 0 (W64 0 1))); (3%nat, VVal (FV 0 (W64 0 0))); (7%nat, VVal (FV 0 (W64 0 0)))].
