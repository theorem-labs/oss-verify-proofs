(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes SysSpec StEqb.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepM StepS PlanS FXN SysSpec.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module SW.

Record layout := Layout {
  lw_rem : r5;
  lw_junkB : list r5
}.

Inductive bdesc : Type :=
| BLit (vs : list sv)
| BBlob (j : int) (off : Z) (len : sv).

Record went := WEnt { we_base : sv; we_len : sv; we_bytes : bdesc }.

Section Checker.
Variable segs : list Segment.
Variable it : itab.
Variable L : layout.

Definition VAR (n : int) : sv := VP n wzero.

Definition lit_int (v : sv) : option int :=
  match v with VL (W64 false i) => if PrimInt63.ltb i bit62i then Some i else None | _ => None end.

Definition lit_Z (v : sv) : option Z :=
  match v with VL w => Some (w2Z w) | _ => None end.

Definition load8 (st : sstate) (a : sv) : option sv :=
  match do_load segs st a 8%uint63 false with inl (Some v) => Some v | _ => None end.
Definition load1 (st : sstate) (a : sv) : option sv :=
  match do_load segs st a 1%uint63 false with inl (Some v) => Some v | _ => None end.
Definition store8 (st : sstate) (a : sv) (v : sv) : option sstate :=
  match do_store segs st a 8%uint63 v with inl st' => Some st' | _ => None end.

Definition addz (a : sv) (z : Z) : sv := sv_alu ALU_ADD a (VL (Z2w z)).

Definition known_ltu (fs : list fact) (a b : sv) : bool := dec_true (decide_ltu fs a b).
Definition known_leu (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu fs b a).
Definition known_eq (fs : list fact) (a b : sv) : bool := dec_true (decide_eq fs a b).

Definition TWO30 : sv := VL (wlit 1073741824%uint63).
Definition TWO47 : sv := VL (wlit 140737488355328%uint63).

Fixpoint omap {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: l' => match f x, omap f l' with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.
Fixpoint iotaZ (z : Z) (n : nat) : list Z := match n with O => [] | S n' => z :: iotaZ (z + 1) n' end.

Definition MAXLIT : Z := 512.
Definition bytes_desc (st : sstate) (base len : sv) : option bdesc :=
  match lit_Z len with
  | Some n =>
      if Z.leb n MAXLIT then
        match omap (fun i => load1 st (addz base i)) (iotaZ 0 (Z.to_nat n)) with
        | Some vs => Some (BLit vs)
        | None => None
        end
      else None
  | None =>
      match base with
      | VP k o =>
          match IMap.find k (s_regs st) with
          | Some (Region lo hi false (BGBlob j sh) IMap.Leaf) =>
              if negb (PrimInt63.eqb k 0%uint63)
                 && PrimInt63.eqb lo 0%uint63 && PrimInt63.eqb sh 0%uint63 && negb (wt o) && PrimInt63.ltb (wl o) bit62i
                 && known_leu (s_facts st) (sv_alu ALU_ADD (VL o) len) hi
                 && known_leu (s_facts st) len hi
              then Some (BBlob j (w2Z o) len) else None
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint svs_eqb (xs ys : list sv) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sv_eqb x y && svs_eqb xs' ys'
  | _, _ => false
  end.

Definition bdesc_eqb (a b : bdesc) : bool :=
  match a, b with
  | BLit xs, BLit ys => svs_eqb xs ys
  | BBlob j o l, BBlob j' o' l' => PrimInt63.eqb j j' && Z.eqb o o' && sv_eqb l l'
  | _, _ => false
  end.

Definition read_ent (st : sstate) (a : sv) : option (sv * sv) :=
  match load8 st a, load8 st (addz a 8) with Some b, Some l => Some (b, l) | _, _ => None end.

Definition read_ents (st : sstate) (c : nat) : option (list (sv * sv)) :=
  let a := getr st X11 in
  match c with
  | 1%nat => match read_ent st a with Some e => Some [e] | None => None end
  | 2%nat => match read_ent st a, read_ent st (addz a 16) with Some e0, Some e1 => Some [e0; e1] | _, _ => None end
  | _ => None
  end.

Definition lit_nat12 (v : sv) : option nat :=
  match lit_Z v with Some 1 => Some 1%nat | Some 2 => Some 2%nat | _ => None end.

Definition ent_ok (fs : list fact) (e : sv * sv) : bool :=
  known_ltu fs (fst e) TWO47 && known_leu fs (snd e) TWO30 && known_leu fs (sv_alu ALU_ADD (fst e) (snd e)) TWO47.

Definition total_of (es : list (sv * sv)) : sv :=
  match es with
  | [e] => snd e
  | [e0; e1] => sv_alu ALU_ADD (snd e0) (snd e1)
  | _ => VL wzero
  end.

Record ltpl := LT {
  lt_st : sstate;
  lt_c : nat;
  lt_vb : int; lt_vl : int; lt_vr : int;
  lt_junk : list (r5 * int);
  lt_n0 : int;
  lt_kc : int
}.

Definition xregs : list r5 :=
  [X1; X3; X4; X5; X6; X7; X8; X9; X10; X11; X12; X13; X14; X15; X16; X17; X18; X19; X20; X21; X22; X23; X24; X25; X26; X27; X28; X29; X30; X31].

Definition junk_regs (extra : list r5) (n0 : int) (st : sstate) : list r5 :=
  filter (fun r => (r5_eqb r X1 || existsb (r5_eqb r) extra || negb (sv_vars_below n0 (getr st r))) && negb (r5_eqb r (lw_rem L))) xregs.

Fixpoint set_junk (st : sstate) (js : list (r5 * int)) : sstate :=
  match js with [] => st | (r, n) :: js' => set_junk (setr st r (VAR n)) js' end.

Fixpoint number_from (n : int) (rs : list r5) : list (r5 * int) :=
  match rs with [] => [] | r :: rs' => (r, n) :: number_from (PrimInt63.add n 1%uint63) rs' end.

Definition with_facts (st : sstate) (fs : list fact) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) fs (s_ops st) (s_priv st) (s_next st).
Definition with_next (st : sstate) (n : int) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) n.

Definition foreign_granules (n0 : int) (r : region) : list int :=
  IMap.fold (fun g gr acc => if forallb (fun c => sv_vars_below n0 (c_v c)) (g_cells gr) then acc else g :: acc)
            (rg_cells r) [].

Definition forget_foreign_region (n0 : int) (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
         (fold_left (fun m g => IMap.add g (Gran true []) m) (foreign_granules n0 r) (rg_cells r)).
Definition forget_foreign (n0 : int) (st : sstate) : sstate :=
  setregs st (fold_left (fun R kr => IMap.add (fst kr) (forget_foreign_region n0 (snd kr)) R)
                        (IMap.elements (s_regs st)) (s_regs st)).

Definition lt_make (extra : list r5) (Y : sstate) (c : nat) (n0 fresh : int) : option ltpl :=
  let a := getr Y X11 in
  let vb := fresh in let vl := PrimInt63.add fresh 1%uint63 in let vr := PrimInt63.add fresh 2%uint63 in
  let js := number_from (PrimInt63.add fresh 3%uint63) (junk_regs extra n0 Y) in
  let nx := PrimInt63.add fresh (Uint63.of_Z (3 + Z.of_nat (length js))) in
  match store8 (forget_foreign n0 Y) a (VAR vb) with
  | None => None
  | Some Y1 =>
  match store8 Y1 (addz a 8) (VAR vl) with
  | None => None
  | Some Y2 =>
      let Y3 := set_junk (setr Y2 (lw_rem L) (VAR vr)) js in
      let site_facts := filter (fact_vars_below n0) (s_facts Y) in

      let Y4 := with_next (with_facts Y3 (FULe (VAR vr) TWO30 :: site_facts)) (PrimInt63.add nx 1%uint63) in
      Some (LT Y4 c vb vl vr js n0 nx)
  end end.

Definition id_subst (n0 : int) : list (int * sv) :=
  map (fun v => (v, VAR v)) (iota_int 0%uint63 (Z.to_nat (to_Z n0))).

Definition lt_subst (X : ltpl) (Y : sstate) : option subst :=
  let a := getr Y X11 in
  match load8 Y a, load8 Y (addz a 8) with
  | Some b, Some l =>
      Some (mk_subst (id_subst (lt_n0 X) ++ (lt_vb X, b) :: (lt_vl X, l) :: (lt_vr X, getr Y (lw_rem L))
                      :: map (fun rn => (snd rn, getr Y (fst rn))) (lt_junk X)))
  | _, _ => None
  end.

Definition sg_id_below (n0 : int) (sg : subst) : bool :=
  forallb (fun v => match IMap.find v sg with Some u => sv_eqb u (VAR v) | None => false end)
          (iota_int 0%uint63 (Z.to_nat (to_Z n0))).
Definition sg_binds (sg : subst) (v : int) (u : sv) : bool :=
  match IMap.find v sg with Some u' => sv_eqb u' u | None => false end.

Definition lt_arrives (src : ltpl) (sw : bool) (e1 : option (sv * sv)) (tgt : ltpl) (Y : sstate) : bool :=
  let a := getr Y X11 in
  let kc := VAR (lt_kc src) in
  match load8 Y a, load8 Y (addz a 8), lt_subst tgt Y with
  | Some b, Some l, Some sg =>
      entails Y (lt_st tgt) sg && sg_id_below (lt_n0 tgt) sg
      && sg_binds sg (lt_vb tgt) b && sg_binds sg (lt_vl tgt) l && sg_binds sg (lt_vr tgt) (getr Y (lw_rem L))
      && sv_eqb (getr Y (lw_rem L)) (sv_alu ALU_SUB (VAR (lt_vr src)) kc)
      && (if sw then
            match e1 with
            | Some (b1, l1) =>
                let dlt := sv_alu ALU_SUB kc (VAR (lt_vl src)) in
                sv_eqb b (sv_alu ALU_ADD b1 dlt) && sv_eqb l (sv_alu ALU_SUB l1 dlt)
            | None => false
            end
          else sv_eqb b (sv_alu ALU_ADD (VAR (lt_vb src)) kc) && sv_eqb l (sv_alu ALU_SUB (VAR (lt_vl src)) kc))
  | _, _, _ => false
  end.

Fixpoint explore (fuel : nat) (ra : int) (st : sstate) : option (list sstate * list sstate) :=
  match fuel with
  | O => None
  | S f =>
      match run segs it [ra] st with
      | SStop KStopPc st' => if PrimInt63.eqb (s_pc st') ra then Some ([st'], []) else None
      | SStop KEcall st' =>
          match IMap.find (s_pc st') it with Some IEcall => Some ([], [st']) | _ => None end
      | SStop (KBranch _ _ _ _) st' =>
          if negb (PrimInt63.ltb (s_pc st') bit62i) then None else
          match IMap.find (s_pc st') it with
          | Some (IBranch c rs1 rs2 off) =>
              match take_branch c (getr st' rs1) (getr st' rs2) off true st', take_branch c (getr st' rs1) (getr st' rs2) off false st' with
              | Some s1, Some s2 =>
                  match explore f ra s1, explore f ra s2 with
                  | Some (x1, y1), Some (x2, y2) => Some (x1 ++ x2, y1 ++ y2)
                  | _, _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition FUEL : nat := 6%nat.

Definition post_done (X : ltpl) : sstate :=
  let st := lt_st X in setpc (setr st X10 (VAR (lt_vr X))) (pc4 st).
Definition post_loop (X : ltpl) (sw : bool) : sstate :=
  let st := lt_st X in let kc := lt_kc X in
  let st1 := setpc (setr st X10 (VAR kc)) (pc4 st) in
  let casef := if sw then FULt (VAR (lt_vl X)) (VAR kc) else FULe (VAR kc) (VAR (lt_vl X)) in

  let remf := FULe (sv_alu ALU_SUB (VAR (lt_vr X)) (VAR kc)) TWO30 in
  with_next (with_facts st1 (FULe (VL (wlit 1%uint63)) (VAR kc) :: FULt (VAR kc) (VAR (lt_vr X)) :: FULt (VAR kc) TWO30 :: casef :: remf :: s_facts st1))
            (PrimInt63.add kc 1%uint63).

Definition sg_mem (n : int) (sg : subst) : bool := match IMap.find n sg with Some _ => true | None => false end.
Definition sg_bind (n : int) (u : sv) (sg : subst) : subst := if sg_mem n sg then sg else IMap.add n u sg.

Fixpoint msv (p t : sv) (sg : subst) {struct p} : subst :=
  match p with
  | VL _ => sg
  | VP n o => if sg_mem n sg then sg
              else if weqb o wzero then IMap.add n t sg
              else match t with VP m o' => IMap.add n (VP m (wsub o' o)) sg | _ => sg end
  | VAlu _ a b => match t with VAlu _ a' b' => msv b b' (msv a a' sg) | _ => sg end
  | VAluw _ a b => match t with VAluw _ a' b' => msv b b' (msv a a' sg) | _ => sg end
  | VMd _ a b => match t with VMd _ a' b' => msv b b' (msv a a' sg) | _ => sg end
  | VMdw _ a b => match t with VMdw _ a' b' => msv b b' (msv a a' sg) | _ => sg end
  | VExt _ _ _ a => match t with VExt _ _ _ a' => msv a a' sg | _ => sg end
  | VIns _ _ a b => match t with VIns _ _ a' b' => msv b b' (msv a a' sg) | _ => sg end
  | VBlob _ _ off _ => match t with VBlob _ _ off' _ => msv off off' sg | _ => sg end
  | VBg _ k _ _ => match t with VBg _ k' _ _ => sg_bind k (VP k' wzero) sg | _ => sg end
  | VF1 _ a => match t with VF1 _ a' => msv a a' sg | _ => sg end
  end.

Fixpoint msv_id (p : sv) (sg : subst) {struct p} : subst :=
  match p with
  | VL _ => sg
  | VP n _ => sg_bind n (VP n wzero) sg
  | VAlu _ a b | VAluw _ a b | VMd _ a b | VMdw _ a b | VIns _ _ a b => msv_id b (msv_id a sg)
  | VExt _ _ _ a | VF1 _ a => msv_id a sg
  | VBlob _ _ off _ => msv_id off sg
  | VBg _ k _ _ => sg_bind k (VP k wzero) sg
  end.
Definition mfact_id (f : fact) (sg : subst) : subst :=
  match f with
  | FRange k _ _ | FAlign k _ => sg_bind k (VP k wzero) sg
  | FULt a b | FULe a b | FEq a b | FNe a b | FSLt a b | FSLe a b => msv_id b (msv_id a sg)
  end.

Definition find_cell (x : sstate) (k g idx w : int) : option sv :=
  match IMap.find k (s_regs x) with
  | Some r => match IMap.find g (rg_cells r) with
              | Some gr => match find (fun c => PrimInt63.eqb (c_idx c) idx && PrimInt63.eqb (c_w c) w) (g_cells gr) with
                           | Some c => Some (c_v c)
                           | None => None
                           end
              | None => None
              end
  | None => None
  end.

Definition mregion (x : sstate) (tk : int) (tr : region) (sg : subst) : subst :=
  let k := match svar sg tk with Some k => k | None => tk end in
  match IMap.find k (s_regs x) with
  | None => sg
  | Some r =>
      let sg1 := msv (rg_hi tr) (rg_hi r) (sg_bind tk (VP k wzero) sg) in
      IMap.fold (fun g tgr acc =>
         fold_left (fun acc c => match find_cell x k g (c_idx c) (c_w c) with
                                 | Some v => msv (c_v c) v acc
                                 | None => acc
                                 end) (g_cells tgr) acc) (rg_cells tr) sg1
  end.

Fixpoint margs (ps ts : list sv) (sg : subst) : subst :=
  match ps, ts with p :: ps', t :: ts' => margs ps' ts' (msv p t sg) | _, _ => sg end.
Definition mops (P x : sstate) (sg : subst) : subst :=
  fold_left (fun acc o => match find (fun o' => PrimInt63.eqb (op_id o') (op_id o)) (s_ops x) with
                          | Some o' => margs (op_args o) (op_args o') acc
                          | None => acc
                          end) (s_ops P) sg.

Definition fregs : list r5 := X0 :: X2 :: xregs.

Definition xmatch (P x : sstate) : subst :=
  let sg0 := IMap.add 0%uint63 (VP 0%uint63 wzero) IMap.empty in
  let sg1 := fold_left (fun acc r => msv (getr P r) (getr x r) acc) fregs sg0 in
  let sg2 := fold_left (fun acc r => msv (getf P r) (getf x r) acc) fregs sg1 in
  let sg3 := IMap.fold (mregion x) (s_regs P) sg2 in
  let sg4 := IMap.fold (mregion x) (s_regs P) sg3 in
  let sg5 := mops P x sg4 in
  let sg6 := fold_left (fun acc f => mfact_id f acc) (s_facts P) sg5 in
  let sg7 := fold_left (fun acc r => msv_id (getr P r) acc) fregs sg6 in
  fold_left (fun acc r => msv_id (getf P r) acc) fregs sg7.

Definition exit_ok (n0 : int) (P x : sstate) : bool := entails x P (xmatch P x).

Record xres := XR { xr_exits : list sstate; xr_ns : list sstate; xr_sw : list sstate }.

Definition explore_tpl_comb (c : nat) (rd rn rs : option (list sstate * list sstate)) : option xres :=
  match rd, rn with
  | Some (xs0, []), Some ([], ys1) =>
      match c with
      | 2%nat => match rs with Some ([], ys2) => Some (XR xs0 ys1 ys2) | _ => None end
      | _ => Some (XR xs0 ys1 [])
      end
  | _, _ => None
  end.

Definition explore_tpl (ra : int) (X : ltpl) : option xres :=
  explore_tpl_comb (lt_c X) (explore FUEL ra (post_done X)) (explore FUEL ra (post_loop X false))
                   (if Nat.eqb (lt_c X) 2 then explore FUEL ra (post_loop X true) else None).

Definition iovcnt_of (y : sstate) : option nat := lit_nat12 (getr y X12).

Definition lt_shape_ok (X : ltpl) (fd : Z) (e1 : option (sv * sv)) : bool :=
  let st := lt_st X in let a := getr st X11 in
  match lit_Z (getr st X17), lit_Z (getr st X10), lit_nat12 (getr st X12) with
  | Some no, Some fd', Some c =>
      Z.eqb no 66 && Z.eqb fd' fd && Nat.eqb c (lt_c X)
      && match load8 st a, load8 st (addz a 8) with
         | Some b, Some l => sv_eqb b (VAR (lt_vb X)) && sv_eqb l (VAR (lt_vl X))
         | _, _ => false
         end
      && match c, e1 with
         | 2%nat, Some e => match read_ent st (addz a 16) with
                           | Some (b1, l1) => sv_eqb b1 (fst e) && sv_eqb l1 (snd e)
                           | None => false
                           end
         | 1%nat, _ => true
         | _, _ => false
         end
      && known_ltu (s_facts st) a TWO47
      && known_leu (s_facts st) (sv_alu ALU_ADD a (VL (wlit 32%uint63))) TWO47
      && PrimInt63.ltb (s_pc st) bit62i
      && sstate_wfb st
      && st_vars_below (lt_kc X) st && PrimInt63.leb (lt_n0 X) (lt_kc X)
      && PrimInt63.ltb (lt_n0 X) (lt_vb X) && PrimInt63.ltb (lt_n0 X) (lt_vl X) && PrimInt63.ltb (lt_n0 X) (lt_vr X)
      && PrimInt63.ltb 0%uint63 (lt_n0 X)
      && PrimInt63.ltb (lt_vb X) (lt_kc X) && PrimInt63.ltb (lt_vl X) (lt_kc X) && PrimInt63.ltb (lt_vr X) (lt_kc X)
      && sv_eqb (getr st (lw_rem L)) (VAR (lt_vr X))
      && existsb (fact_eqb (FULe (VAR (lt_vr X)) TWO30)) (s_facts st)
      && match IMap.find (s_pc st) it with Some IEcall => true | _ => false end
  | _, _, _ => false
  end.

Definition bytes_again (st : sstate) (es : list went) : bool :=
  forallb (fun e => match bytes_desc st (we_base e) (we_len e) with
                    | Some d => bdesc_eqb d (we_bytes e)
                    | None => false
                    end) es.

Definition went_below (n0 : int) (e : went) : bool :=
  sv_vars_below n0 (we_base e) && sv_vars_below n0 (we_len e)
  && match we_bytes e with BLit vs => forallb (sv_vars_below n0) vs | BBlob _ _ len => sv_vars_below n0 len end.

Variable fdok : sstate -> bool.

Record tplcert := TC { tc_tpl : ltpl; tc_exits : list sstate; tc_ns : list sstate; tc_sw : list sstate }.
Record swcert := SWC { c_T1 : sstate; c_ra : int; c_fd : Z; c_wes : list went; c_tpls : list tplcert }.

Definition tc_of (X : ltpl) (r : xres) : tplcert := TC X (xr_exits r) (xr_ns r) (xr_sw r).
Definition oe1_of (wes : list went) : option (sv * sv) := match wes with [_; e] => Some (we_base e, we_len e) | _ => None end.

Definition sw_gen (T P : sstate) : option swcert :=
  let n0 := s_next T in
  match lit_int (getr T X1) with
  | None => None
  | Some ra =>
  match run segs it [] T with
  | SStop KEcall T1 =>
    match lit_Z (getr T1 X10), lit_nat12 (getr T1 X12) with
    | Some fd, Some c1 =>
      match read_ents T1 c1 with
      | None => None
      | Some es =>
        match omap (fun e => match bytes_desc T1 (fst e) (snd e) with Some d => Some (WEnt (fst e) (snd e) d) | None => None end) es with
        | None => None
        | Some wes =>
          match lt_make [] T1 c1 n0 (PrimInt63.add n0 1%uint63) with
          | None => None
          | Some A =>
            match explore_tpl ra A with
            | None => None
            | Some rA =>
              let fresh2 := PrimInt63.add n0 64%uint63 in
              let fresh1 := PrimInt63.add n0 128%uint63 in
              let oB2 := match c1, xr_ns rA with
                         | 2%nat, y :: _ => lt_make (lw_junkB L) y 2%nat n0 fresh2
                         | _, _ => None
                         end in
              let rB2 := match oB2 with Some B2 => explore_tpl ra B2 | None => Some (XR [] [] []) end in
              match rB2 with
              | None => None
              | Some rB2 =>
                let firsts1 := match c1 with 2%nat => xr_sw rA ++ xr_sw rB2 | _ => xr_ns rA end in
                let oB1 := match firsts1 with y :: _ => lt_make (lw_junkB L) y 1%nat n0 fresh1 | [] => None end in
                let rB1 := match oB1 with Some B1 => explore_tpl ra B1 | None => Some (XR [] [] []) end in
                match rB1 with
                | None => None
                | Some rB1 =>
                    Some (SWC T1 ra fd wes
                           (tc_of A rA :: (match oB2 with Some B => [tc_of B rB2] | None => [] end)
                                       ++ (match oB1 with Some B => [tc_of B rB1] | None => [] end)))
                end
              end
            end
          end
        end
      end
    | _, _ => None
    end
  | _ => None
  end end.

Definition sw_cert (T P : sstate) : swcert := match sw_gen T P with Some C => C | None => SWC T 0%uint63 0 [] [] end.

Definition tpl_checks (n0 : int) (fd : Z) (c1 : nat) (oe1 : option (sv * sv)) (wes : list went) (P : sstate)
           (all : list tplcert) (t : tplcert) : bool :=
  let X := tc_tpl t in
  PrimInt63.eqb (lt_n0 X) n0 && lt_shape_ok X fd oe1 && bytes_again (lt_st X) wes
  && (Nat.eqb (lt_c X) 1 || (Nat.eqb (lt_c X) 2 && Nat.eqb c1 2))
  && forallb (exit_ok n0 P) (tc_exits t)
  && forallb (fun y => existsb (fun t' => Nat.eqb (lt_c (tc_tpl t')) (lt_c X) && lt_arrives X false oe1 (tc_tpl t') y) all) (tc_ns t)
  && forallb (fun y => Nat.eqb (lt_c X) 2 && existsb (fun t' => Nat.eqb (lt_c (tc_tpl t')) 1 && lt_arrives X true oe1 (tc_tpl t') y) all) (tc_sw t).

Definition wdflt : went := WEnt (VL wzero) (VL wzero) (BLit []).
Definition total_sv (wes : list went) : sv :=
  match wes with [w] => we_len w | [w; w'] => sv_alu ALU_ADD (we_len w) (we_len w') | _ => VL wzero end.

Definition sw_verify (T P : sstate) (C : swcert) : bool :=
  let n0 := s_next T in let T1 := c_T1 C in let wes := c_wes C in let c1 := length wes in let w0 := nth 0 wes wdflt in
  sstate_wfb P
  && match lit_int (getr T X1) with Some ra => PrimInt63.eqb ra (c_ra C) | None => false end
  && match lit_Z (getr T1 X17), lit_Z (getr T1 X10), lit_nat12 (getr T1 X12) with
     | Some no, Some fd, Some c1' => Z.eqb no 66 && Z.eqb fd (c_fd C) && (Z.eqb fd 1 || Z.eqb fd 2) && Nat.eqb c1' c1
     | _, _, _ => false
     end
  && fdok T1
  && forallb (fun w => ent_ok (s_facts T1) (we_base w, we_len w) && went_below n0 w) wes
  && match c_tpls C with
     | tA :: _ =>
         let A := tc_tpl tA in
         Nat.eqb (lt_c A) c1
         && match lt_subst A T1 with
            | Some sg => entails T1 (lt_st A) sg && sg_id_below n0 sg
                         && sg_binds sg (lt_vb A) (we_base w0) && sg_binds sg (lt_vl A) (we_len w0)
                         && sg_binds sg (lt_vr A) (getr T1 (lw_rem L))
            | None => false end
         && known_eq (s_facts T1) (getr T1 (lw_rem L)) (total_sv wes)
     | [] => false
     end
  && forallb (tpl_checks n0 (c_fd C) c1 (oe1_of wes) wes P (c_tpls C)) (c_tpls C).

Definition sw_check (T P : sstate) : bool :=
  match sw_gen T P with Some C => sw_verify T P C | None => false end.

End Checker.

Definition lowbyte (w : word) : byte := Z_to_bv 8 (bv_unsigned w).

Definition desc_bytes (E : env) (d : bdesc) : list byte :=
  match d with
  | BLit vs => map (fun v => lowbyte (den E v)) vs
  | BBlob j off len => map (fun i => nth (Z.to_nat off + i)%nat (eb E j) (Z_to_bv 8 0))
                           (seq 0 (Z.to_nat (bv_unsigned (den E len))))
  end.
Definition ent_bytes (E : env) (e : went) : list byte := desc_bytes E (we_bytes e).
Definition sw_bytes (C : swcert) (E : env) : list byte := concat (map (ent_bytes E) (c_wes C)).
Definition sw_fd (C : swcert) : word := Z_to_bv 64 (c_fd C).

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.

Variable it : itab.
Variable L : layout.
Variable fdok : sstate -> bool.
Hypothesis HIT : itab_ok segs it.
Hypothesis fdok_sound : forall E st ms model, st_ok segs OPS E st ms model -> fdok st = true ->
  forall fd, fd = 1 \/ fd = 2 -> fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).

Lemma lit_Z_sound : forall E v z, lit_Z v = Some z -> bv_unsigned (den E v) = z /\ 0 <= z < two64.
Proof.
  intros E v z H. destruct v; try discriminate H. cbn [lit_Z] in H. injection H as <-. cbn [den].
  rewrite wbv_unsigned. split; [reflexivity|]. rewrite <- wbv_unsigned. pose proof (bv_unsigned_in_range _ (wbv w)). unfold bv_modulus, two64 in *. lia.
Qed.

Lemma lit_int_sound : forall E v i, lit_int v = Some i -> den E v = Z_to_bv 64 (to_Z i) /\ to_Z i < 2 ^ 62.
Proof.
  intros E v i H. destruct v as [[[|] l]| | | | | | | | | |]; try discriminate H. cbn [lit_int] in H.
  destruct (PrimInt63.ltb l bit62i) eqn:Hl; [|discriminate H]. injection H as <-.
  apply Uint63.ltb_spec in Hl. change (to_Z bit62i) with (2 ^ 62) in Hl. split; [|exact Hl].
  cbn [den]. apply bv_eq. rewrite wbv_unsigned, Z_to_bv_unsigned. unfold w2Z. cbn [wt wl].
  symmetry. apply bv_wrap_small. unfold bv_modulus. pose proof (Uint63.to_Z_bounded l). change wB with (2 ^ 63) in *. lia.
Qed.

Lemma lit_nat12_sound : forall E v c, lit_nat12 v = Some c -> bv_unsigned (den E v) = Z.of_nat c /\ (c = 1%nat \/ c = 2%nat).
Proof.
  intros E v c H. unfold lit_nat12 in H. destruct (lit_Z v) as [z|] eqn:Hz; [|discriminate H].
  destruct (lit_Z_sound E v z Hz) as [Hu _].
  destruct z as [|p|p]; try discriminate H; destruct p as [p|p|]; try destruct p; try discriminate H; injection H as <-; rewrite Hu; cbn; auto.
Qed.

Lemma known_ltu_sound : forall E fs a b, facts_hold E fs -> known_ltu fs a b = true -> bv_unsigned (den E a) < bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_ltu, dec_true in H. destruct (decide_ltu fs a b) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (ltu_iff _ _ true) (ValP.decide_ltu_sound E fs Hfs a b true D)).
Qed.
Lemma known_leu_sound : forall E fs a b, facts_hold E fs -> known_leu fs a b = true -> bv_unsigned (den E a) <= bv_unsigned (den E b).
Proof.
  intros E fs a b Hfs H. unfold known_leu, dec_false in H. destruct (decide_ltu fs b a) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (ltu_iff _ _ false) (ValP.decide_ltu_sound E fs Hfs b a false D)).
Qed.
Lemma known_eq_sound : forall E fs a b, facts_hold E fs -> known_eq fs a b = true -> den E a = den E b.
Proof.
  intros E fs a b Hfs H. unfold known_eq, dec_true in H. destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate H.
  exact (proj1 (eqb_iff _ _ true) (ValP.decide_eq_sound E fs Hfs a b true D)).
Qed.

Lemma den_TWO30 : forall E, bv_unsigned (den E TWO30) = 2 ^ 30.
Proof. intros E. cbn [den TWO30]. rewrite wbv_unsigned, wlit_ok. reflexivity. Qed.
Lemma den_TWO47 : forall E, bv_unsigned (den E TWO47) = 2 ^ 47.
Proof. intros E. cbn [den TWO47]. rewrite wbv_unsigned, wlit_ok. reflexivity. Qed.
Lemma den_VAR : forall E n, den E (VAR n) = ev E n.
Proof. intros E n. cbn [den VAR]. rewrite ValP.wbv_wzero. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma u64_range : forall w : word, 0 <= bv_unsigned w < two64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w). unfold bv_modulus, two64 in *. lia. Qed.

Lemma den_add : forall E a b, den E (sv_alu ALU_ADD a b) = (den E a + den E b)%bv.
Proof. intros. rewrite den_sv_alu. reflexivity. Qed.
Lemma den_sub : forall E a b, den E (sv_alu ALU_SUB a b) = (den E a - den E b)%bv.
Proof. intros. rewrite den_sv_alu. reflexivity. Qed.
Lemma add_small : forall a b : word, bv_unsigned a + bv_unsigned b < two64 -> bv_unsigned (a + b)%bv = bv_unsigned a + bv_unsigned b.
Proof. intros a b H. rewrite bv_add_unsigned. apply bv_wrap_small. pose proof (u64_range a). pose proof (u64_range b). unfold bv_modulus, two64 in *. lia. Qed.
Lemma sub_small : forall a b : word, bv_unsigned b <= bv_unsigned a -> bv_unsigned (a - b)%bv = bv_unsigned a - bv_unsigned b.
Proof. intros a b H. rewrite bv_sub_unsigned. apply bv_wrap_small. pose proof (u64_range a). pose proof (u64_range b). unfold bv_modulus, two64 in *. lia. Qed.

Lemma den_addz : forall E a z, 0 <= z -> bv_unsigned (den E a) + z < two64 -> bv_unsigned (den E (addz a z)) = bv_unsigned (den E a) + z.
Proof.
  intros E a z Hz H. unfold addz. rewrite den_add. cbn [den]. rewrite StepM.wbv_Z2w.
  assert (Hz' : bv_unsigned (Z_to_bv 64 z) = z).
  { rewrite Z_to_bv_unsigned. apply bv_wrap_small. pose proof (u64_range (den E a)). unfold bv_modulus, two64 in *. lia. }
  rewrite add_small; rewrite Hz'; [reflexivity | exact H].
Qed.

Lemma ent_ok_sound : forall E fs e, facts_hold E fs -> ent_ok fs e = true ->
  bv_unsigned (den E (fst e)) < 2 ^ 47 /\ bv_unsigned (den E (snd e)) <= 2 ^ 30 /\
  bv_unsigned (den E (fst e)) + bv_unsigned (den E (snd e)) <= 2 ^ 47.
Proof.
  intros E fs e Hfs H. unfold ent_ok in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (known_ltu_sound E fs _ _ Hfs H1) as A. rewrite den_TWO47 in A.
  pose proof (known_leu_sound E fs _ _ Hfs H2) as B. rewrite den_TWO30 in B.
  pose proof (known_leu_sound E fs _ _ Hfs H3) as C. rewrite den_TWO47, den_add in C.
  rewrite add_small in C by (unfold two64; lia). auto.
Qed.

Lemma omap_spec : forall {A B} (f : A -> option B) l ys,
  omap f l = Some ys -> length ys = length l /\ forall k (a : A) (b : B), (k < length l)%nat -> f (nth k l a) = Some (nth k ys b).
Proof.
  intros A B f l. induction l as [|x l IH]; intros ys H; cbn [omap] in H.
  - injection H as <-. split; [reflexivity|]. intros k a b Hk. cbn in Hk. lia.
  - destruct (f x) as [y|] eqn:Hy; [|discriminate H]. destruct (omap f l) as [ys'|] eqn:Ho; [|discriminate H].
    injection H as <-. destruct (IH ys' eq_refl) as [HL HN]. split; [cbn; lia|].
    intros [|k] a b Hk; cbn; [exact Hy|]. apply HN. cbn in Hk. lia.
Qed.
Lemma iotaZ_length : forall z n, length (iotaZ z n) = n.
Proof. intros z n. revert z. induction n; intros z; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
Lemma iotaZ_nth : forall z n k d, (k < n)%nat -> nth k (iotaZ z n) d = z + Z.of_nat k.
Proof.
  intros z n. revert z. induction n as [|n IH]; intros z [|k] d Hk; cbn; try lia. rewrite IH by lia. lia.
Qed.
Lemma forallb_true_In : forall {A} (p : A -> bool) l x, forallb p l = true -> In x l -> p x = true.
Proof. intros A p l x H Hx. exact (proj1 (forallb_forall _ _) H x Hx). Qed.

Lemma ov_read_split : forall m a n b bs,
  ov_read_bytes segs m a (S n) = Some (b :: bs) ->
  rb segs m (bv_unsigned a) = Some b /\ ov_read_bytes segs m (a + 1)%bv n = Some bs.
Proof.
  intros m a n b bs H. cbn [ov_read_bytes] in H. rewrite MemP.rb_unfold, Z_to_bv_bv_unsigned.
  destruct (m a) as [b0|].
  - destruct (ov_read_bytes segs m (a + 1)%bv n); [|discriminate H]. injection H as -> ->. auto.
  - destruct (memory_read segs a 1) as [[|b0 r]|]; try discriminate H.
    destruct (ov_read_bytes segs m (a + 1)%bv n); [|discriminate H]. injection H as -> ->. auto.
Qed.

Lemma ov_read_length : forall m n a bs, ov_read_bytes segs m a n = Some bs -> length bs = n.
Proof.
  intros m n. induction n as [|n IH]; intros a bs H.
  - cbn in H. injection H as <-. reflexivity.
  - destruct bs as [|b bs']. { exfalso. cbn [ov_read_bytes] in H. destruct (match m a with Some b => Some b | None => _ end); [|discriminate H]. destruct (ov_read_bytes segs m (a+1)%bv n); discriminate H. }
    destruct (ov_read_split m a n b bs' H) as [_ H2]. cbn. rewrite (IH _ _ H2). reflexivity.
Qed.

Lemma ov_read_nth : forall m n A bs i, 0 <= A -> A + Z.of_nat n <= two64 ->
  ov_read_bytes segs m (Z_to_bv 64 A) n = Some bs -> (i < n)%nat ->
  rb segs m (A + Z.of_nat i) = Some (nth i bs (Z_to_bv 8 0)).
Proof.
  intros m n. induction n as [|n IH]; intros A bs i HA HAn H Hi; [lia|].
  destruct bs as [|b bs']; [pose proof (ov_read_length _ _ _ _ H) as HL; discriminate HL|].
  destruct (ov_read_split m _ n b bs' H) as [H1 H2].
  rewrite Z_to_bv_unsigned, bv_wrap_small in H1 by (unfold bv_modulus; unfold two64 in HAn; lia).
  destruct i as [|i]; [rewrite Z.add_0_r; exact H1|]. cbn [nth].
  rewrite MemP.Z_to_bv_succ in H2. replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia.
  apply (IH (A + 1) bs' i); [lia | lia | exact H2 | lia].
Qed.

Lemma ov_read_aux : forall ms n a bs, ms_rom ms = rom_of segs ->
  ov_read_bytes segs (ms_mem ms) a n = Some bs -> read_bytes_aux (ms_read_byte ms) a n = Some bs.
Proof.
  intros ms n. induction n as [|n IH]; intros a bs Hrom H; cbn [ov_read_bytes read_bytes_aux] in *; [exact H|].
  unfold ms_read_byte at 1. rewrite Hrom. unfold rom_of.
  destruct (ms_mem ms a) as [b|].
  - destruct (ov_read_bytes segs (ms_mem ms) (a + 1)%bv n) as [r|] eqn:Hr; [|discriminate H]. rewrite (IH _ _ Hrom Hr). exact H.
  - destruct (memory_read segs a 1) as [[|b r0]|]; try discriminate H.
    destruct (ov_read_bytes segs (ms_mem ms) (a + 1)%bv n) as [r|] eqn:Hr; [|discriminate H]. rewrite (IH _ _ Hrom Hr). exact H.
Qed.

Lemma read_bytes_map_of : forall mp a (n : nat) bs, Z.of_nat n < two64 ->
  read_bytes_aux mp a n = Some bs -> read_bytes_map mp a (Z_to_bv 64 (Z.of_nat n)) = Some bs.
Proof.
  intros mp a n bs Hn H. rewrite read_bytes_map_eq. unfold word_to_nat. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; unfold two64 in Hn; lia).
  rewrite Nat2Z.id. exact H.
Qed.

Lemma load8_sound : forall E st ms model a v,
  st_ok segs OPS E st ms model -> load8 segs st a = Some v ->
  exists bs, ov_read_bytes segs (ms_mem ms) (den E a) 8 = Some bs /\ den E v = le_bytes_to_word bs /\
             read_u64 (ms_read_byte ms) (den E a) = Some (den E v).
Proof.
  intros E st ms model a v HS H. unfold load8 in H.
  destruct (do_load segs st a 8 false) as [[v'|]|] eqn:Hd; try discriminate H. injection H as <-.
  destruct (do_load_sound segs OPS E st ms model a 8%uint63 false v' HS ltac:(unfold MemP.wok; right; right; right; reflexivity) Hd) as (bs & HL & HR & HV).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in *. change (to_Z 8%uint63) with 8 in HV. rewrite ext_word_id64 in HV.
  exists bs. split; [exact HR|]. split; [exact HV|].
  unfold read_u64. change (Z_to_bv 64 8) with (Z_to_bv 64 (Z.of_nat 8)).
  rewrite (read_bytes_map_of _ _ 8 bs) by first [unfold two64; lia | exact (ov_read_aux ms 8 _ bs (so_rom _ _ _ _ _ _ HS) HR)].
  rewrite HV. reflexivity.
Qed.

Lemma load1_sound : forall E st ms model a v,
  st_ok segs OPS E st ms model -> load1 segs st a = Some v ->
  rb segs (ms_mem ms) (bv_unsigned (den E a)) = Some (lowbyte (den E v)).
Proof.
  intros E st ms model a v HS H. unfold load1 in H.
  destruct (do_load segs st a 1 false) as [[v'|]|] eqn:Hd; try discriminate H. injection H as <-.
  destruct (do_load_sound segs OPS E st ms model a 1%uint63 false v' HS ltac:(unfold MemP.wok; left; reflexivity) Hd) as (bs & HL & HR & HV).
  change (Z.to_nat (to_Z 1%uint63)) with 1%nat in *. change (to_Z 1%uint63) with 1 in HV.
  destruct bs as [|b [|? ?]]; try discriminate HL.
  destruct (ov_read_split _ _ _ _ _ HR) as [H1 _]. rewrite H1. f_equal.
  unfold lowbyte. rewrite HV. unfold ext_word, ext_Z, le_bytes_to_word. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb.
  apply bv_eq. rewrite !Z_to_bv_unsigned. change (2 ^ (8 * 0)) with 1. rewrite Z.div_1_r.
  rewrite (bv_wrap_small 64 (bv_unsigned b)) by (unfold bv_modulus; lia).
  change (2 ^ (8 * 1)) with 256. rewrite (Z.mod_small _ 256) by lia.
  rewrite (bv_wrap_small 64 (bv_unsigned b)) by (unfold bv_modulus; lia). symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
Qed.

Lemma load8_acc : forall E st ms model a v,
  st_ok segs OPS E st ms model -> load8 segs st a = Some v ->
  forall j, 0 <= j < 8 -> fx_acc segs E (s_regs st) (bv_unsigned (den E a) + j).
Proof.
  intros E st ms model a v HS H. unfold load8 in H.
  destruct (do_load segs st a 8 false) as [[v'|]|] eqn:Hd; try discriminate H.
  exact (StepAcc.do_load_acc segs OPS E st ms model a 8%uint63 false v' HS ltac:(unfold MemP.wok; right; right; right; reflexivity) Hd).
Qed.

Lemma load1_acc : forall E st ms model a v,
  st_ok segs OPS E st ms model -> load1 segs st a = Some v -> fx_acc segs E (s_regs st) (bv_unsigned (den E a)).
Proof.
  intros E st ms model a v HS H. unfold load1 in H.
  destruct (do_load segs st a 1 false) as [[v'|]|] eqn:Hd; try discriminate H.
  pose proof (StepAcc.do_load_acc segs OPS E st ms model a 1%uint63 false v' HS ltac:(unfold MemP.wok; left; reflexivity) Hd 0 ltac:(change (to_Z 1%uint63) with 1; lia)) as F.
  rewrite Z.add_0_r in F. exact F.
Qed.

Lemma ent_acc : forall E st ms model p b l,
  st_ok segs OPS E st ms model -> bv_unsigned (den E p) + 16 <= two64 ->
  load8 segs st p = Some b -> load8 segs st (addz p 8) = Some l ->
  forall j, 0 <= j < 16 -> fx_acc segs E (s_regs st) (bv_unsigned (den E p) + j).
Proof.
  intros E st ms model p b l HS Hr Hb Hl j Hj. destruct (Z_lt_le_dec j 8) as [J|J].
  - exact (load8_acc E st ms model p b HS Hb j ltac:(lia)).
  - pose proof (load8_acc E st ms model _ l HS Hl (j - 8) ltac:(lia)) as F.
    rewrite (den_addz E p 8) in F by lia.
    replace (bv_unsigned (den E p) + 8 + (j - 8)) with (bv_unsigned (den E p) + j) in F by lia. exact F.
Qed.

Lemma explore_S : forall f ra st, explore segs it (S f) ra st =
      match run segs it [ra] st with
      | SStop KStopPc st' => if PrimInt63.eqb (s_pc st') ra then Some ([st'], []) else None
      | SStop KEcall st' =>
          match IMap.find (s_pc st') it with Some IEcall => Some ([], [st']) | _ => None end
      | SStop (KBranch _ _ _ _) st' =>
          if negb (PrimInt63.ltb (s_pc st') bit62i) then None else
          match IMap.find (s_pc st') it with
          | Some (IBranch c rs1 rs2 off) =>
              match take_branch c (getr st' rs1) (getr st' rs2) off true st', take_branch c (getr st' rs1) (getr st' rs2) off false st' with
              | Some s1, Some s2 =>
                  match explore segs it f ra s1, explore segs it f ra s2 with
                  | Some (x1, y1), Some (x2, y2) => Some (x1 ++ x2, y1 ++ y2)
                  | _, _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | _ => None
      end.
Proof. reflexivity. Qed.

Lemma explore_sound : forall fuel ra st xs ys,
  explore segs it fuel ra st = Some (xs, ys) ->
  forall (MI : Model -> Prop), mstable MI ->
  forall E ms model K,
  st_ok segs OPS E st ms model -> MI model ->
  (forall x ms' mo', In x xs -> s_pc x = ra -> MI mo' -> st_ok segs OPS E x ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  (forall y ms' mo', In y ys -> IMap.find (s_pc y) it = Some IEcall -> MI mo' -> st_ok segs OPS E y ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  induction fuel as [|f IH]; intros ra st xs ys Hx MI HMI E ms model K HS HMo HX HY; [discriminate Hx|].
  rewrite explore_S in Hx.
  destruct (run segs it [ra] st) as [s0|why st1] eqn:Hr; [discriminate Hx|].
  pose proof (run_sound segs OPS E st ms model it [ra] why st1 HIT HS Hr) as (ms1 & mo1 & Hms & HS1).
  pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as MH.
  pose proof (asteps_stable segs MI ms model ms1 mo1 HMI Hms HMo) as HMo1.
  apply (ShapeAcc.rz_asteps segs ms model ms1 mo1 K MH Hms).
  destruct why as [| |c1 a1 b1 off1|?|? ?|? ?|?| | | | |]; try discriminate Hx.
  - destruct (PrimInt63.eqb (s_pc st1) ra) eqn:Hpc; [|discriminate Hx]. injection Hx as <- <-.
    apply (HX st1 ms1 mo1); [left; reflexivity | apply Uint63.eqb_correct; exact Hpc | exact HMo1 | exact HS1].
  - destruct (IMap.find (s_pc st1) it) as [fi|] eqn:Hfi; [|discriminate Hx]. destruct fi; try discriminate Hx.
    injection Hx as <- <-. apply (HY st1 ms1 mo1); [left; reflexivity | exact Hfi | exact HMo1 | exact HS1].
  - destruct (PrimInt63.ltb (s_pc st1) bit62i) eqn:Hpc62; [|discriminate Hx]. cbn [negb] in Hx.
    destruct (IMap.find (s_pc st1) it) as [fi|] eqn:Hfi; [|discriminate Hx]. destruct fi; try discriminate Hx.
    destruct (take_branch c (getr st1 rs1) (getr st1 rs2) off true st1) as [s1|] eqn:HT; [|discriminate Hx].
    destruct (take_branch c (getr st1 rs1) (getr st1 rs2) off false st1) as [s2|] eqn:HF; [|discriminate Hx].
    destruct (explore segs it f ra s1) as [[x1 y1]|] eqn:E1; [|discriminate Hx].
    destruct (explore segs it f ra s2) as [[x2 y2]|] eqn:E2; [|discriminate Hx]. injection Hx as <- <-.
    pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS1)) as MH1.
    destruct (branch_taken c (den E (getr st1 rs1)) (den E (getr st1 rs2))) eqn:BT.
    + destruct (take_branch_sound segs OPS E st1 ms1 mo1 it c rs1 rs2 off true s1 HIT HS1 Hpc62 Hfi BT HT) as (ms2 & Hstep & HS2).
      apply (ShapeAcc.rz_astep segs ms1 mo1 ms2 mo1 K MH1 (so_svc _ _ _ _ _ _ HS1) Hstep).
      apply (IH ra s1 x1 y1 E1 MI HMI E ms2 mo1 K HS2 HMo1).
      * intros x ms' mo' Hin. apply HX. apply in_app_iff. left. exact Hin.
      * intros y ms' mo' Hin. apply HY. apply in_app_iff. left. exact Hin.
    + destruct (take_branch_sound segs OPS E st1 ms1 mo1 it c rs1 rs2 off false s2 HIT HS1 Hpc62 Hfi BT HF) as (ms2 & Hstep & HS2).
      apply (ShapeAcc.rz_astep segs ms1 mo1 ms2 mo1 K MH1 (so_svc _ _ _ _ _ _ HS1) Hstep).
      apply (IH ra s2 x2 y2 E2 MI HMI E ms2 mo1 K HS2 HMo1).
      * intros x ms' mo' Hin. apply HX. apply in_app_iff. right. exact Hin.
      * intros y ms' mo' Hin. apply HY. apply in_app_iff. right. exact Hin.
Qed.

Lemma iota_int_In : forall n i v, to_Z i + Z.of_nat n <= wB -> to_Z i <= to_Z v < to_Z i + Z.of_nat n -> In v (iota_int i n).
Proof.
  induction n as [|n IH]; intros i v Hn Hv; [lia|]. cbn [iota_int].
  destruct (Z.eq_dec (to_Z v) (to_Z i)) as [Heq|Hne].
  - left. apply Uint63.to_Z_inj. symmetry. exact Heq.
  - right. pose proof (Uint63.to_Z_bounded v). pose proof (Uint63.to_Z_bounded i).
    apply IH; rewrite Uint63.add_spec; change (to_Z 1%uint63) with 1; rewrite Z.mod_small by lia; lia.
Qed.

Lemma sg_id_below_sound : forall n0 sg v, sg_id_below n0 sg = true -> to_Z v < to_Z n0 -> IMap.find v sg = Some (VAR v).
Proof.
  intros n0 sg v H Hv. unfold sg_id_below in H.
  pose proof (Uint63.to_Z_bounded n0). pose proof (Uint63.to_Z_bounded v).
  assert (Hin : In v (iota_int 0%uint63 (Z.to_nat (to_Z n0)))).
  { apply iota_int_In; change (to_Z 0%uint63) with 0; rewrite Z2Nat.id by lia; lia. }
  pose proof (forallb_true_In _ _ v H Hin) as X. cbn beta in X.
  destruct (IMap.find v sg) as [u|]; [|discriminate X]. apply sv_eqb_eq in X. subst u. reflexivity.
Qed.

Lemma subst_env_id_ext : forall n0 E sg, sg_id_below n0 sg = true -> env_ext n0 E (subst_env E sg).
Proof.
  intros n0 E sg H. split; [reflexivity|]. intros k Hk.
  pose proof (sg_id_below_sound n0 sg k H Hk) as F. split.
  - rewrite (subst_env_ev E sg k (VAR k) F). apply den_VAR.
  - cbn [subst_env eg]. unfold svar. rewrite F. cbn [VAR]. change (weqb wzero wzero) with true. reflexivity.
Qed.

Lemma sg_binds_sound : forall E sg v u, sg_binds sg v u = true -> ev (subst_env E sg) v = den E u.
Proof.
  intros E sg v u H. unfold sg_binds in H. destruct (IMap.find v sg) as [u'|] eqn:F; [|discriminate H].
  apply sv_eqb_eq in H. subst u'. exact (subst_env_ev E sg v u F).
Qed.

Lemma exit_ok_sound : forall n0 P x E ms model,
  sstate_wfb P = true -> exit_ok n0 P x = true -> st_ok segs OPS E x ms model ->
  exists E', st_ok segs OPS E' P ms model /\ eb E' = eb E.
Proof.
  intros n0 P x E ms model WF H HS. unfold exit_ok in H.
  exists (subst_env E (xmatch P x)). split; [exact (entails_sound segs OPS E x P _ ms model WF H HS) | apply subst_env_eb].
Qed.

Lemma lt_arrives_sound : forall src sw e1 tgt y E ms model,
  sstate_wfb (lt_st tgt) = true -> lt_arrives segs L src sw e1 tgt y = true -> st_ok segs OPS E y ms model ->
  exists E' b l, st_ok segs OPS E' (lt_st tgt) ms model /\ env_ext (lt_n0 tgt) E E' /\ eb E' = eb E /\
    load8 segs y (getr y X11) = Some b /\ load8 segs y (addz (getr y X11) 8) = Some l /\
    ev E' (lt_vb tgt) = den E b /\ ev E' (lt_vl tgt) = den E l /\ ev E' (lt_vr tgt) = den E (getr y (lw_rem L)) /\
    den E (getr y (lw_rem L)) = (ev E (lt_vr src) - ev E (lt_kc src))%bv /\
    (if sw then exists b1 l1, e1 = Some (b1, l1) /\
                  den E b = (den E b1 + (ev E (lt_kc src) - ev E (lt_vl src)))%bv /\
                  den E l = (den E l1 - (ev E (lt_kc src) - ev E (lt_vl src)))%bv
     else den E b = (ev E (lt_vb src) + ev E (lt_kc src))%bv /\ den E l = (ev E (lt_vl src) - ev E (lt_kc src))%bv).
Proof.
  intros src sw e1 tgt y E ms model WF H HS. unfold lt_arrives in H.
  destruct (load8 segs y (getr y X11)) as [b|] eqn:Hb; [|discriminate H].
  destruct (load8 segs y (addz (getr y X11) 8)) as [l|] eqn:Hl; [|discriminate H].
  destruct (lt_subst segs L tgt y) as [sg|]; [|discriminate H].
  apply andb_prop in H as [H Hform]. apply andb_prop in H as [H Hrem]. apply andb_prop in H as [H Bvr].
  apply andb_prop in H as [H Bvl]. apply andb_prop in H as [H Bvb]. apply andb_prop in H as [EN ID].
  exists (subst_env E sg), b, l.
  split; [exact (entails_sound segs OPS E y (lt_st tgt) sg ms model WF EN HS)|].
  split; [exact (subst_env_id_ext _ E sg ID)|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (sg_binds_sound E sg _ _ Bvb)|]. split; [exact (sg_binds_sound E sg _ _ Bvl)|]. split; [exact (sg_binds_sound E sg _ _ Bvr)|].
  apply sv_eqb_eq in Hrem. split; [rewrite Hrem, den_sub, !den_VAR; reflexivity|].
  destruct sw.
  - destruct e1 as [[b1 l1]|]; [|discriminate Hform]. apply andb_prop in Hform as [F1 F2]. apply sv_eqb_eq in F1. apply sv_eqb_eq in F2.
    exists b1, l1. split; [reflexivity|]. rewrite F1, F2, den_add, !den_sub, !den_VAR. split; reflexivity.
  - apply andb_prop in Hform as [F1 F2]. apply sv_eqb_eq in F1. apply sv_eqb_eq in F2.
    rewrite F1, F2, den_add, den_sub, !den_VAR. split; reflexivity.
Qed.

Lemma nth_map_seq : forall {A} (f : nat -> A) N st k d, (k < N)%nat -> nth k (map f (seq st N)) d = f (st + k)%nat.
Proof.
  intros A f N. induction N as [|N IH]; intros st k d Hk; [lia|]. cbn [seq map]. destruct k as [|k]; cbn [nth].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH by lia. f_equal. lia.
Qed.

Lemma desc_bytes_length_lit : forall E vs, length (desc_bytes E (BLit vs)) = length vs.
Proof. intros. cbn [desc_bytes]. apply length_map. Qed.

Lemma bytes_desc_sound : forall E st ms model base len d,
  st_ok segs OPS E st ms model -> bytes_desc segs st base len = Some d ->
  bv_unsigned (den E base) + bv_unsigned (den E len) <= 2 ^ 47 -> bv_unsigned (den E len) <= 2 ^ 30 ->
  Z.of_nat (length (desc_bytes E d)) = bv_unsigned (den E len) /\
  forall i, 0 <= i < bv_unsigned (den E len) ->
    rb segs (ms_mem ms) (bv_unsigned (den E base) + i) = Some (nth (Z.to_nat i) (desc_bytes E d) (Z_to_bv 8 0)).
Proof.
  intros E st ms model base len d HS H Hsum Hlen. unfold bytes_desc in H.
  pose proof (u64_range (den E base)) as HB.
  destruct (lit_Z len) as [n|] eqn:Hn.
  -
    destruct (Z.leb n MAXLIT) eqn:Hmax; [|discriminate H].
    destruct (omap (fun i => load1 segs st (addz base i)) (iotaZ 0 (Z.to_nat n))) as [vs|] eqn:Ho; [|discriminate H].
    injection H as <-. destruct (lit_Z_sound E len n Hn) as [HL Hnr]. rewrite HL in *.
    destruct (omap_spec _ _ _ Ho) as [HLen HNth]. rewrite iotaZ_length in HLen, HNth.
    split; [rewrite desc_bytes_length_lit, HLen; lia|].
    intros i Hi. cbn [desc_bytes].
    pose proof (HNth (Z.to_nat i) 0 (VL wzero) ltac:(lia)) as HX. rewrite iotaZ_nth in HX by lia.
    rewrite Z2Nat.id in HX by lia. rewrite Z.add_0_l in HX.
    pose proof (load1_sound E st ms model _ _ HS HX) as R. rewrite (den_addz E base i) in R by (unfold two64; lia).
    rewrite R. f_equal. unfold desc_bytes. symmetry.
    rewrite (nth_indep _ (Z_to_bv 8 0) (lowbyte (den E (VL wzero)))) by (rewrite length_map, HLen; lia).
    exact (map_nth (fun v => lowbyte (den E v)) vs (VL wzero) (Z.to_nat i)).
  -
    destruct base as [|k o| | | | | | | | |]; try discriminate H.
    destruct (IMap.find k (s_regs st)) as [[lo hi w bg cells]|] eqn:Hr; [|discriminate H].
    destruct w; [discriminate H|]. destruct bg as [| | | |j sh]; try discriminate H. destruct cells; [|discriminate H].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end. injection H as <-.
    apply andb_prop in Hc as [Hc C7]. apply andb_prop in Hc as [Hc C6]. apply andb_prop in Hc as [Hc C5]. apply andb_prop in Hc as [Hc C4].
    apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
    apply Uint63.eqb_correct in C2. apply Uint63.eqb_correct in C3. subst lo sh.
    assert (C1' : PrimInt63.eqb k 0%uint63 = false) by (destruct (PrimInt63.eqb k 0%uint63); [discriminate C1 | reflexivity]). clear C1. rename C1' into C1.
    destruct o as [ot ol]. cbn [wt wl] in C4, C5. destruct ot; [discriminate C4|]. apply Uint63.ltb_spec in C5. change (to_Z bit62i) with (2 ^ 62) in C5.
    pose proof (so_reg _ _ _ _ _ _ HS k _ Hr) as R. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
    pose proof (known_leu_sound E _ _ _ Hfs C6) as A6. rewrite den_add in A6. cbn [den] in A6.
    pose proof (known_leu_sound E _ _ _ Hfs C7) as A7.
    assert (Ho : bv_unsigned (wbv {| wt := false; wl := ol |}) = to_Z ol) by (rewrite wbv_unsigned; unfold w2Z; cbn [wt wl]; lia).
    pose proof (Uint63.to_Z_bounded ol) as Hol.
    assert (HhiZ : hiZ E (Region 0%uint63 hi false (BGBlob j 0%uint63) IMap.Leaf) = bv_unsigned (den E hi)) by reflexivity.
    pose proof (ro_range _ _ _ _ _ _ R C1) as Hrange. rewrite HhiZ in Hrange. change (loZ _) with 0 in Hrange. unfold two64 in Hrange.
    pose proof (u64_range (den E hi)) as Hhi. pose proof (u64_range (ev E k)) as Hk.
    rewrite add_small in A6 by (rewrite Ho; unfold two64; lia). rewrite Ho in A6.
    pose proof (u64_range (den E len)) as Hlen0.
    assert (Hbase : bv_unsigned (den E (VP k {| wt := false; wl := ol |})) = bv_unsigned (ev E k) + to_Z ol).
    { cbn [den]. rewrite add_small; rewrite Ho; [reflexivity | unfold two64 in *; lia]. }
    split.
    + cbn [desc_bytes]. rewrite length_map, length_seq. unfold two64 in *. lia.
    + intros i Hi. cbn [desc_bytes]. rewrite (nth_map_seq _ _ 0) by lia. cbn [Nat.add].
      pose proof (ro_bg _ _ _ _ _ _ R (to_Z ol + i)) as B.
      cbn [rg_bg rg_cells bg_byte] in B. rewrite HhiZ in B. change (loZ _) with 0 in B. change (to_Z 0%uint63) with 0 in B.
      rewrite Hbase. replace (bv_unsigned (ev E k) + to_Z ol + i) with (bv_unsigned (ev E k) + (to_Z ol + i)) by lia.
      rewrite B.
      * f_equal. f_equal. rewrite Z.sub_0_r. rewrite Z2Nat.inj_add by lia. reflexivity.
      * intros _. lia.
      * intros X. rewrite X in C1. discriminate C1.
      * intros g gr _ Hg. cbn in Hg. discriminate Hg.
Qed.

Lemma bytes_desc_acc : forall E st ms model base len d,
  st_ok segs OPS E st ms model -> bytes_desc segs st base len = Some d ->
  bv_unsigned (den E base) + bv_unsigned (den E len) <= 2 ^ 47 -> bv_unsigned (den E len) <= 2 ^ 30 ->
  forall i, 0 <= i < bv_unsigned (den E len) -> fx_acc segs E (s_regs st) (bv_unsigned (den E base) + i).
Proof.
  intros E st ms model base len d HS H Hsum Hlen. unfold bytes_desc in H.
  pose proof (u64_range (den E base)) as HB.
  destruct (lit_Z len) as [n|] eqn:Hn.
  - destruct (Z.leb n MAXLIT) eqn:Hmax; [|discriminate H].
    destruct (omap (fun i => load1 segs st (addz base i)) (iotaZ 0 (Z.to_nat n))) as [vs|] eqn:Ho; [|discriminate H].
    destruct (lit_Z_sound E len n Hn) as [HL Hnr]. rewrite HL in *.
    destruct (omap_spec _ _ _ Ho) as [HLen HNth]. rewrite iotaZ_length in HLen, HNth.
    intros i Hi.
    pose proof (HNth (Z.to_nat i) 0 (VL wzero) ltac:(lia)) as HX. rewrite iotaZ_nth in HX by lia.
    rewrite Z2Nat.id in HX by lia. rewrite Z.add_0_l in HX.
    pose proof (load1_acc E st ms model _ _ HS HX) as R. rewrite (den_addz E base i) in R by (unfold two64; lia). exact R.
  - destruct base as [|k o| | | | | | | | |]; try discriminate H.
    destruct (IMap.find k (s_regs st)) as [[lo hi w bg cells]|] eqn:Hr; [|discriminate H].
    destruct w; [discriminate H|]. destruct bg as [| | | |j sh]; try discriminate H. destruct cells; [|discriminate H].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end. clear H.
    apply andb_prop in Hc as [Hc C7]. apply andb_prop in Hc as [Hc C6]. apply andb_prop in Hc as [Hc C5]. apply andb_prop in Hc as [Hc C4].
    apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
    apply Uint63.eqb_correct in C2. apply Uint63.eqb_correct in C3. subst lo sh.
    assert (C1' : PrimInt63.eqb k 0%uint63 = false) by (destruct (PrimInt63.eqb k 0%uint63); [discriminate C1 | reflexivity]). clear C1. rename C1' into C1.
    destruct o as [ot ol]. cbn [wt wl] in C4, C5. destruct ot; [discriminate C4|]. apply Uint63.ltb_spec in C5. change (to_Z bit62i) with (2 ^ 62) in C5.
    pose proof (so_reg _ _ _ _ _ _ HS k _ Hr) as R. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
    pose proof (known_leu_sound E _ _ _ Hfs C6) as A6. rewrite den_add in A6. cbn [den] in A6.
    assert (Ho : bv_unsigned (wbv {| wt := false; wl := ol |}) = to_Z ol) by (rewrite wbv_unsigned; unfold w2Z; cbn [wt wl]; lia).
    pose proof (Uint63.to_Z_bounded ol) as Hol.
    assert (HhiZ : hiZ E (Region 0%uint63 hi false (BGBlob j 0%uint63) IMap.Leaf) = bv_unsigned (den E hi)) by reflexivity.
    pose proof (ro_range _ _ _ _ _ _ R C1) as Hrange. rewrite HhiZ in Hrange. change (loZ _) with 0 in Hrange. unfold two64 in Hrange.
    pose proof (u64_range (den E hi)) as Hhi. pose proof (u64_range (ev E k)) as Hk.
    rewrite add_small in A6 by (rewrite Ho; unfold two64; lia). rewrite Ho in A6.
    pose proof (u64_range (den E len)) as Hlen0.
    assert (Hbase : bv_unsigned (den E (VP k {| wt := false; wl := ol |})) = bv_unsigned (ev E k) + to_Z ol).
    { cbn [den]. rewrite add_small; rewrite Ho; [reflexivity | unfold two64 in *; lia]. }
    intros i Hi. left. exists k, (Region 0%uint63 hi false (BGBlob j 0%uint63) IMap.Leaf).
    split; [exact Hr|]. split; [exact C1|]. rewrite HhiZ, Hbase. change (loZ _) with 0. lia.
Qed.

Lemma andb_true_split : forall a b, a && b = true -> a = true /\ b = true.
Proof. intros a b H. apply andb_prop in H. exact H. Qed.

Lemma lt_shape_ok_inv : forall X fd e1, lt_shape_ok segs it L X fd e1 = true ->
  let st := lt_st X in let a := getr st X11 in
  lit_Z (getr st X17) = Some 66 /\ lit_Z (getr st X10) = Some fd /\ lit_nat12 (getr st X12) = Some (lt_c X) /\
  load8 segs st a = Some (VAR (lt_vb X)) /\ load8 segs st (addz a 8) = Some (VAR (lt_vl X)) /\
  (lt_c X = 2%nat -> exists b1 l1, e1 = Some (b1, l1) /\ load8 segs st (addz a 16) = Some b1 /\ load8 segs st (addz (addz a 16) 8) = Some l1) /\
  known_ltu (s_facts st) a TWO47 = true /\ known_leu (s_facts st) (sv_alu ALU_ADD a (VL (wlit 32%uint63))) TWO47 = true /\
  PrimInt63.ltb (s_pc st) bit62i = true /\ sstate_wfb st = true /\ st_vars_below (lt_kc X) st = true /\
  to_Z (lt_n0 X) <= to_Z (lt_kc X) /\ to_Z (lt_n0 X) < to_Z (lt_vb X) /\ to_Z (lt_n0 X) < to_Z (lt_vl X) /\ to_Z (lt_n0 X) < to_Z (lt_vr X) /\
  (0 < to_Z (lt_n0 X) /\ to_Z (lt_vb X) < to_Z (lt_kc X) /\ to_Z (lt_vl X) < to_Z (lt_kc X) /\ to_Z (lt_vr X) < to_Z (lt_kc X) /\
   getr st (lw_rem L) = VAR (lt_vr X) /\ In (FULe (VAR (lt_vr X)) TWO30) (s_facts st) /\ IMap.find (s_pc st) it = Some IEcall).
Proof.
  intros X fd e1 H. unfold lt_shape_ok in H. cbv zeta in H. cbv zeta.
  destruct (lit_Z (getr (lt_st X) X17)) as [z17|]; [|discriminate H].
  destruct (lit_Z (getr (lt_st X) X10)) as [fd'|]; [|discriminate H].
  destruct (lit_nat12 (getr (lt_st X) X12)) as [c|]; [|discriminate H].
  apply andb_true_split in H as [H R7]. apply andb_true_split in H as [H R6]. apply andb_true_split in H as [H R5].
  apply andb_true_split in H as [H R4]. apply andb_true_split in H as [H R3]. apply andb_true_split in H as [H R2]. apply andb_true_split in H as [H R1].
  apply Uint63.ltb_spec in R1. apply Uint63.ltb_spec in R2. apply Uint63.ltb_spec in R3. apply Uint63.ltb_spec in R4. change (to_Z 0%uint63) with 0 in R1.
  apply sv_eqb_eq in R5. apply existsb_exists in R6. destruct R6 as (f6 & R6in & R6eq). apply ValP.fact_eqb_eq in R6eq. subst f6.
  destruct (IMap.find (s_pc (lt_st X)) it) as [fi|] eqn:R7'; [|discriminate R7]. destruct fi; try discriminate R7. clear R7.
  apply andb_true_split in H as [H Q4]. apply andb_true_split in H as [H Q3]. apply andb_true_split in H as [H Q2].
  apply andb_true_split in H as [H Q1]. apply andb_true_split in H as [H Qsv]. apply andb_true_split in H as [H Qwf].
  apply andb_true_split in H as [H Qpc]. apply andb_true_split in H as [H Qleu]. apply andb_true_split in H as [H Qltu].
  apply andb_true_split in H as [H Qe1]. apply andb_true_split in H as [H Qld]. apply andb_true_split in H as [H Qc].
  apply andb_true_split in H as [Qno Qfd].
  apply Z.eqb_eq in Qno. apply Z.eqb_eq in Qfd. apply Nat.eqb_eq in Qc. subst z17 fd' c.
  apply Uint63.leb_spec in Q1. apply Uint63.ltb_spec in Q2. apply Uint63.ltb_spec in Q3. apply Uint63.ltb_spec in Q4.
  destruct (load8 segs (lt_st X) (getr (lt_st X) X11)) as [b|]; [|discriminate Qld].
  destruct (load8 segs (lt_st X) (addz (getr (lt_st X) X11) 8)) as [l|]; [|discriminate Qld].
  apply andb_true_split in Qld as [Qb Ql]. apply sv_eqb_eq in Qb. apply sv_eqb_eq in Ql. subst b l.
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros Hc. rewrite Hc in Qe1. destruct e1 as [[b1 l1]|]; [|discriminate Qe1]. unfold read_ent in Qe1.
    destruct (load8 segs (lt_st X) (addz (getr (lt_st X) X11) 16)) as [b1'|]; [|discriminate Qe1].
    destruct (load8 segs (lt_st X) (addz (addz (getr (lt_st X) X11) 16) 8)) as [l1'|]; [|discriminate Qe1].
    apply andb_true_split in Qe1 as [E1 E2]. apply sv_eqb_eq in E1. apply sv_eqb_eq in E2. cbn [fst snd] in E1, E2. subst b1' l1'.
    exists b1, l1. repeat split; reflexivity. }
  split; [exact Qltu|]. split; [exact Qleu|]. split; [exact Qpc|]. split; [exact Qwf|]. split; [exact Qsv|].
  split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
  split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|]. split; [exact R6in|]. reflexivity.
Qed.


Lemma den_addz_bv : forall E a z, den E (addz a z) = (den E a + Z_to_bv 64 z)%bv.
Proof. intros E a z. unfold addz. rewrite den_add. cbn [den]. rewrite StepM.wbv_Z2w. reflexivity. Qed.

Lemma env_ext_weaken : forall n n' E E', to_Z n' <= to_Z n -> env_ext n E E' -> env_ext n' E E'.
Proof. intros n n' E E' Hle [Hb Hk]. split; [exact Hb|]. intros k Hk'. apply Hk. lia. Qed.

Lemma env_upd_other : forall E n w k, k <> n -> ev (env_upd E n w) k = ev E k.
Proof.
  intros E n w k Hne. cbn [env_upd ev]. destruct (PrimInt63.eqb k n) eqn:Q; [|reflexivity].
  apply Uint63.eqb_correct in Q. congruence.
Qed.

Lemma svs_eqb_eq : forall xs ys, svs_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [svs_eqb] in H; try discriminate H; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply sv_eqb_eq in H1. rewrite (IH ys H2). subst. reflexivity.
Qed.
Lemma bdesc_eqb_eq : forall a b, bdesc_eqb a b = true -> a = b.
Proof.
  intros [xs|j o l] [ys|j' o' l'] H; cbn [bdesc_eqb] in H; try discriminate H.
  - rewrite (svs_eqb_eq _ _ H). reflexivity.
  - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Uint63.eqb_correct in H1. apply Z.eqb_eq in H2. apply sv_eqb_eq in H3. subst. reflexivity.
Qed.

Lemma desc_bytes_ext : forall n0 E E' w, env_ext n0 E E' -> went_below n0 w = true ->
  den E' (we_base w) = den E (we_base w) /\ den E' (we_len w) = den E (we_len w) /\ ent_bytes E' w = ent_bytes E w.
Proof.
  intros n0 E E' w HX H. unfold went_below in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (den_reval n0 E E' HX) as DR.
  split; [exact (DR _ H1)|]. split; [exact (DR _ H2)|].
  unfold ent_bytes. destruct (we_bytes w) as [vs|j o l]; cbn [desc_bytes].
  - apply map_ext_in. intros v Hv. rewrite (DR v (forallb_true_In _ _ v H3 Hv)). reflexivity.
  - rewrite (DR _ H3), (proj1 HX). reflexivity.
Qed.

Lemma bytes_again_sound : forall n0 E E' st ms model wes w,
  st_ok segs OPS E' st ms model -> bytes_again segs st wes = true -> In w wes -> went_below n0 w = true -> env_ext n0 E E' ->
  bv_unsigned (den E (we_base w)) + bv_unsigned (den E (we_len w)) <= 2 ^ 47 -> bv_unsigned (den E (we_len w)) <= 2 ^ 30 ->
  Z.of_nat (length (ent_bytes E w)) = bv_unsigned (den E (we_len w)) /\
  forall i, 0 <= i < bv_unsigned (den E (we_len w)) ->
    rb segs (ms_mem ms) (bv_unsigned (den E (we_base w)) + i) = Some (nth (Z.to_nat i) (ent_bytes E w) (Z_to_bv 8 0)).
Proof.
  intros n0 E E' st ms model wes w HS H Hin Hwb HX Hsum Hlen.
  pose proof (forallb_true_In _ _ w H Hin) as Hw. cbn beta in Hw.
  destruct (bytes_desc segs st (we_base w) (we_len w)) as [d|] eqn:Hd; [|discriminate Hw]. apply bdesc_eqb_eq in Hw.
  destruct (desc_bytes_ext n0 E E' w HX Hwb) as (D1 & D2 & D3).
  rewrite <- D1, <- D2 in Hsum. rewrite <- D2 in Hlen. rewrite <- D1, <- D2, <- D3. unfold ent_bytes. rewrite <- Hw.
  exact (bytes_desc_sound E' st ms model _ _ d HS Hd Hsum Hlen).
Qed.

Lemma bytes_again_acc : forall n0 E E' st ms model wes w,
  st_ok segs OPS E' st ms model -> bytes_again segs st wes = true -> In w wes -> went_below n0 w = true -> env_ext n0 E E' ->
  bv_unsigned (den E (we_base w)) + bv_unsigned (den E (we_len w)) <= 2 ^ 47 -> bv_unsigned (den E (we_len w)) <= 2 ^ 30 ->
  forall i, 0 <= i < bv_unsigned (den E (we_len w)) -> fx_acc segs E' (s_regs st) (bv_unsigned (den E (we_base w)) + i).
Proof.
  intros n0 E E' st ms model wes w HS H Hin Hwb HX Hsum Hlen.
  pose proof (forallb_true_In _ _ w H Hin) as Hw. cbn beta in Hw.
  destruct (bytes_desc segs st (we_base w) (we_len w)) as [d|] eqn:Hd; [|discriminate Hw].
  destruct (desc_bytes_ext n0 E E' w HX Hwb) as (D1 & D2 & D3).
  rewrite <- D1, <- D2 in Hsum. rewrite <- D2 in Hlen. rewrite <- D1, <- D2.
  exact (bytes_desc_acc E' st ms model _ _ d HS Hd Hsum Hlen).
Qed.

Lemma read_bytes_of_rb : forall ms (A : Z) (n : nat) (bs : list byte),
  ms_rom ms = rom_of segs -> 0 <= A -> A + Z.of_nat n <= two64 -> Z.of_nat n <= 2 ^ 62 -> length bs = n ->
  (forall i, 0 <= i < Z.of_nat n -> rb segs (ms_mem ms) (A + i) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
  read_bytes_map (ms_read_byte ms) (Z_to_bv 64 A) (Z_to_bv 64 (Z.of_nat n)) = Some bs.
Proof.
  intros ms A n bs Hrom HA HAn Hn62 Hlen Hrb.
  apply read_bytes_map_of; [unfold two64; lia|]. apply (ov_read_aux ms n _ bs Hrom).
  apply (MemP.ov_read_bytes_rb segs (ms_mem ms) A n bs HA HAn); [|exact Hlen].
  intros i Hi. rewrite (Hrb i Hi). symmetry. apply nth_error_nth'. rewrite Hlen. lia.
Qed.

Section Site.
Variables (E0 : env) (n0 : int) (fd : Z) (wes : list went) (ra : int) (P : sstate) (K : TSet).
Variable MI : Model -> Prop.
Variable TPL : ltpl -> Prop.

Definition w0 : went := nth 0 wes wdflt.
Definition w1 : went := nth 1 wes wdflt.
Definition c1 : nat := length wes.
Definition oe1 : option (sv * sv) := match wes with [_; e] => Some (we_base e, we_len e) | _ => None end.
Definition uZ (w : word) : Z := bv_unsigned w.
Definition curw (X : ltpl) : went := if Nat.eqb (lt_c X) c1 then w0 else w1.
Definition blen (w : went) : Z := uZ (den E0 (we_len w)).
Definition bbase (w : went) : Z := uZ (den E0 (we_base w)).
Definition BS (w : went) : list byte := ent_bytes E0 w.
Definition tailB (X : ltpl) : list byte := if Nat.eqb (lt_c X) 2 then BS w1 else [].
Definition tailn (X : ltpl) : Z := if Nat.eqb (lt_c X) 2 then blen w1 else 0.
Definition REM (X : ltpl) (EX : env) : list byte :=
  skipn (Z.to_nat (blen (curw X) - uZ (ev EX (lt_vl X)))) (BS (curw X)) ++ tailB X.

Definition TI (X : ltpl) (EX : env) (n : Z) : Prop :=
  env_ext n0 E0 EX /\
  uZ (ev EX (lt_vb X)) + uZ (ev EX (lt_vl X)) = bbase (curw X) + blen (curw X) /\
  uZ (ev EX (lt_vl X)) <= blen (curw X) /\
  n = uZ (ev EX (lt_vr X)) /\
  n = uZ (ev EX (lt_vl X)) + tailn X.

Hypothesis Hfd12 : fd = 1 \/ fd = 2.
Hypothesis HMI : mstable MI.
Hypothesis Hfds : forall mo, MI mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)).
Hypothesis HK0 : K [].
Hypothesis HPwf : sstate_wfb P = true.
Hypothesis Hcont : forall E' ms' mo', eb E' = eb E0 -> MI mo' -> st_ok segs OPS E' P ms' mo' -> realizes segs (mkCfg ms' mo') K.
Hypothesis Hwes : forallb (went_below n0) wes = true.
Hypothesis Hc1 : c1 = 1%nat \/ c1 = 2%nat.
Hypothesis Hent : forall w, (w = w0 \/ (c1 = 2%nat /\ w = w1)) ->
  bbase w < 2 ^ 47 /\ blen w <= 2 ^ 30 /\ bbase w + blen w <= 2 ^ 47 /\ Z.of_nat (length (BS w)) = blen w.
Hypothesis HT : forall X, TPL X ->
  lt_n0 X = n0 /\ lt_shape_ok segs it L X fd oe1 = true /\ bytes_again segs (lt_st X) wes = true /\
  (lt_c X = 1%nat \/ (lt_c X = 2%nat /\ c1 = 2%nat)) /\
  exists xs ys zs,
    explore segs it FUEL ra (post_done X) = Some (xs, []) /\
    explore segs it FUEL ra (post_loop X false) = Some ([], ys) /\
    (lt_c X = 2%nat -> explore segs it FUEL ra (post_loop X true) = Some ([], zs)) /\
    (forall x, In x xs -> exit_ok n0 P x = true) /\
    (forall y, In y ys -> exists tgt, TPL tgt /\ lt_c tgt = lt_c X /\ lt_arrives segs L X false oe1 tgt y = true) /\
    (forall y, In y zs -> exists tgt, TPL tgt /\ lt_c tgt = 1%nat /\ lt_arrives segs L X true oe1 tgt y = true).

Lemma w0_in : In w0 wes.
Proof. clear Hfd12 HMI Hfds HK0 HPwf Hcont Hwes Hent HT. unfold w0, c1 in *. destruct wes as [|a l]; [cbn in Hc1; lia|]. left. reflexivity. Qed.
Lemma w1_in : c1 = 2%nat -> In w1 wes /\ wes = [w0; w1] /\ oe1 = Some (we_base w1, we_len w1).
Proof. clear Hfd12 HMI Hfds HK0 HPwf Hcont Hwes Hc1 Hent HT. unfold w0, w1, c1, oe1. destruct wes as [|a [|b [|? ?]]]; cbn; intros H; try lia. repeat split; auto. Qed.
Lemma curw_in : forall X, TPL X -> curw X = w0 \/ (c1 = 2%nat /\ curw X = w1).
Proof.
  intros X HX. destruct (HT X HX) as (_ & _ & _ & Hc & _). unfold curw.
  destruct (Nat.eqb (lt_c X) c1) eqn:Q; [left; reflexivity|]. apply Nat.eqb_neq in Q. right. split; [lia|reflexivity].
Qed.

Lemma length_REM : forall X EX n, TPL X -> TI X EX n -> Z.of_nat (length (REM X EX)) = n /\ 0 <= tailn X /\
  Z.of_nat (length (tailB X)) = tailn X.
Proof.
  intros X EX n HX (_ & Hsum & Hle & Hn1 & Hn2).
  destruct (Hent _ (curw_in X HX)) as (_ & _ & _ & HL).
  assert (HT2 : 0 <= tailn X /\ Z.of_nat (length (tailB X)) = tailn X).
  { unfold tailn, tailB. destruct (HT X HX) as (_ & _ & _ & Hc & _).
    destruct (Nat.eqb (lt_c X) 2) eqn:Q; [|cbn; lia]. apply Nat.eqb_eq in Q.
    destruct Hc as [Hc|[_ Hc2]]; [rewrite Hc in Q; discriminate Q|].
    destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (_ & B & _ & HL1). unfold blen in *. pose proof (u64_range (den E0 (we_len w1))). unfold uZ in *. lia. }
  split; [|exact HT2]. unfold REM. rewrite length_app, length_skipn. pose proof (u64_range (ev EX (lt_vl X))). unfold uZ in *. lia.
Qed.

Lemma w_bytes : forall X EX ms model w, st_ok segs OPS EX (lt_st X) ms model -> TPL X -> env_ext n0 E0 EX ->
  (w = w0 \/ (c1 = 2%nat /\ w = w1)) ->
  Z.of_nat (length (BS w)) = blen w /\
  forall i, 0 <= i < blen w -> rb segs (ms_mem ms) (bbase w + i) = Some (nth (Z.to_nat i) (BS w) (Z_to_bv 8 0)).
Proof.
  intros X EX ms model w HS HX HXenv Hw.
  destruct (HT X HX) as (_ & _ & Hba & _). destruct (Hent w Hw) as (B1 & B2 & B3 & _).
  assert (Hin : In w wes) by (destruct Hw as [-> | [H2 ->]]; [apply w0_in | apply (proj1 (w1_in H2))]).
  exact (bytes_again_sound n0 E0 EX (lt_st X) ms model wes w HS Hba Hin (forallb_true_In _ _ _ Hwes Hin) HXenv B3 B2).
Qed.

Lemma w_acc : forall X EX ms model w, st_ok segs OPS EX (lt_st X) ms model -> TPL X -> env_ext n0 E0 EX ->
  (w = w0 \/ (c1 = 2%nat /\ w = w1)) ->
  forall i, 0 <= i < blen w -> fx_acc segs EX (s_regs (lt_st X)) (bbase w + i).
Proof.
  intros X EX ms model w HS HX HXenv Hw.
  destruct (HT X HX) as (_ & _ & Hba & _). destruct (Hent w Hw) as (B1 & B2 & B3 & _).
  assert (Hin : In w wes) by (destruct Hw as [-> | [H2 ->]]; [apply w0_in | apply (proj1 (w1_in H2))]).
  exact (bytes_again_acc n0 E0 EX (lt_st X) ms model wes w HS Hba Hin (forallb_true_In _ _ _ Hwes Hin) HXenv B3 B2).
Qed.

Lemma w_den : forall EX w, env_ext n0 E0 EX -> (w = w0 \/ (c1 = 2%nat /\ w = w1)) ->
  bv_unsigned (den EX (we_base w)) = bbase w /\ bv_unsigned (den EX (we_len w)) = blen w /\
  den EX (we_base w) = Z_to_bv 64 (bbase w) /\ den EX (we_len w) = Z_to_bv 64 (blen w).
Proof.
  intros EX w HXenv Hw.
  assert (Hin : In w wes) by (destruct Hw as [-> | [H2 ->]]; [apply w0_in | apply (proj1 (w1_in H2))]).
  destruct (desc_bytes_ext n0 E0 EX w HXenv (forallb_true_In _ _ _ Hwes Hin)) as (D1 & D2 & _).
  rewrite D1, D2. unfold bbase, blen, uZ. rewrite !Z_to_bv_bv_unsigned. repeat split; reflexivity.
Qed.

Lemma loop_main : forall (m : nat) X EX ms model n,
  TPL X -> (Z.to_nat n < m)%nat -> MI model -> st_ok segs OPS EX (lt_st X) ms model -> TI X EX n ->
  realizes segs (mkCfg ms model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (REM X EX)) K).
Proof.
  induction m as [|m IH]; intros X EX ms model n HX Hm HMo HS HTI; [lia|].
  pose proof (Hfds model HMo) as Hfdsm.
  destruct (HT X HX) as (Hn0 & Hsh & Hba & Hc & xsX & ysX & zsX & XD & XN & XS & Hexits & Hns & Hsws).
  pose proof (lt_shape_ok_inv X fd oe1 Hsh) as SH. cbv zeta in SH.
  destruct SH as (L17 & L10 & L12 & Lb & Ll & Le1 & Lltu & Lleu & Lpc & Lwf & Lsv & Lkc & Lvb & Lvl & Lvr & Ln0 & Kvb & Kvl & Kvr & Lrem & Lf30 & Lecall).
  rewrite Hn0 in Lkc, Lvb, Lvl, Lvr, Ln0.
  destruct HTI as (HXenv & Hsum & Hle & Hn1 & Hn2).
  destruct (length_REM X EX n HX (conj HXenv (conj Hsum (conj Hle (conj Hn1 Hn2))))) as (HLR & Htn & HLT).
  set (st := lt_st X) in *.
  pose proof (so_facts _ _ _ _ _ _ HS) as Hfs. pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as MH.
  destruct (Hent _ (curw_in X HX)) as (Cb & Cl & Cbl & CL).

  destruct (lit_Z_sound EX _ _ L17) as [U17 _]. destruct (lit_Z_sound EX _ _ L10) as [U10 _]. destruct (lit_nat12_sound EX _ _ L12) as [U12 _].
  set (x8 := den EX (getr st X17)) in *.
  assert (Hvr30 : uZ (ev EX (lt_vr X)) <= 2 ^ 30).
  { pose proof (proj1 (Forall_forall _ _) Hfs _ Lf30) as F. cbn [fact_holds] in F. rewrite den_VAR, den_TWO30 in F. exact F. }
  pose proof (u64_range (ev EX (lt_vb X))) as Rvb. pose proof (u64_range (ev EX (lt_vl X))) as Rvl. pose proof (u64_range (ev EX (lt_vr X))) as Rvr.
  unfold uZ in *.

  destruct (w_bytes X EX ms model (curw X) HS HX HXenv (curw_in X HX)) as [BL BR].

  apply (rz_pend segs OPS EX st ms model _ HS (itab_ecall_at segs it (s_pc st) HIT Lecall)). fold x8.
  set (isys := sys_input segs (pend ms x8) x8).
  set (iovs := (ev EX (lt_vb X), ev EX (lt_vl X)) :: (if Nat.eqb (lt_c X) 2 then [(Z_to_bv 64 (bbase w1), Z_to_bv 64 (blen w1))] else [])).
  set (R := REM X EX) in *.
  assert (Ha1 : in_arg isys 1 = den EX (getr st X11)) by (unfold isys; rewrite <- (so_a1 segs OPS EX st ms model HS); reflexivity).
  pose proof (known_ltu_sound EX _ _ _ Hfs Lltu) as A1. rewrite den_TWO47 in A1.
  pose proof (known_leu_sound EX _ _ _ Hfs Lleu) as A2. rewrite den_TWO47, den_add in A2. cbn [den] in A2.
  rewrite add_small in A2 by (rewrite wbv_unsigned, wlit_ok; change (to_Z 32%uint63) with 32; unfold two64; lia).
  rewrite wbv_unsigned, wlit_ok in A2. change (to_Z 32%uint63) with 32 in A2.
  assert (Hcnt : iovcnt32 (in_arg isys 2) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold isys. change (in_arg (sys_input segs (pend ms x8) x8) 2) with (ms_gpr (pend ms x8) 2). rewrite pend_gpr, (so_a2 segs OPS EX st ms model HS).
    unfold iovcnt32, abi_low32. rewrite U12. replace (length iovs) with (lt_c X) by (unfold iovs; destruct Hc as [-> | [-> _]]; reflexivity).
    rewrite Z.mod_small by (destruct Hc as [-> | [-> _]]; cbn; lia). reflexivity. }
  assert (HSPEC : forall o, syscall_spec isys model o <->
     (R = [] /\ o = Ok (wv_eff0 isys) model []) \/
     (exists k, (1 <= k)%nat /\ (k <= length R)%nat /\ o = Ok (wv_eff isys iovs k) model (map (WriteEv (Z_to_bv 64 fd)) (firstn k R)))).
  { intros o.
    assert (HR : R = concat ((skipn (Z.to_nat (blen (curw X) - bv_unsigned (ev EX (lt_vl X)))) (BS (curw X))) :: (if Nat.eqb (lt_c X) 2 then [BS w1] else []))).
    { unfold R, REM, tailB. destruct (Nat.eqb (lt_c X) 2); cbn [concat]; rewrite ?app_nil_r; reflexivity. }
    rewrite HR. apply (writev_outcome isys model o (Z_to_bv 64 fd) iovs).
    - unfold isys. rewrite in_sysno_sys_input. exact U17.
    - replace (fd32 (in_arg isys 0)) with (Z_to_bv 64 fd); [exact Hfdsm|].
      unfold isys. change (in_arg (sys_input segs (pend ms x8) x8) 0) with (ms_gpr (pend ms x8) 0). rewrite pend_gpr, (so_a0 segs OPS EX st ms model HS).
      symmetry. rewrite fd32_id by (rewrite U10; lia). apply bv_eq. rewrite U10, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. lia.
    - unfold w_is0, bv_eqb. rewrite !Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). apply Z.eqb_neq. change (bv_wrap 64 0) with 0. lia.
    - unfold iovs. destruct (Nat.eqb (lt_c X) 2); cbn; auto.
    - exact Hcnt.
    - rewrite Ha1. unfold access_okb, TASK_SIZE. apply andb_true_intro. split; apply Z.leb_le; unfold iovs; destruct (Nat.eqb (lt_c X) 2); cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia.
    - rewrite Ha1. unfold iovs.
      assert (M8 : forall a v, load8 segs st a = Some v -> read_u64 (in_mem isys) (den EX a) = Some (den EX v)).
      { intros a v Hl. destruct (load8_sound EX st ms model a v HS Hl) as (bs & _ & _ & HU). unfold isys. exact HU. }
      cbn [iov_at]. rewrite <- !den_addz_bv. split; [rewrite (M8 _ _ Lb), den_VAR; reflexivity|]. split; [rewrite (M8 _ _ Ll), den_VAR; reflexivity|].
      split; [lia|].
      destruct (Nat.eqb (lt_c X) 2) eqn:Q2; [|exact I]. apply Nat.eqb_eq in Q2.
      destruct (Le1 Q2) as (b1 & l1 & He1 & Lb1 & Ll1). destruct Hc as [Hc|[_ Hc2]]; [rewrite Hc in Q2; discriminate Q2|].
      destruct (w1_in Hc2) as (_ & _ & Hoe). rewrite Hoe in He1. injection He1 as <- <-.
      destruct (w_den EX w1 HXenv (or_intror (conj Hc2 eq_refl))) as (_ & _ & Db1 & Dl1).
      cbn [iov_at]. rewrite <- !den_addz_bv. split; [rewrite (M8 _ _ Lb1), Db1; reflexivity|]. split; [rewrite (M8 _ _ Ll1), Dl1; reflexivity|]. split; [|exact I].
      destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (_ & B & _).
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; unfold blen, uZ in *; pose proof (u64_range (den E0 (we_len w1))); lia). lia.
    - unfold iovs. constructor; [cbn [fst snd]; unfold access_okb, TASK_SIZE; apply andb_true_intro; split; apply Z.leb_le; lia|].
      destruct (Nat.eqb (lt_c X) 2) eqn:Q2; [|constructor]. apply Nat.eqb_eq in Q2. destruct Hc as [Hc|[_ Hc2]]; [rewrite Hc in Q2; discriminate Q2|].
      constructor; [|constructor]. cbn [fst snd].
      destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (B1 & B2 & B3 & _).
      pose proof (u64_range (den E0 (we_len w1))) as R1. pose proof (u64_range (den E0 (we_base w1))) as R2. unfold bbase, blen, uZ in B1, B2, B3 |- *.
      unfold access_okb, TASK_SIZE. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (unfold bv_modulus; lia).
      apply andb_true_intro. split; apply Z.leb_le; lia.
    - unfold iovs. constructor.
      + cbn [fst snd].
        assert (RB : read_bytes_map (ms_read_byte ms) (Z_to_bv 64 (bv_unsigned (ev EX (lt_vb X)))) (Z_to_bv 64 (Z.of_nat (Z.to_nat (bv_unsigned (ev EX (lt_vl X))))))
                     = Some (skipn (Z.to_nat (blen (curw X) - bv_unsigned (ev EX (lt_vl X)))) (BS (curw X)))).
        { apply (read_bytes_of_rb ms); [exact (so_rom _ _ _ _ _ _ HS) | lia | unfold two64; lia | lia | rewrite length_skipn; lia |].
          intros i Hi. rewrite nth_skipn.
          replace (bv_unsigned (ev EX (lt_vb X)) + i) with (bbase (curw X) + (blen (curw X) - bv_unsigned (ev EX (lt_vl X)) + i)) by lia.
          rewrite BR by lia. f_equal. f_equal. lia. }
        rewrite Z2Nat.id, !Z_to_bv_bv_unsigned in RB by lia. exact RB.
      + destruct (Nat.eqb (lt_c X) 2) eqn:Q2; [|constructor]. apply Nat.eqb_eq in Q2. destruct Hc as [Hc'|[_ Hc2]]; [rewrite Hc' in Q2; discriminate Q2|].
        constructor; [|constructor]. cbn [fst snd].
        destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (B1 & B2 & B3 & BL1).
        destruct (w_bytes X EX ms model w1 HS HX HXenv (or_intror (conj Hc2 eq_refl))) as [BL' BR'].
        pose proof (u64_range (den E0 (we_len w1))) as R1. pose proof (u64_range (den E0 (we_base w1))) as R2.
        assert (Rb : 0 <= bbase w1) by (unfold bbase, uZ; lia). assert (Rl : 0 <= blen w1) by (unfold blen, uZ; lia).
        assert (RB : read_bytes_map (ms_read_byte ms) (Z_to_bv 64 (bbase w1)) (Z_to_bv 64 (Z.of_nat (Z.to_nat (blen w1)))) = Some (BS w1)).
        { apply (read_bytes_of_rb ms); [exact (so_rom _ _ _ _ _ _ HS) | lia | unfold two64; lia | lia | lia |].
          intros i Hi. apply BR'. lia. }
        rewrite Z2Nat.id in RB by lia. exact RB.
    - unfold iovs. cbn [iovs_total]. destruct (Nat.eqb (lt_c X) 2) eqn:Q2; cbn [iovs_total].
      + apply Nat.eqb_eq in Q2. destruct Hc as [Hc'|[_ Hc2]]; [rewrite Hc' in Q2; discriminate Q2|].
        destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (_ & B & _). pose proof (u64_range (den E0 (we_len w1))) as R1.
        rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus, blen, uZ in *; lia).
        unfold tailn in Hn2. rewrite Q2 in Hn2. cbn [Nat.eqb] in Hn2. lia.
      + unfold tailn in Hn2. rewrite Q2 in Hn2. cbn [Nat.eqb] in Hn2. lia. }
  assert (Eisys : sys_input segs (pend ms x8) x8 = isys) by reflexivity. clearbody isys.

  pose proof (u64_range (den EX (getr st X11))) as Ra1.
  assert (HLiov : (length iovs = 1 \/ length iovs = 2)%nat) by (unfold iovs; destruct (Nat.eqb (lt_c X) 2); cbn; auto).
  assert (DESC : forall i j, (i < length iovs)%nat -> 0 <= j < 16 ->
             fx_acc segs EX (s_regs st) (bv_unsigned (den EX (getr st X11)) + 16 * Z.of_nat i + j)).
  { intros i j Hi Hj. destruct i as [|[|i]].
    - rewrite Z.mul_0_r, Z.add_0_r. exact (ent_acc EX st ms model (getr st X11) _ _ HS ltac:(unfold two64; lia) Lb Ll j Hj).
    - assert (Q2 : lt_c X = 2%nat).
      { unfold iovs in Hi. destruct (Nat.eqb (lt_c X) 2) eqn:Q; [apply Nat.eqb_eq; exact Q | cbn in Hi; lia]. }
      destruct (Le1 Q2) as (b1 & l1 & _ & Lb1 & Ll1).
      pose proof (ent_acc EX st ms model (addz (getr st X11) 16) _ _ HS ltac:(rewrite den_addz by (unfold two64; lia); unfold two64; lia) Lb1 Ll1 j Hj) as F.
      rewrite den_addz in F by (unfold two64; lia). change (16 * Z.of_nat 1) with 16. exact F.
    - exfalso. destruct HLiov as [Q|Q]; rewrite Q in Hi; lia. }
  assert (DATA : forall b len j, In (b, len) iovs -> 0 <= j < bv_unsigned len -> fx_acc segs EX (s_regs st) (bv_unsigned b + j)).
  { intros b len j Hin Hj. unfold iovs in Hin. destruct Hin as [Hin|Hin].
    - injection Hin as <- <-.
      pose proof (w_acc X EX ms model (curw X) HS HX HXenv (curw_in X HX) (blen (curw X) - bv_unsigned (ev EX (lt_vl X)) + j)) as F.
      replace (bv_unsigned (ev EX (lt_vb X)) + j) with (bbase (curw X) + (blen (curw X) - bv_unsigned (ev EX (lt_vl X)) + j)) by lia.
      apply F. lia.
    - destruct (Nat.eqb (lt_c X) 2) eqn:Q2; [|destruct Hin]. destruct Hin as [Hin|[]]. injection Hin as <- <-.
      apply Nat.eqb_eq in Q2. destruct Hc as [Hc'|[_ Hc2]]; [rewrite Hc' in Q2; discriminate Q2|].
      destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (B1 & B2 & B3 & _).
      pose proof (u64_range (den E0 (we_len w1))) as R1. pose proof (u64_range (den E0 (we_base w1))) as R2.
      unfold bbase, blen, uZ in B1, B2, B3.
      assert (Ub1 : bv_unsigned (Z_to_bv 64 (bbase w1)) = bbase w1) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus, bbase, uZ; lia).
      assert (Ul1 : bv_unsigned (Z_to_bv 64 (blen w1)) = blen w1) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus, blen, uZ; lia).
      rewrite Ul1 in Hj. rewrite Ub1.
      exact (w_acc X EX ms model w1 HS HX HXenv (or_intror (conj Hc2 eq_refl)) j Hj). }
  assert (ACC : forall k a nn j, In (a, nn) (wv_cps isys iovs k) -> 0 <= j < Z.of_nat nn ->
             op_cov OPS (insts EX (s_ops st)) (bv_unsigned a + j)).
  { intros k a nn j Hin Hj. apply (so_cover _ _ _ _ _ _ HS).
    destruct (wv_cps_in isys iovs k a nn HLiov Hcnt Hin) as [[-> (i & Hi & Hx)] | (len & Hl & Hlen)].
    - rewrite Hx, Ha1, bv_wrap_small by (unfold bv_modulus; destruct HLiov as [Q|Q]; rewrite Q in Hi; lia).
      apply DESC; [exact Hi | cbn in Hj; lia].
    - apply (DATA a len j Hl). lia. }
  assert (ACC0 : forall a nn j, In (a, nn) (syscall_effect_accesses (wv_eff0 isys)) -> 0 <= j < Z.of_nat nn ->
             op_cov OPS (insts EX (s_ops st)) (bv_unsigned a + j)).
  { intros a nn j Hin Hj. apply (so_cover _ _ _ _ _ _ HS).
    destruct (wv_eff0_in isys (length iovs) a nn HLiov Hcnt Hin) as [-> (i & Hi & Hx)].
    rewrite Hx, Ha1, bv_wrap_small by (unfold bv_modulus; destruct HLiov as [Q|Q]; rewrite Q in Hi; lia).
    apply DESC; [exact Hi | cbn in Hj; lia]. }

  assert (MAT : forall acc, (forall a nn j, In (a, nn) acc -> 0 <= j < Z.of_nat nn -> op_cov OPS (insts EX (s_ops st)) (bv_unsigned a + j)) ->
            materialize_model_accesses model acc = Some (matz model acc) /\ MI (matz model acc) /\ st_ok segs OPS EX st ms (matz model acc)).
  { intros acc Hcv. destruct (sys_acc OPS EX (s_ops st) (ms_mem ms) model acc (so_mf _ _ _ _ _ _ HS) (so_ops _ _ _ _ _ _ HS) Hcv) as (M1 & M2 & M3).
    split; [exact M1|]. split; [exact (HMI _ _ _ HMo M1)|]. exact (st_ok_model segs OPS EX st ms model _ HS M2 M3). }

  assert (POST : forall (mo2 : Model) (v : sv) (fs' : list fact) (n' : int) (E' : env) (ret : word),
            st_ok segs OPS E' st ms mo2 -> den E' v = ret -> Forall (fact_holds E') fs' ->
            st_ok segs OPS E' (svc_ret st v fs' n') (svc_post ms x8 ret) mo2).
  { intros mo2 v fs' n' E' ret HS' Hv Hfs'. apply (st_ok_svc_return segs OPS E' st ms mo2 mo2 x8 ret v fs' n' HS' Lpc Hv Hfs').
    - exact (so_mf _ _ _ _ _ _ HS').
    - exact (so_ops _ _ _ _ _ _ HS'). }

  assert (DONE : forall mo2, MI mo2 -> st_ok segs OPS EX st ms mo2 -> realizes segs (mkCfg (svc_post ms x8 (Z_to_bv 64 n)) mo2) K).
  { intros mo2 HM2 HS2.
    assert (HSd : st_ok segs OPS EX (post_done X) (svc_post ms x8 (Z_to_bv 64 n)) mo2).
    { change (post_done X) with (svc_ret st (VAR (lt_vr X)) [] (s_next st)). apply (POST mo2 _ _ _ EX _ HS2); [|constructor].
      rewrite den_VAR. apply bv_eq. rewrite Z_to_bv_unsigned, bv_wrap_small; [lia | unfold bv_modulus; lia]. }
    apply (explore_sound FUEL ra (post_done X) _ _ XD MI HMI EX _ mo2 K HSd HM2).
    - intros x ms' mo' Hin _ HM' HSx. destruct (exit_ok_sound n0 P x EX ms' mo' HPwf (Hexits x Hin) HSx) as (E' & HSP & HXE).
      apply (Hcont E' ms' mo'); [| exact HM' | exact HSP]. rewrite HXE. exact (proj1 HXenv).
    - intros y ms' mo' Hin. destruct Hin. }
  destruct (Z.eq_dec n 0) as [Hz|Hnz].
  -
    assert (HR0 : R = []) by (destruct R; [reflexivity | cbn in HLR; lia]).
    destruct (MAT _ ACC0) as (M1 & M2 & M3). set (mo0 := matz model (syscall_effect_accesses (wv_eff0 isys))) in *.
    apply (rz_silent_all segs _ unit (fun _ => mkCfg (advance_past_svc (apply_effect (pend ms x8) (wv_eff0 isys))) mo0) tt).
    + apply (node_gen_a segs (pend ms x8) model x8 unit (fun _ => wv_eff0 isys) (fun _ => model) (fun _ => mo0) (fun _ => []) MH eq_refl
               (fun _ => nonspur_nonalloc segs _ _ _ _ (nonalloc_eq x8 _ U17 eq_refl))).
      * intros o. rewrite Eisys, (HSPEC o). rewrite HR0. split.
        -- intros [[_ ->] | (k & Hk1 & Hk2 & _)]; [exists tt; reflexivity | cbn in Hk2; lia].
        -- intros [[] ->]. left. split; reflexivity.
      * intros _. split; [exact MH | exact M1].
    + intros []. rewrite HR0. cbn [map]. unfold wv_eff0. rewrite apply_effect_nowrite. fold (svc_post ms x8 (Z_to_bv 64 0)).
      rewrite <- Hz. apply (rz_conseq segs _ K); [exact (DONE mo0 M2 M3) | apply t_eq_sym; apply t_emit_nil_eq; exact HK0].
  -
    assert (HRn : (1 <= length R)%nat) by lia.
    set (evs := fun i : wr_index R => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) R)).
    set (mo2 := fun i : wr_index R => matz model (wv_cps isys iovs (proj1_sig i))).
    set (nx := fun i : wr_index R => mkCfg (advance_past_svc (apply_effect (pend ms x8) (wv_eff isys iovs (proj1_sig i)))) (mo2 i)).
    assert (NODE : node_ok segs (mkCfg (pend ms x8) model) (wr_index R) evs nx).
    { apply (node_gen_a segs (pend ms x8) model x8 (wr_index R) (fun i => wv_eff isys iovs (proj1_sig i)) (fun _ => model) mo2 evs MH eq_refl
               (fun _ => nonspur_nonalloc segs _ _ _ _ (nonalloc_eq x8 _ U17 eq_refl))).
      - intros o. rewrite Eisys, (HSPEC o). split.
        + intros [[HR0 _] | (k & Hk1 & Hk2 & ->)]; [rewrite HR0 in HRn; cbn in HRn; lia|].
          exists (exist _ k (conj Hk1 Hk2)). reflexivity.
        + intros [[k [Hk1 Hk2]] ->]. right. exists k. cbn [proj1_sig]. auto.
      - intros i. split; [exact MH|]. rewrite wv_eff_accesses. exact (proj1 (MAT _ (ACC (proj1_sig i)))). }
    apply (rz_conseq segs _ (t_alt (fun i : wr_index R => t_emit (evs i) (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn (proj1_sig i) R)) K)))).
    2:{ apply t_alt_wall; [exact HK0 | exact HRn]. }
    apply (rz_node segs _ (wr_index R) evs nx _ (wr_full R HRn) NODE).
    intros [k [Hk1 Hk2]]. cbn [proj1_sig]. unfold nx, mo2. cbn [proj1_sig]. unfold wv_eff. rewrite apply_effect_nowrite.
    fold (svc_post ms x8 (Z_to_bv 64 (Z.of_nat k))).
    destruct (MAT _ (ACC k)) as (_ & HMk & HSmk). set (mok := matz model (wv_cps isys iovs k)) in *.
    destruct (Nat.eq_dec k (length R)) as [Hkn|Hkn].
    +
      rewrite Hkn, skipn_all. cbn [map]. replace (Z.of_nat (length R)) with n by lia.
      apply (rz_conseq segs _ K); [exact (DONE mok HMk HSmk) | apply t_eq_sym; apply t_emit_nil_eq; exact HK0].
    +
      assert (Hk : 1 <= Z.of_nat k < n) by lia.
      set (kw := Z_to_bv 64 (Z.of_nat k)). set (kc := lt_kc X) in *. set (Ek := env_upd EX kc kw).
      assert (Ukw : bv_unsigned kw = Z.of_nat k) by (unfold kw; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
      assert (HXk : env_ext kc EX Ek) by apply env_upd_ext.
      assert (HSk : st_ok segs OPS Ek st ms mok) by (apply (st_ok_reval segs OPS kc EX Ek HXk st ms mok); [lia | exact Lsv | exact HSmk]).
      assert (Evb : ev Ek (lt_vb X) = ev EX (lt_vb X)) by (apply env_upd_other; intros Q; apply (f_equal to_Z) in Q; lia).
      assert (Evl : ev Ek (lt_vl X) = ev EX (lt_vl X)) by (apply env_upd_other; intros Q; apply (f_equal to_Z) in Q; lia).
      assert (Evr : ev Ek (lt_vr X) = ev EX (lt_vr X)) by (apply env_upd_other; intros Q; apply (f_equal to_Z) in Q; lia).
      assert (Ekc : ev Ek kc = kw) by apply env_upd_same.
      set (sw := Nat.eqb (lt_c X) 2 && Z.ltb (bv_unsigned (ev EX (lt_vl X))) (Z.of_nat k)).
      assert (HSp : st_ok segs OPS Ek (post_loop X sw) (svc_post ms x8 kw) mok).
      { change (post_loop X sw) with
          (svc_ret st (VAR kc) [FULe (VL (wlit 1%uint63)) (VAR kc); FULt (VAR kc) (VAR (lt_vr X)); FULt (VAR kc) TWO30;
                                (if sw then FULt (VAR (lt_vl X)) (VAR kc) else FULe (VAR kc) (VAR (lt_vl X)));
                                FULe (sv_alu ALU_SUB (VAR (lt_vr X)) (VAR kc)) TWO30] (PrimInt63.add kc 1%uint63)).
        apply (POST mok _ _ _ Ek _ HSk); [rewrite den_VAR; exact Ekc|].
        repeat apply Forall_cons; try apply Forall_nil; cbn [fact_holds]; rewrite ?den_VAR, ?Ekc, ?Evr, ?Evl, ?den_TWO30.
        - cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 1%uint63) with 1. lia.
        - lia.
        - lia.
        - destruct sw eqn:Hsw.
          + unfold sw in Hsw. apply andb_prop in Hsw as [_ Hsw]. apply Z.ltb_lt in Hsw. cbn [fact_holds]. rewrite den_VAR, Evl, den_VAR, Ekc. lia.
          + cbn [fact_holds]. rewrite !den_VAR, Ekc, Evl.
            unfold sw in Hsw. destruct (Nat.eqb (lt_c X) 2) eqn:Q2.
            * cbn [andb] in Hsw. apply Z.ltb_ge in Hsw. lia.
            * unfold tailn in Hn2. rewrite Q2 in Hn2. cbn [Nat.eqb] in Hn2. lia.
        - rewrite den_sub, !den_VAR, Ekc, Evr. rewrite sub_small by lia. lia. }
      assert (XL : explore segs it FUEL ra (post_loop X sw) = Some ([], if sw then zsX else ysX)).
      { destruct sw eqn:Hsw; [|exact XN]. apply XS. unfold sw in Hsw. apply andb_prop in Hsw as [Q _]. apply Nat.eqb_eq in Q. exact Q. }
      apply (explore_sound FUEL ra (post_loop X sw) _ _ XL MI HMI Ek _ mok _ HSp HMk); [intros x ms' mo' Hin; destruct Hin|].
      intros y ms'' mo'' Hin Hye HMy HSy.
      assert (ARR : exists tgt, TPL tgt /\ lt_c tgt = (if sw then 1%nat else lt_c X) /\ lt_arrives segs L X sw oe1 tgt y = true).
      { destruct sw; [exact (Hsws y Hin) | exact (Hns y Hin)]. }
      destruct ARR as (tgt & Htgt & Hctgt & Harr).
      destruct (HT tgt Htgt) as (Tn0 & Tsh & _). pose proof (lt_shape_ok_inv tgt fd oe1 Tsh) as TSH. cbv zeta in TSH.
      destruct TSH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Twf & _).
      destruct (lt_arrives_sound X sw oe1 tgt y Ek ms'' mo'' Twf Harr HSy) as (E' & b & l & HS' & HXE' & _ & _ & _ & Evb' & Evl' & Evr' & Drem & Dform).
      rewrite Tn0 in HXE'. fold kc in Dform, Drem. rewrite Ekc, Evr in Drem. rewrite ?Ekc, ?Evb, ?Evl in Dform.

      assert (HTI' : TI tgt E' (n - Z.of_nat k) /\ REM tgt E' = skipn k R).
      { unfold TI, REM. rewrite Evb', Evl', Evr', Drem. rewrite sub_small by (rewrite Ukw; lia). rewrite Ukw.
        assert (HXE0 : env_ext n0 E0 E').
        { eapply env_ext_trans; [reflexivity | exact HXenv |]. eapply env_ext_trans; [| apply (env_ext_weaken kc n0); [lia | exact HXk] | exact HXE']. lia. }
        destruct sw eqn:Hsw.
        -
          unfold sw in Hsw. apply andb_prop in Hsw as [Q2 Hlt]. apply Nat.eqb_eq in Q2. apply Z.ltb_lt in Hlt.
          destruct Hc as [Hc'|[_ Hc2]]; [rewrite Hc' in Q2; discriminate Q2|].
          destruct Dform as (b1 & l1 & He1 & Db & Dl). destruct (w1_in Hc2) as (W1in & _ & Hoe). rewrite Hoe in He1. injection He1 as <- <-.
          rewrite ?Evl in Db. rewrite ?Evl in Dl.
          destruct (w_den Ek w1 ltac:(eapply env_ext_trans; [reflexivity | exact HXenv | apply (env_ext_weaken kc n0); [lia | exact HXk]])
                      (or_intror (conj Hc2 eq_refl))) as (_ & _ & D1 & D2). rewrite D1 in Db. rewrite D2 in Dl.
          destruct (Hent w1 (or_intror (conj Hc2 eq_refl))) as (B1 & B2 & B3 & BL1).
          pose proof (u64_range (den E0 (we_len w1))) as R1. pose proof (u64_range (den E0 (we_base w1))) as R2.
          assert (Rb : 0 <= bbase w1) by (unfold bbase, uZ; lia). assert (Rl : 0 <= blen w1) by (unfold blen, uZ; lia).
          assert (Hcw : curw tgt = w1) by (unfold curw; rewrite Hctgt, Hc2; reflexivity).
          assert (HcwX : curw X = w0) by (unfold curw; rewrite Q2, Hc2; reflexivity).
          unfold tailn, tailB in Hn2, Htn, HLT |- *. rewrite Hctgt, Hcw. cbn [Nat.eqb].
          rewrite Q2 in Hn2. cbn [Nat.eqb] in Hn2. rewrite HcwX in Hsum, Hle, CL.
          assert (Udl : bv_unsigned (kw - ev EX (lt_vl X))%bv = Z.of_nat k - bv_unsigned (ev EX (lt_vl X))) by (rewrite sub_small; rewrite Ukw; lia).
          assert (Ub1 : bv_unsigned (Z_to_bv 64 (bbase w1)) = bbase w1) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
          assert (Ul1 : bv_unsigned (Z_to_bv 64 (blen w1)) = blen w1) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
          unfold uZ. rewrite Db, Dl.
          rewrite (add_small (Z_to_bv 64 (bbase w1))) by (rewrite Udl, Ub1; unfold two64; lia).
          rewrite (sub_small (Z_to_bv 64 (blen w1))) by (rewrite Udl, Ul1; lia).
          rewrite Udl, Ub1, Ul1.
          split; [split; [exact HXE0|]; lia|].
          unfold R, REM, tailB, uZ. rewrite HcwX, Q2. cbn [Nat.eqb]. rewrite skipn_app, length_skipn, app_nil_r.
          rewrite (skipn_all2 (n:=k)) by (rewrite length_skipn; lia). cbn [app]. f_equal. lia.
        -
          destruct Dform as [Db Dl].
          assert (Hcw : curw tgt = curw X) by (unfold curw; rewrite Hctgt; reflexivity).
          assert (Hkle : Z.of_nat k <= bv_unsigned (ev EX (lt_vl X))).
          { unfold sw in Hsw. destruct (Nat.eqb (lt_c X) 2) eqn:Q2; [cbn [andb] in Hsw; apply Z.ltb_ge in Hsw; lia |].
            unfold tailn in Hn2. rewrite Q2 in Hn2. cbn [Nat.eqb] in Hn2. lia. }
          unfold tailn, tailB in Hn2, Htn, HLT |- *. rewrite !Hctgt, !Hcw.
          unfold uZ. rewrite Db, Dl.
          rewrite (add_small (ev EX (lt_vb X)) kw) by (rewrite Ukw; unfold two64; lia).
          rewrite (sub_small (ev EX (lt_vl X)) kw) by (rewrite Ukw; lia). rewrite Ukw.
          split; [split; [exact HXE0|]; lia|].
          unfold R, REM, tailB, uZ. rewrite skipn_app, length_skipn, skipn_skipn.
          replace (k - (length (BS (curw X)) - Z.to_nat (blen (curw X) - bv_unsigned (ev EX (lt_vl X)))))%nat with 0%nat by lia.
          cbn [skipn]. f_equal. f_equal. lia. }
      destruct HTI' as [HTI' HREM']. rewrite <- HREM'.
      apply (IH tgt E' ms'' mo'' (n - Z.of_nat k) Htgt ltac:(lia) HMy HS' HTI').
Qed.
End Site.

Definition explore_eqs (ra : int) (t : tplcert) : Prop :=
  explore segs it FUEL ra (post_done (tc_tpl t)) = Some (tc_exits t, []) /\
  explore segs it FUEL ra (post_loop (tc_tpl t) false) = Some ([], tc_ns t) /\
  (lt_c (tc_tpl t) = 2%nat -> explore segs it FUEL ra (post_loop (tc_tpl t) true) = Some ([], tc_sw t)).

Theorem stdio_write_sound : forall (MP : Model -> Prop), mstable MP -> forall T P C E ms model K,
  sw_verify segs it L fdok T P C = true ->
  run segs it [] T = SStop KEcall (c_T1 C) ->
  Forall (explore_eqs (c_ra C)) (c_tpls C) ->
  st_ok segs OPS E T ms model -> MP model -> K [] ->
  (forall E' ms' mo', eb E' = eb E -> MP mo' -> st_ok segs OPS E' P ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) (t_emit (map (WriteEv (sw_fd C)) (sw_bytes C E)) K).
Proof.
  intros MP HMP T P C E ms model K HV Hrun HX HS HMo HK0 Hcont.
  unfold sw_verify in HV. cbv zeta in HV.
  apply andb_true_split in HV as [HV Vtpls]. apply andb_true_split in HV as [HV VA]. apply andb_true_split in HV as [HV Vwes].
  apply andb_true_split in HV as [HV Vfdok]. apply andb_true_split in HV as [HV Vlits]. apply andb_true_split in HV as [Vwf Vra].
  destruct C as [T1 ra fd wes tpls]. cbn [c_T1 c_ra c_fd c_wes c_tpls] in *.
  destruct (lit_int (getr T X1)) as [ra'|] eqn:Hra; [|discriminate Vra]. apply Uint63.eqb_correct in Vra. subst ra'.
  destruct (lit_Z (getr T1 X17)) as [no|] eqn:H17; [|discriminate Vlits].
  destruct (lit_Z (getr T1 X10)) as [fd'|] eqn:H10; [|discriminate Vlits].
  destruct (lit_nat12 (getr T1 X12)) as [c1'|] eqn:H12; [|discriminate Vlits].
  apply andb_true_split in Vlits as [Vlits Vc1]. apply andb_true_split in Vlits as [Vlits Vfd12]. apply andb_true_split in Vlits as [Vno Vfd].
  apply Z.eqb_eq in Vno. apply Z.eqb_eq in Vfd. apply Nat.eqb_eq in Vc1. subst no fd'.
  assert (Hfd12 : fd = 1 \/ fd = 2) by (apply orb_prop in Vfd12; destruct Vfd12 as [X1|X1]; apply Z.eqb_eq in X1; auto).
  destruct (lit_nat12_sound E _ _ H12) as [_ Hc1']. assert (Hc1 : length wes = 1%nat \/ length wes = 2%nat) by (rewrite <- Vc1; exact Hc1').
  destruct tpls as [|tA tpls']; [discriminate VA|].
  apply andb_true_split in VA as [VA Veq]. apply andb_true_split in VA as [VcA VA].
  apply Nat.eqb_eq in VcA.
  destruct (lt_subst segs L (tc_tpl tA) T1) as [sgA|] eqn:HsgA; [|discriminate VA].
  apply andb_true_split in VA as [VA Bvr]. apply andb_true_split in VA as [VA Bvl]. apply andb_true_split in VA as [VA Bvb].
  apply andb_true_split in VA as [ENA IDA].

  pose proof (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) as MH.
  destruct (run_sound segs OPS E T ms model it [] KEcall T1 HIT HS Hrun) as (ms1 & mo1 & Hms & HS1).
  pose proof (asteps_stable segs MP ms model ms1 mo1 HMP Hms HMo) as HMo1.
  apply (ShapeAcc.rz_asteps segs ms model ms1 mo1 _ MH Hms).

  set (A := tc_tpl tA) in *.
  assert (HTA : In tA (tA :: tpls')) by (left; reflexivity).
  pose proof (forallb_true_In _ _ tA Vtpls HTA) as CA. unfold tpl_checks in CA.
  apply andb_true_split in CA as [CA _]. apply andb_true_split in CA as [CA _]. apply andb_true_split in CA as [CA _].
  apply andb_true_split in CA as [CA _]. apply andb_true_split in CA as [CA _]. apply andb_true_split in CA as [An0 Ash].
  apply Uint63.eqb_correct in An0.
  pose proof (lt_shape_ok_inv A fd (oe1_of wes) Ash) as SHA. cbv zeta in SHA.
  destruct SHA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Awf & _).
  pose proof (entails_sound segs OPS E T1 (lt_st A) sgA ms1 mo1 Awf ENA HS1) as HSA.
  set (EA := subst_env E sgA) in *.
  pose proof (so_facts _ _ _ _ _ _ HS1) as Hfs1.

  assert (Hent0 : forall w, In w wes -> bv_unsigned (den E (we_base w)) < 2 ^ 47 /\ bv_unsigned (den E (we_len w)) <= 2 ^ 30 /\
                       bv_unsigned (den E (we_base w)) + bv_unsigned (den E (we_len w)) <= 2 ^ 47 /\ went_below (s_next T) w = true).
  { intros w Hw. pose proof (forallb_true_In _ _ w Vwes Hw) as Y. apply andb_true_split in Y as [Y1 Y2].
    destruct (ent_ok_sound E (s_facts T1) (we_base w, we_len w) Hfs1 Y1) as (B1 & B2 & B3). cbn [fst snd] in B1, B2, B3. auto. }
  assert (Hwb : forallb (went_below (s_next T)) wes = true).
  { apply forallb_forall. intros w Hw. exact (proj2 (proj2 (proj2 (Hent0 w Hw)))). }

  set (MI := fun mo : Model => MP mo /\ fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))).
  assert (HMI : mstable MI).
  { intros mo acc mo' [H1 H2] M. split; [exact (HMP _ _ _ H1 M)|]. rewrite (mat_fds _ _ _ M). exact H2. }
  assert (MAIN := loop_main E (s_next T) fd wes ra P K MI (fun X => exists t, In t (tA :: tpls') /\ X = tc_tpl t) Hfd12
            HMI (fun mo H => proj2 H) HK0 Vwf (fun E' ms' mo' He Hm HSP => Hcont E' ms' mo' He (proj1 Hm) HSP) Hwb Hc1).
  assert (HENT : forall w, w = w0 wes \/ (c1 wes = 2%nat /\ w = w1 wes) ->
     bbase E w < 2 ^ 47 /\ blen E w <= 2 ^ 30 /\ bbase E w + blen E w <= 2 ^ 47 /\ Z.of_nat (length (BS E w)) = blen E w).
  { intros w Hw. unfold bbase, blen, BS, uZ.
    assert (Hin : In w wes).
    { destruct Hw as [-> | [H2 ->]]; [apply (w0_in wes Hc1) | apply (proj1 (w1_in wes H2))]. }
    destruct (Hent0 w Hin) as (B1 & B2 & B3 & B4). repeat split; try assumption.
    pose proof (subst_env_id_ext (s_next T) E sgA IDA) as HXA.

    pose proof (forallb_true_In _ _ tA Vtpls HTA) as CA'. unfold tpl_checks in CA'.
    apply andb_true_split in CA' as [CA' _]. apply andb_true_split in CA' as [CA' _]. apply andb_true_split in CA' as [CA' _].
    apply andb_true_split in CA' as [CA' _]. apply andb_true_split in CA' as [_ Aba].
    exact (proj1 (bytes_again_sound (s_next T) E EA (lt_st A) ms1 mo1 wes w HSA Aba Hin B4 HXA B3 B2)). }
  specialize (MAIN HENT).
  assert (HTPL : forall X, (exists t, In t (tA :: tpls') /\ X = tc_tpl t) ->
    lt_n0 X = s_next T /\ lt_shape_ok segs it L X fd (oe1 wes) = true /\ bytes_again segs (lt_st X) wes = true /\
    (lt_c X = 1%nat \/ (lt_c X = 2%nat /\ c1 wes = 2%nat)) /\
    exists xs ys zs,
      explore segs it FUEL ra (post_done X) = Some (xs, []) /\
      explore segs it FUEL ra (post_loop X false) = Some ([], ys) /\
      (lt_c X = 2%nat -> explore segs it FUEL ra (post_loop X true) = Some ([], zs)) /\
      (forall x, In x xs -> exit_ok (s_next T) P x = true) /\
      (forall y, In y ys -> exists tgt, (exists t, In t (tA :: tpls') /\ tgt = tc_tpl t) /\ lt_c tgt = lt_c X /\ lt_arrives segs L X false (oe1 wes) tgt y = true) /\
      (forall y, In y zs -> exists tgt, (exists t, In t (tA :: tpls') /\ tgt = tc_tpl t) /\ lt_c tgt = 1%nat /\ lt_arrives segs L X true (oe1 wes) tgt y = true)).
  { intros X (t & Ht & ->). pose proof (forallb_true_In _ _ t Vtpls Ht) as Ct. unfold tpl_checks in Ct.
    apply andb_true_split in Ct as [Ct Csw]. apply andb_true_split in Ct as [Ct Cns]. apply andb_true_split in Ct as [Ct Cex].
    apply andb_true_split in Ct as [Ct Cc]. apply andb_true_split in Ct as [Ct Cba]. apply andb_true_split in Ct as [Cn0 Csh].
    apply Uint63.eqb_correct in Cn0.
    pose proof (proj1 (Forall_forall _ _) HX t Ht) as (XD & XN & XS).
    split; [exact Cn0|]. split; [exact Csh|]. split; [exact Cba|]. split.
    { apply orb_prop in Cc. destruct Cc as [C1|C2]; [left; apply Nat.eqb_eq; exact C1|].
      apply andb_true_split in C2 as [C2 C3]. apply Nat.eqb_eq in C2. apply Nat.eqb_eq in C3. right. unfold c1. auto. }
    exists (tc_exits t), (tc_ns t), (tc_sw t). split; [exact XD|]. split; [exact XN|]. split; [exact XS|]. split.
    { intros x Hx. exact (forallb_true_In _ _ x Cex Hx). }
    split.
    { intros y Hy. pose proof (forallb_true_In _ _ y Cns Hy) as Q. apply existsb_exists in Q as (t' & Ht' & Q).
      apply andb_true_split in Q as [Q1 Q2]. apply Nat.eqb_eq in Q1. exists (tc_tpl t'). split; [exists t'; auto|]. split; [exact Q1 | exact Q2]. }
    { intros y Hy. pose proof (forallb_true_In _ _ y Csw Hy) as Q. apply andb_true_split in Q as [_ Q]. apply existsb_exists in Q as (t' & Ht' & Q).
      apply andb_true_split in Q as [Q1 Q2]. apply Nat.eqb_eq in Q1. exists (tc_tpl t'). split; [exists t'; auto|]. split; [exact Q1 | exact Q2]. } }
  specialize (MAIN HTPL).

  assert (HTI : TI E (s_next T) wes A EA (bv_unsigned (den E (total_sv wes)))).
  { unfold TI, EA. pose proof (subst_env_id_ext (s_next T) E sgA IDA) as HXA.
    rewrite (sg_binds_sound E sgA _ _ Bvb), (sg_binds_sound E sgA _ _ Bvl), (sg_binds_sound E sgA _ _ Bvr).
    rewrite (known_eq_sound E _ _ _ Hfs1 Veq).
    assert (Hcw : curw wes A = w0 wes) by (unfold curw, c1; fold A in VcA; rewrite VcA, Nat.eqb_refl; reflexivity).
    rewrite Hcw. unfold bbase, blen, uZ, tailn. unfold blen, w0.
    split; [exact HXA|]. split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
    fold A in VcA. rewrite VcA. unfold c1, total_sv, w1.
    destruct wes as [|wa [|wb [|? ?]]]; cbn [length Nat.eqb nth] in *; try lia.
    destruct (Hent0 wa (or_introl eq_refl)) as (_ & Ba & _). destruct (Hent0 wb (or_intror (or_introl eq_refl))) as (_ & Bb & _).
    rewrite den_add, add_small by (unfold two64; lia). reflexivity. }
  pose proof (MAIN (S (Z.to_nat (bv_unsigned (den E (total_sv wes))))) A EA ms1 mo1 (bv_unsigned (den E (total_sv wes)))
                ltac:(exists tA; split; [left; reflexivity | reflexivity]) ltac:(lia)
                (conj HMo1 (fdok_sound E T1 ms1 mo1 HS1 Vfdok fd Hfd12)) HSA HTI) as R.

  unfold sw_bytes, sw_fd. cbn [c_wes c_fd].
  replace (concat (map (ent_bytes E) wes)) with (REM E wes A EA); [exact R|].
  unfold REM, tailB, BS, EA. rewrite (sg_binds_sound E sgA _ _ Bvl).
  assert (Hcw : curw wes A = w0 wes) by (unfold curw, c1; fold A in VcA; rewrite VcA, Nat.eqb_refl; reflexivity).
  rewrite Hcw. unfold blen, uZ. rewrite Z.sub_diag. cbn [Z.to_nat skipn].
  fold A in VcA. rewrite VcA. unfold c1, w0, w1. destruct wes as [|wa [|wb [|? ?]]]; cbn [length Nat.eqb nth map concat] in *; try lia; rewrite ?app_nil_r; reflexivity.
Qed.

Definition xr_eqb (o : option (list sstate * list sstate)) (ex ns : list sstate) : bool :=
  match o with Some (a, b) => StEqb.sts_eqb a ex && StEqb.sts_eqb b ns | None => false end.
Lemma xr_eqb_eq : forall o ex ns, xr_eqb o ex ns = true -> o = Some (ex, ns).
Proof.
  intros [[a b]|] ex ns H; cbn [xr_eqb] in H; [|discriminate H]. apply andb_prop in H as [H1 H2].
  apply StEqb.sts_eqb_eq in H1. apply StEqb.sts_eqb_eq in H2. subst. reflexivity.
Qed.

Definition explore_chk_comb (c : nat) (rd rn rs : option (list sstate * list sstate)) (ex ns sw : list sstate) : bool :=
  xr_eqb rd ex [] && xr_eqb rn [] ns && (negb (Nat.eqb c 2) || xr_eqb rs [] sw).
Lemma explore_chk_comb_sound : forall c rd rn rs ex ns sw, explore_chk_comb c rd rn rs ex ns sw = true ->
  rd = Some (ex, []) /\ rn = Some ([], ns) /\ (c = 2%nat -> rs = Some ([], sw)).
Proof.
  intros c rd rn rs ex ns sw H. unfold explore_chk_comb in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply xr_eqb_eq in H1. apply xr_eqb_eq in H2. split; [exact H1|]. split; [exact H2|].
  intros Hc. subst c. cbn [Nat.eqb negb orb] in H3. apply xr_eqb_eq in H3. exact H3.
Qed.

Lemma explore_chk_sound : forall ra ts,
  forallb (fun t => explore_chk_comb (lt_c (tc_tpl t)) (explore segs it FUEL ra (post_done (tc_tpl t)))
                      (explore segs it FUEL ra (post_loop (tc_tpl t) false)) (explore segs it FUEL ra (post_loop (tc_tpl t) true))
                      (tc_exits t) (tc_ns t) (tc_sw t)) ts = true ->
  Forall (explore_eqs ra) ts.
Proof.
  intros ra ts H. rewrite forallb_forall in H. apply Forall_forall. intros t Ht.
  exact (explore_chk_comb_sound _ _ _ _ _ _ _ (H t Ht)).
Qed.

Definition sres_eqb (r : sres) (T1 : sstate) : bool :=
  match r with SStop KEcall st => StEqb.st_eqb st T1 | _ => false end.
Lemma sres_eqb_eq : forall r T1, sres_eqb r T1 = true -> r = SStop KEcall T1.
Proof.
  intros [st|why st] T1 H; cbn [sres_eqb] in H; [discriminate H|]. destruct why; try discriminate H.
  apply StEqb.st_eqb_eq in H. subst. reflexivity.
Qed.

Theorem stdio_write_sound_b : forall (MP : Model -> Prop), mstable MP -> forall T P C E ms model K,
  sw_verify segs it L fdok T P C = true ->
  sres_eqb (run segs it [] T) (c_T1 C) = true ->
  forallb (fun t => explore_chk_comb (lt_c (tc_tpl t)) (explore segs it FUEL (c_ra C) (post_done (tc_tpl t)))
                      (explore segs it FUEL (c_ra C) (post_loop (tc_tpl t) false)) (explore segs it FUEL (c_ra C) (post_loop (tc_tpl t) true))
                      (tc_exits t) (tc_ns t) (tc_sw t)) (c_tpls C) = true ->
  st_ok segs OPS E T ms model -> MP model -> K [] ->
  (forall E' ms' mo', eb E' = eb E -> MP mo' -> st_ok segs OPS E' P ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms model) (t_emit (map (WriteEv (sw_fd C)) (sw_bytes C E)) K).
Proof.
  intros MP HMP T P C E ms model K H1 H2 H3 HS HMo HK Hcont.
  apply sres_eqb_eq in H2. apply explore_chk_sound in H3.
  exact (stdio_write_sound MP HMP T P C E ms model K H1 H2 H3 HS HMo HK Hcont).
Qed.
End Sound.

End SW.
