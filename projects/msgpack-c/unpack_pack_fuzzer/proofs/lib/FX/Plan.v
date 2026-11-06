(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step.
Open Scope Z_scope.

Module Plan.

Definition subst := IMap.t sv.

Definition svar (sg : subst) (v : int) : option int :=
  match IMap.find v sg with
  | Some (VP k o) => if weqb o wzero then Some k else None
  | _ => None
  end.

Definition width_okb (lo n : int) : bool :=
  PrimInt63.leb 1%uint63 n && PrimInt63.leb n 8%uint63 && PrimInt63.leb lo 8%uint63
  && PrimInt63.leb (PrimInt63.add lo n) 8%uint63.
Definition sv_ext_c (sx : bool) (lo n : int) (a : sv) : sv :=
  if width_okb lo n then sv_ext sx lo n a else VExt sx lo n a.
Definition sv_ins_c (lo n : int) (a v : sv) : sv :=
  if width_okb lo n then sv_ins lo n a v else VIns lo n a v.

Fixpoint sapply (sg : subst) (v : sv) : option sv :=
  match v with
  | VL w => Some (VL w)
  | VP k o => match IMap.find k sg with
              | Some u => Some (sv_alu ALU_ADD u (VL o))
              | None => None
              end
  | VAlu op a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (sv_alu op a' b') | _, _ => None end
  | VAluw op a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (sv_aluw op a' b') | _, _ => None end
  | VMd op a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (sv_md op a' b') | _, _ => None end
  | VMdw op a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (sv_mdw op a' b') | _, _ => None end
  | VExt sx lo n a => match sapply sg a with Some a' => Some (sv_ext_c sx lo n a') | None => None end
  | VIns lo n a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (sv_ins_c lo n a' b') | _, _ => None end
  | VBlob sx j off n => match sapply sg off with Some o' => Some (VBlob sx j o' n) | None => None end
  | VBg sx k off n => match svar sg k with Some k' => Some (VBg sx k' off n) | None => None end
  | VF1 op a => match sapply sg a with Some a' => Some (VF1 op a') | None => None end
  end.

Fixpoint vsubst (k : int) (u : sv) (v : sv) : sv :=
  match v with
  | VL w => v
  | VP k' o => if PrimInt63.eqb k k' then sv_alu ALU_ADD u (VL o) else v
  | VAlu op a b => sv_alu op (vsubst k u a) (vsubst k u b)
  | VAluw op a b => sv_aluw op (vsubst k u a) (vsubst k u b)
  | VMd op a b => sv_md op (vsubst k u a) (vsubst k u b)
  | VMdw op a b => sv_mdw op (vsubst k u a) (vsubst k u b)
  | VExt sx lo n a => sv_ext_c sx lo n (vsubst k u a)
  | VIns lo n a b => sv_ins_c lo n (vsubst k u a) (vsubst k u b)
  | VBlob sx j off n => VBlob sx j (vsubst k u off) n
  | VBg _ _ _ _ => v
  | VF1 op a => VF1 op (vsubst k u a)
  end.

Definition cell_map (f : sv -> sv) (c : cell) : cell := Cell (c_idx c) (c_w c) (f (c_v c)).
Definition gran_map (f : sv -> sv) (gr : gran) : gran := Gran (g_dirty gr) (List.map (cell_map f) (g_cells gr)).
Definition region_map (f : sv -> sv) (r : region) : region :=
  Region (rg_lo r) (f (rg_hi r)) (rg_w r) (rg_bg r) (IMap.map (gran_map f) (rg_cells r)).
Definition op_map (f : sv -> sv) (o : opinst) : opinst := OpI (op_id o) (List.map f (op_args o)).

Definition fact_map (f : sv -> sv) (x : fact) : fact :=
  match x with
  | FRange k lo hi => x | FAlign k m => x
  | FULt a b => FULt (f a) (f b) | FULe a b => FULe (f a) (f b)
  | FEq a b => FEq (f a) (f b)   | FNe a b => FNe (f a) (f b)
  | FSLt a b => FSLt (f a) (f b) | FSLe a b => FSLe (f a) (f b)
  end.

Definition smatch (sg : subst) (tv : sv) (v : sv) : bool :=
  match sapply sg tv with Some tv' => sv_eqb tv' v | None => false end.

Definition sapply_fact (sg : subst) (f : fact) : option fact :=
  match f with
  | FRange k lo hi => match svar sg k with Some k' => Some (FRange k' lo hi) | None => None end
  | FAlign k m => match svar sg k with Some k' => Some (FAlign k' m) | None => None end
  | FULt a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (FULt a' b') | _, _ => None end
  | FULe a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (FULe a' b') | _, _ => None end
  | FEq a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (FEq a' b') | _, _ => None end
  | FNe a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (FNe a' b') | _, _ => None end
  | FSLt a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (FSLt a' b') | _, _ => None end
  | FSLe a b => match sapply sg a, sapply sg b with Some a', Some b' => Some (FSLe a' b') | _, _ => None end
  end.

Fixpoint fact_eqb (f g : fact) : bool :=
  match f, g with
  | FRange k lo hi, FRange k' lo' hi' => PrimInt63.eqb k k' && weqb lo lo' && weqb hi hi'
  | FAlign k m, FAlign k' m' => PrimInt63.eqb k k' && PrimInt63.eqb m m'
  | FULt a b, FULt a' b' => sv_eqb a a' && sv_eqb b b'
  | FULe a b, FULe a' b' => sv_eqb a a' && sv_eqb b b'
  | FEq a b, FEq a' b' => sv_eqb a a' && sv_eqb b b'
  | FNe a b, FNe a' b' => sv_eqb a a' && sv_eqb b b'
  | FSLt a b, FSLt a' b' => sv_eqb a a' && sv_eqb b b'
  | FSLe a b, FSLe a' b' => sv_eqb a a' && sv_eqb b b'
  | _, _ => false
  end.

Definition implied (fs : list fact) (f : fact) : bool :=
  if existsb (fact_eqb f) fs then true else
  match f with
  | FRange k lo hi => match find_range fs k with
                      | Some (lo', hi') => wleu lo lo' && wleu hi' hi
                      | None => false
                      end
  | FAlign k m => PrimInt63.leb m (find_align fs k)
  | FULt a b => match decide_ltu fs a b with Some true => true | _ => false end
  | FULe a b => match decide_ltu fs b a with Some false => true | _ => false end
  | FEq a b => match decide_eq fs a b with Some true => true | _ => false end
  | FNe a b => match decide_eq fs a b with Some false => true | _ => false end
  | FSLt a b => match decide_lts fs a b with Some true => true | _ => false end
  | FSLe a b => match decide_lts fs b a with Some false => true | _ => false end
  end.

Definition rel_facts1 (vs : list int) (fs : list fact) : list fact := rel_facts (close_vs fs vs vs) fs.
Fixpoint has_fact (f : fact) (fs : list fact) : bool :=
  match fs with [] => false | g :: fs' => if fact_eqb f g then true else has_fact f fs' end.
Definition decide_eq_t (fs : list fact) (a b : sv) : option bool :=
  let vs := sv_vs a (sv_vs b []) in
  match decide_eq (rel_facts vs fs) a b with
  | Some true => Some true
  | _ => match decide_eq (rel_facts (close_vs fs vs vs) fs) a b with
         | Some true => Some true
         | _ => decide_eq fs a b
         end
  end.
Definition decide_ltu_t (fs : list fact) (a b : sv) : option bool :=
  let vs := sv_vs a (sv_vs b []) in
  match decide_ltu (rel_facts vs fs) a b with
  | Some true => Some true
  | _ => match decide_ltu (rel_facts (close_vs fs vs vs) fs) a b with
         | Some true => Some true
         | _ => decide_ltu fs a b
         end
  end.
Definition implied_t (fs : list fact) (f : fact) : bool :=
  if has_fact f fs then true
  else if implied (rel_facts (fact_vs f) fs) f then true
  else if implied (rel_facts1 (fact_vs f) fs) f then true
  else implied fs f.

Definition fact_entailed (fs : list fact) (sg : subst) (f : fact) : bool :=
  match sapply_fact sg f with
  | Some f' => implied_t fs f'
  | None =>
      match f with
      | FRange k lo hi => match IMap.find k sg with
                          | Some u => implied_t fs (FULe (VL lo) u) && implied_t fs (FULe u (VL hi))
                          | None => false
                          end
      | FAlign k m => match IMap.find k sg with
                      | Some u => PrimInt63.leb m 62%uint63 && aligned fs u m
                      | None => false
                      end
      | _ => false
      end
  end.

Definition cell_match (sg : subst) (tc : cell) (c : cell) : bool :=
  PrimInt63.eqb (c_idx tc) (c_idx c) && PrimInt63.eqb (c_w tc) (c_w c) && smatch sg (c_v tc) (c_v c).

Fixpoint slot_match_exact (sg : subst) (ts s : slot) : bool :=
  match ts, s with
  | [], [] => true
  | tc :: ts', c :: s' => cell_match sg tc c && slot_match_exact sg ts' s'
  | _, _ => false
  end.

Fixpoint slot_match_sub (sg : subst) (ts s : slot) : bool :=
  match ts with
  | [] => true
  | tc :: ts' => existsb (cell_match sg tc) s && slot_match_sub sg ts' s
  end.

Definition bg_match (sg : subst) (tb b : bg) : bool :=
  match tb, b with
  | BGNone, _ => true
  | BGZero, BGZero | BGImage, BGImage | BGUnk, BGUnk => true
  | BGBlob j sh, BGBlob j' sh' => PrimInt63.eqb j j' && PrimInt63.eqb sh sh'
  | _, _ => false
  end.

Definition cell_keys_in (lo : int) (hi : option int) (cells : IMap.t gran) : bool :=
  IMap.forallb (fun g gr =>
     forallb (fun c =>

        let k0 := PrimInt63.add (PrimInt63.lsl g 3%uint63) (c_idx c) in
        let k1 := PrimInt63.add k0 (c_w c) in
        PrimInt63.eqb (granule k0) g && PrimInt63.eqb (gidx k0) (c_idx c) &&
        kleb lo k0 && kltb k0 k1 &&
        match hi with Some h => kleb k1 h | None => true end) (g_cells gr)) cells.

Definition region_match (sg : subst) (tk : int) (tr : region) (k : int) (r : region) : bool :=
  bg_match sg (rg_bg tr) (rg_bg r)
  && Bool.eqb (rg_w tr) (rg_w r)
  && kleb (rg_lo r) (rg_lo tr)
  && (if smatch sg (rg_hi tr) (rg_hi r) then cell_keys_in (rg_lo tr) None (rg_cells tr)
      else match rg_hi tr, rg_hi r with
           | VL th, VL h => match okey th, okey h with
                            | Some a, Some b => wleu th h && cell_keys_in (rg_lo tr) (Some a) (rg_cells tr)
                            | _, _ => false
                            end
           | _, _ => false
           end)
  &&
     IMap.forallb (fun g tgr =>
        match IMap.find g (rg_cells r) with
        | Some gr => if g_dirty tgr then slot_match_sub sg (g_cells tgr) (g_cells gr)
                     else negb (g_dirty gr) && slot_match_exact sg (g_cells tgr) (g_cells gr)
        | None => match g_cells tgr with [] => true | _ => false end
        end) (rg_cells tr)
  && IMap.forallb (fun g gr => match IMap.find g (rg_cells tr) with
                               | Some _ => true
                               | None => negb (g_dirty gr) && match g_cells gr with [] => true | _ => false end
                               end) (rg_cells r).

Definition anchor_images (sg : subst) (TR : IMap.t region) : list int :=
  IMap.fold (fun tk _ acc => match svar sg tk with Some k => k :: acc | None => acc end) TR [].

Fixpoint int_notin (x : int) (l : list int) : bool :=
  match l with [] => true | y :: l' => negb (PrimInt63.eqb x y) && int_notin x l' end.
Fixpoint int_nodup (l : list int) : bool :=
  match l with [] => true | x :: l' => int_notin x l' && int_nodup l' end.

Definition regions_match (sg : subst) (TR R : IMap.t region) : bool :=

  IMap.forallb (fun tk tr => match svar sg tk with
                             | Some k => match IMap.find k R with
                                         | Some r => Bool.eqb (PrimInt63.eqb tk 0%uint63) (PrimInt63.eqb k 0%uint63)
                                                     && region_match sg tk tr k r
                                         | None => false
                                         end
                             | None => false
                             end) TR
  && int_nodup (anchor_images sg TR).

Fixpoint remove_first {A} (p : A -> bool) (l : list A) : option (list A) :=
  match l with
  | [] => None
  | x :: l' => if p x then Some l' else match remove_first p l' with Some l'' => Some (x :: l'') | None => None end
  end.

Definition op_match (sg : subst) (t o : opinst) : bool :=
  PrimInt63.eqb (op_id t) (op_id o) &&
  (fix go (ta a : list sv) : bool :=
     match ta, a with
     | [], [] => true
     | x :: ta', y :: a' => smatch sg x y && go ta' a'
     | _, _ => false
     end) (op_args t) (op_args o).

Fixpoint ops_match (sg : subst) (ts os : list opinst) : bool :=
  match ts with
  | [] => match os with [] => true | _ => false end
  | t :: ts' => match remove_first (op_match sg t) os with
                | Some os' => ops_match sg ts' os'
                | None => false
                end
  end.

Fixpoint privs_eqb (a b : list (int * int)) : bool :=
  match a, b with
  | [], [] => true
  | (x1, y1) :: a', (x2, y2) :: b' => PrimInt63.eqb x1 x2 && PrimInt63.eqb y1 y2 && privs_eqb a' b'
  | _, _ => false
  end.

Definition resv_match (sg : subst) (t r : sresv) : bool :=
  match t, r with
  | RUnk, _ => true
  | RNone, RNone => true
  | RAddr a, RAddr b => smatch sg a b
  | _, _ => false
  end.

Definition entails (st : sstate) (T : sstate) (sg : subst) : bool :=
  PrimInt63.eqb (s_pc st) (s_pc T)
  && sv_eqb (rf_get (s_rf T) X0) (VL wzero)
  && rf_forallb2 (smatch sg) (s_rf T) (s_rf st)
  && rf_forallb2 (smatch sg) (s_ff T) (s_ff st)
  && resv_match sg (s_resv T) (s_resv st)
  && regions_match sg (s_regs T) (s_regs st)
  && forallb (fact_entailed (s_facts st) sg) (s_facts T)
  && ops_match sg (s_ops T) (s_ops st)
  && privs_eqb (s_priv T) (s_priv st)
  && match svar sg 0%uint63 with Some k => PrimInt63.eqb k 0%uint63 | None => false end.

Fixpoint keys_increasing (prev : option int) (l : list int) : bool :=
  match l with
  | [] => true
  | k :: l' => match prev with Some p => PrimInt63.ltb p k | None => true end && keys_increasing (Some k) l'
  end.
Definition bst_b {A} (m : IMap.t A) : bool := keys_increasing None (List.map fst (IMap.elements m)).

Fixpoint slot_wfb (prev_end : int) (s : slot) : bool :=
  match s with
  | [] => true
  | c :: s' => PrimInt63.leb prev_end (c_idx c) && PrimInt63.ltb 0%uint63 (c_w c)
               && PrimInt63.leb (PrimInt63.add (c_idx c) (c_w c)) 8%uint63
               && PrimInt63.ltb (c_idx c) 8%uint63 && PrimInt63.leb (c_w c) 8%uint63
               && slot_wfb (PrimInt63.add (c_idx c) (c_w c)) s'
  end.

Definition region_wfb (r : region) : bool :=
  bst_b (rg_cells r) && IMap.forallb (fun _ gr => slot_wfb 0%uint63 (g_cells gr)) (rg_cells r).

Definition sstate_wfb (T : sstate) : bool :=
  bst_b (s_regs T) && IMap.forallb (fun _ r => region_wfb r) (s_regs T)
  && sv_eqb (rf_get (s_rf T) X0) (VL wzero).

Record contract := Contract {
  c_pc : int;
  c_apply : sstate -> option (list sstate)
}.

Fixpoint sv_vars_below (n : int) (v : sv) : bool :=
  match v with
  | VL _ => true
  | VP k _ => PrimInt63.ltb k n
  | VAlu _ a b | VAluw _ a b | VMd _ a b | VMdw _ a b | VIns _ _ a b => sv_vars_below n a && sv_vars_below n b
  | VExt _ _ _ a => sv_vars_below n a
  | VBlob _ _ off _ => sv_vars_below n off
  | VBg _ k _ _ => PrimInt63.ltb k n
  | VF1 _ a => sv_vars_below n a
  end.
Fixpoint slot_vars_below (n : int) (s : slot) : bool :=
  match s with [] => true | c :: s' => sv_vars_below n (c_v c) && slot_vars_below n s' end.
Definition region_vars_below (n : int) (r : region) : bool :=
  sv_vars_below n (rg_hi r) && IMap.forallb (fun _ gr => slot_vars_below n (g_cells gr)) (rg_cells r).
Definition fact_vars_below (n : int) (f : fact) : bool :=
  match f with
  | FRange k _ _ | FAlign k _ => PrimInt63.ltb k n
  | FULt a b | FULe a b | FEq a b | FNe a b | FSLt a b | FSLe a b => sv_vars_below n a && sv_vars_below n b
  end.
Definition resv_vars_below (n : int) (rv : sresv) : bool :=
  match rv with RAddr a => sv_vars_below n a | _ => true end.
Definition rf_allb {A} (p : A -> bool) (x : rf A) : bool := forallb p (rf_to_list x).

Definition st_vars_below (n : int) (st : sstate) : bool :=
  rf_allb (sv_vars_below n) (s_rf st) && rf_allb (sv_vars_below n) (s_ff st) && resv_vars_below n (s_resv st)
  && IMap.forallb (fun k r => PrimInt63.ltb k n && region_vars_below n r) (s_regs st)
  && forallb (fact_vars_below n) (s_facts st)
  && forallb (fun o => forallb (sv_vars_below n) (op_args o)) (s_ops st).

Definition sapply_ok (sg : subst) (v : sv) : bool :=
  match sapply sg v with Some _ => true | None => false end.

Definition sapply_d (sg : subst) (v : sv) : sv :=
  match sapply sg v with Some v' => v' | None => VL wzero end.

Fixpoint omap_list {A B : Type} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => Some []
  | x :: l' => match f x, omap_list f l' with Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.

Definition region_inst_ok (sg : subst) (r : region) : bool :=
  sapply_ok sg (rg_hi r)
  && IMap.forallb (fun _ gr => List.forallb (fun c => sapply_ok sg (c_v c)) (g_cells gr)) (rg_cells r).

Definition regs_inst (sg : subst) (TR : IMap.t region) : option (IMap.t region) :=
  if int_nodup (anchor_images sg TR) then
    IMap.fold (fun tk tr acc =>
      match acc with
      | None => None
      | Some R =>
          match svar sg tk with
          | Some k =>
              if Bool.eqb (PrimInt63.eqb tk 0%uint63) (PrimInt63.eqb k 0%uint63) && region_inst_ok sg tr
              then Some (IMap.add k (region_map (sapply_d sg) tr) R)
              else None
          | None => None
          end
      end) TR (Some IMap.empty)
  else None.

Definition fact_inst (sg : subst) (f : fact) : list fact :=
  match f with
  | FRange k lo hi =>
      match svar sg k with
      | Some k' => [FRange k' lo hi]
      | None => match IMap.find k sg with
                | Some u => [FULe (VL lo) u; FULe u (VL hi)]
                | None => []
                end
      end
  | FAlign k m => match svar sg k with Some k' => [FAlign k' m] | None => [] end
  | _ => match sapply_fact sg f with Some f' => [f'] | None => [] end
  end.

Definition resv_inst (sg : subst) (rv : sresv) : option sresv :=
  match rv with
  | RAddr a => match sapply sg a with Some a' => Some (RAddr a') | None => None end
  | RNone => Some RNone
  | RUnk => Some RUnk
  end.

Definition op_inst (sg : subst) (o : opinst) : option opinst :=
  match omap_list (sapply sg) (op_args o) with Some args => Some (OpI (op_id o) args) | None => None end.

Definition st_inst (sg : subst) (next : int) (T : sstate) : option sstate :=
  if rf_allb (sapply_ok sg) (s_rf T) && rf_allb (sapply_ok sg) (s_ff T)
     && sv_eqb (rf_get (s_rf T) X0) (VL wzero)
     && match svar sg 0%uint63 with Some k => PrimInt63.eqb k 0%uint63 | None => false end
  then
    match resv_inst sg (s_resv T), regs_inst sg (s_regs T), omap_list (op_inst sg) (s_ops T) with
    | Some rv, Some R, Some os =>
        Some (SS (s_pc T) (rf_map (sapply_d sg) (s_rf T)) (rf_map (sapply_d sg) (s_ff T)) rv R
                 (List.flat_map (fact_inst sg) (s_facts T)) os (s_priv T) next)
    | _, _, _ => None
    end
  else None.

Inductive plan : Type :=
| PRun (stops : list int) (k : plan)
| PCase (kT kF : plan)
| PSplit (r : r5) (n : int) (ks : list plan)
| PSetReg (r : r5) (v : sv) (k : plan)
| PSubst (x : int) (u : sv) (k : plan)
| PName (r : r5) (k : plan)
| PSetHi (rk : int) (v : sv) (k : plan)
| PAssume (f : fact) (k : plan)
| PCall (cid : int) (ks : list plan)
| PCut (tid : int) (sg : list (int * sv))
| PCutDec (tid : int) (sg : list (int * sv))
| PEcall (eid : int) (sg : list (int * sv))
| PForget (k : int) (glo ghi : int) (kk : plan)
| PDropFacts (keep : nat) (k : plan)
| PFail (msg : int).

Record template := Tpl {
  t_st : sstate;
  t_measure : sv
}.

Record ctx := Ctx {
  c_itab : itab;
  c_cuts : IMap.t template;
  c_ecalls : IMap.t sstate;
  c_contracts : IMap.t contract;
  c_mroot : sv
}.

Definition mk_subst (l : list (int * sv)) : subst :=
  fold_left (fun m kv => IMap.add (fst kv) (snd kv) m) l IMap.empty.

Definition obligation : Type := (list fact * fact)%type.

Definition ctx_wfb (C : ctx) : bool :=
  IMap.forallb (fun _ t => sstate_wfb (t_st t)) (c_cuts C)
  && IMap.forallb (fun _ T => sstate_wfb T) (c_ecalls C).

Fixpoint iota_int (i : int) (n : nat) : list int :=
  match n with O => [] | S n' => i :: iota_int (PrimInt63.add i 1%uint63) n' end.

Definition DEAD : int := 57005%uint63.
Definition fact_refuted (fs : list fact) (f : fact) : bool :=
  match f with
  | FEq a b => match decide_eq fs a b with Some false => true | _ => false end
  | FNe a b => match decide_eq fs a b with Some true => true | _ => false end
  | FULt a b => match decide_ltu fs a b with Some false => true | _ => false end
  | FULe a b => match decide_ltu fs b a with Some true => true | _ => false end
  | FRange k lo hi => wltu hi lo
  | _ => false
  end.
Fixpoint dead_go (pre : list fact) (l : list fact) : bool :=
  match l with
  | [] => false
  | f :: l' => if fact_refuted (rev_append pre l') f then true else dead_go (f :: pre) l'
  end.
Definition facts_dead (fs : list fact) : bool := dead_go [] fs.

Section WithSegs.
Variable segs : list Segment.

Fixpoint check (C : ctx) (p : plan) (st : sstate) {struct p} : option (list obligation) :=
  match p with
  | PFail msg => if PrimInt63.eqb msg DEAD && facts_dead (s_facts st) then Some [] else None
  | PRun stops k =>
      match run segs (c_itab C) stops st with
      | SStop KStopPc st' => check C k st'
      | SStop KEcall st' => check C k st'
      | SStop (KBranch _ _ _ _) st' => check C k st'
      | _ => None
      end
  | PCase kT kF =>
      if PrimInt63.ltb (s_pc st) bit62i then
      match IMap.find (s_pc st) (c_itab C) with
      | Some (IBranch c rs1 rs2 off) =>
          let a := getr st rs1 in let b := getr st rs2 in
          match take_branch c a b off true st, take_branch c a b off false st with
          | Some stT, Some stF =>
              match check C kT stT, check C kF stF with
              | Some o1, Some o2 => Some (o1 ++ o2)
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
      else None
  | PSplit r n ks =>
      let v := getr st r in
      match decide_ltu_t (s_facts st) v (VL (wlit n)) with
      | Some true =>
          if Nat.eqb (length ks) (Z.to_nat (to_Z n)) then
            (fix go (ks : list plan) (i : int) : option (list obligation) :=
               match ks with
               | [] => Some []
               | k :: ks' =>
                   match check C k (addfact (setr st r (VL (wlit i))) (FEq v (VL (wlit i)))), go ks' (PrimInt63.add i 1%uint63) with
                   | Some o1, Some o2 => Some (o1 ++ o2)
                   | _, _ => None
                   end
               end) ks 0%uint63
          else None
      | _ => None
      end
  | PSetReg r v k =>
      match r, decide_eq_t (s_facts st) (getr st r) v with
      | X0, _ => None
      | _, Some true => check C k (setr st r v)
      | _, _ => None
      end
  | PSubst x u k =>
      if negb (PrimInt63.eqb x 0%uint63)
         && match IMap.find x (s_regs st) with Some _ => false | None => true end
         && match decide_eq_t (s_facts st) (VP x wzero) u with Some true => true | _ => false end
      then
        let f := vsubst x u in
        check C k (SS (s_pc st) (rf_map f (s_rf st)) (rf_map f (s_ff st))
                     (match s_resv st with RAddr a => RAddr (f a) | rv => rv end)
                     (IMap.map (region_map f) (s_regs st)) (List.map (fact_map f) (s_facts st))
                     (List.map (op_map f) (s_ops st)) (s_priv st) (s_next st))
      else None
  | PName r k =>
      let n := s_next st in
      match r with
      | X0 => None
      | _ =>
          if st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n bit62i then
            check C k (SS (s_pc st) (rf_set (s_rf st) r (VP n wzero)) (s_ff st) (s_resv st) (s_regs st)
                        (FEq (VP n wzero) (getr st r) :: s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63))
          else None
      end
  | PSetHi rk v k =>
      if PrimInt63.eqb rk 0%uint63 then None else
      match IMap.find rk (s_regs st) with
      | Some r =>
          match decide_eq_t (s_facts st) (rg_hi r) v with
          | Some true => check C k (setregs st (IMap.add rk (Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)))
          | _ => None
          end
      | None => None
      end
  | PAssume f k =>
      if implied_t (s_facts st) f then check C k (addfact st f)
      else
      match check C k (addfact st f) with
      | Some o => Some ((s_facts st, f) :: o)
      | None => None
      end
  | PCall cid ks =>
      match IMap.find cid (c_contracts C) with
      | Some ct =>
          if PrimInt63.eqb (s_pc st) (c_pc ct) then
            match c_apply ct st with
            | Some sts =>
                (fix go (ks : list plan) (sts : list sstate) : option (list obligation) :=
                   match ks, sts with
                   | [], [] => Some []
                   | k :: ks', st' :: sts' =>
                       if PrimInt63.leb (s_next st) (s_next st') then
                         match check C k st', go ks' sts' with
                         | Some o1, Some o2 => Some (o1 ++ o2)
                         | _, _ => None
                         end
                       else None
                   | _, _ => None
                   end) ks sts
            | None => None
            end
          else None
      | None => None
      end
  | PCut tid sg =>
      match IMap.find tid (c_cuts C) with
      | Some T => if entails st (t_st T) (mk_subst sg) then Some [] else None
      | None => None
      end
  | PCutDec tid sg =>
      match IMap.find tid (c_cuts C) with
      | Some T =>
          let s := mk_subst sg in
          if entails st (t_st T) s then
            match sapply s (t_measure T) with
            | Some m => match decide_ltu_t (s_facts st) m (c_mroot C) with
                        | Some true => Some []
                        | _ => None
                        end
            | None => None
            end
          else None
      | None => None
      end
  | PEcall eid sg =>
      match IMap.find (s_pc st) (c_itab C), IMap.find eid (c_ecalls C) with
      | Some IEcall, Some T => if entails st T (mk_subst sg) then Some [] else None
      | _, _ => None
      end
  | PForget k glo ghi kk =>
      match IMap.find k (s_regs st) with
      | Some r => check C kk (setregs st (IMap.add k (Mem.region_forget r glo ghi) (s_regs st)))
      | None => None
      end
  | PDropFacts keep k =>
      check C k (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (firstn keep (s_facts st))
                    (s_ops st) (s_priv st) (s_next st))
  end.

Section Rot.
Variable rot : Mem.rotab.
Fixpoint check_r (C : ctx) (p : plan) (st : sstate) {struct p} : option (list obligation) :=
  match p with
  | PFail msg => if PrimInt63.eqb msg DEAD && facts_dead (s_facts st) then Some [] else None
  | PRun stops k =>
      match run_r segs rot (c_itab C) stops st with
      | SStop KStopPc st' => check_r C k st'
      | SStop KEcall st' => check_r C k st'
      | SStop (KBranch _ _ _ _) st' => check_r C k st'
      | _ => None
      end
  | PCase kT kF =>
      if PrimInt63.ltb (s_pc st) bit62i then
      match IMap.find (s_pc st) (c_itab C) with
      | Some (IBranch c rs1 rs2 off) =>
          let a := getr st rs1 in let b := getr st rs2 in
          match take_branch c a b off true st, take_branch c a b off false st with
          | Some stT, Some stF =>
              match check_r C kT stT, check_r C kF stF with
              | Some o1, Some o2 => Some (o1 ++ o2)
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
      else None
  | PSplit r n ks =>
      let v := getr st r in
      match decide_ltu_t (s_facts st) v (VL (wlit n)) with
      | Some true =>
          if Nat.eqb (length ks) (Z.to_nat (to_Z n)) then
            (fix go (ks : list plan) (i : int) : option (list obligation) :=
               match ks with
               | [] => Some []
               | k :: ks' =>
                   match check_r C k (addfact (setr st r (VL (wlit i))) (FEq v (VL (wlit i)))), go ks' (PrimInt63.add i 1%uint63) with
                   | Some o1, Some o2 => Some (o1 ++ o2)
                   | _, _ => None
                   end
               end) ks 0%uint63
          else None
      | _ => None
      end
  | PSetReg r v k =>
      match r, decide_eq_t (s_facts st) (getr st r) v with
      | X0, _ => None
      | _, Some true => check_r C k (setr st r v)
      | _, _ => None
      end
  | PSubst x u k =>
      if negb (PrimInt63.eqb x 0%uint63)
         && match IMap.find x (s_regs st) with Some _ => false | None => true end
         && match decide_eq_t (s_facts st) (VP x wzero) u with Some true => true | _ => false end
      then
        let f := vsubst x u in
        check_r C k (SS (s_pc st) (rf_map f (s_rf st)) (rf_map f (s_ff st))
                     (match s_resv st with RAddr a => RAddr (f a) | rv => rv end)
                     (IMap.map (region_map f) (s_regs st)) (List.map (fact_map f) (s_facts st))
                     (List.map (op_map f) (s_ops st)) (s_priv st) (s_next st))
      else None
  | PName r k =>
      let n := s_next st in
      match r with
      | X0 => None
      | _ =>
          if st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n bit62i then
            check_r C k (SS (s_pc st) (rf_set (s_rf st) r (VP n wzero)) (s_ff st) (s_resv st) (s_regs st)
                        (FEq (VP n wzero) (getr st r) :: s_facts st) (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63))
          else None
      end
  | PSetHi rk v k =>
      if PrimInt63.eqb rk 0%uint63 then None else
      match IMap.find rk (s_regs st) with
      | Some r =>
          match decide_eq_t (s_facts st) (rg_hi r) v with
          | Some true => check_r C k (setregs st (IMap.add rk (Region (rg_lo r) v (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st)))
          | _ => None
          end
      | None => None
      end
  | PAssume f k =>
      if implied_t (s_facts st) f then check_r C k (addfact st f)
      else
      match check_r C k (addfact st f) with
      | Some o => Some ((s_facts st, f) :: o)
      | None => None
      end
  | PCall cid ks =>
      match IMap.find cid (c_contracts C) with
      | Some ct =>
          if PrimInt63.eqb (s_pc st) (c_pc ct) then
            match c_apply ct st with
            | Some sts =>
                (fix go (ks : list plan) (sts : list sstate) : option (list obligation) :=
                   match ks, sts with
                   | [], [] => Some []
                   | k :: ks', st' :: sts' =>
                       if PrimInt63.leb (s_next st) (s_next st') then
                         match check_r C k st', go ks' sts' with
                         | Some o1, Some o2 => Some (o1 ++ o2)
                         | _, _ => None
                         end
                       else None
                   | _, _ => None
                   end) ks sts
            | None => None
            end
          else None
      | None => None
      end
  | PCut tid sg =>
      match IMap.find tid (c_cuts C) with
      | Some T => if entails st (t_st T) (mk_subst sg) then Some [] else None
      | None => None
      end
  | PCutDec tid sg =>
      match IMap.find tid (c_cuts C) with
      | Some T =>
          let s := mk_subst sg in
          if entails st (t_st T) s then
            match sapply s (t_measure T) with
            | Some m => match decide_ltu_t (s_facts st) m (c_mroot C) with
                        | Some true => Some []
                        | _ => None
                        end
            | None => None
            end
          else None
      | None => None
      end
  | PEcall eid sg =>
      match IMap.find (s_pc st) (c_itab C), IMap.find eid (c_ecalls C) with
      | Some IEcall, Some T => if entails st T (mk_subst sg) then Some [] else None
      | _, _ => None
      end
  | PForget k glo ghi kk =>
      match IMap.find k (s_regs st) with
      | Some r => check_r C kk (setregs st (IMap.add k (Mem.region_forget r glo ghi) (s_regs st)))
      | None => None
      end
  | PDropFacts keep k =>
      check_r C k (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (firstn keep (s_facts st))
                    (s_ops st) (s_priv st) (s_next st))
  end.
End Rot.

End WithSegs.
End Plan.
