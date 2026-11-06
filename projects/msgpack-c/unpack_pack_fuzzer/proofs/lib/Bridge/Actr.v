(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr Mem State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require GTwinSub.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module ActrA.
Definition ATPi : int := 0x60cc80%uint63.
Definition SBw : w64 := wlit 0x7fff8000%uint63.
Definition K_TWIN : w64 := wlit 9%uint63.
Definition ASTACK : int := 8192%uint63.
Definition AREQMAXw : w64 := wlit 0xFFF00000%uint63.

Definition SYMCAPw : w64 := wlit 65536%uint63.
Definition BLK_LO : w64 := wlit 0x62f000%uint63.
Definition BLK_HI : w64 := wlit 140737488355327%uint63.

Definition twin_len (n : sv) : sv :=
  match n with
  | VL w => VL (wlit (PrimInt63.lsr (PrimInt63.add (wl w) 7%uint63) 3%uint63))
  | _ => sv_alu ALU_SRL (sv_alu ALU_ADD n (VL (wlit 7%uint63))) (VL (wlit 3%uint63))
  end.
Definition twin_region (n : sv) : region :=
  let r := Region 0%uint63 (twin_len n) false BGZero IMap.empty in
  match n with
  | VL w => let t := PrimInt63.land (wl w) 7%uint63 in
            if PrimInt63.eqb t 0%uint63 then r
            else region_store r (PrimInt63.lsr (wl w) 3%uint63) 1%uint63 (VL (wlit t))
  | _ => r
  end.

Notation "a &&& b" := (if a then b else false) (at level 40, left associativity, only parsing).
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing).
Definition known_leu_s (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu_s fs b a).

Definition sp_below_anchor_t (fs : list fact) (sp : sv) : bool := KnownT.KnownT.known_leu_t fs sp (VP STACK_ID wzero).
Definition stack_side_t (fs : list fact) (sp : sv) (spok : bool) (k : int) : bool :=
  if (if spok then (if CtrA.anchored_above fs k then true else KnownT.KnownT.known_leu_t fs (VP STACK_ID wzero) (VP k wzero)) else false) then true
  else KnownT.KnownT.known_leu_t fs sp (VP k wzero).
Definition known_leu_qt (fs : list fact) (a b : sv) : bool :=
  if sv_eqb a b then true else
  if fact_lookup fs (is_FULe a b) then true else
  if fact_lookup fs (is_FULt a b) then true else KnownT.KnownT.known_leu_t fs a b.

Definition sz_and7 (n : sv) : sv := sv_alu ALU_AND n (VL (wlit 7%uint63)).
Definition sz_last (n : sv) : sv := sv_alu ALU_SRL (sv_alu ALU_ADD n (VL wones)) (VL (wlit 3%uint63)).
Definition twin_main (n : sv) : region := Region 0%uint63 (sz_last n) false BGZero IMap.empty.
Definition tail_region (n : sv) : region :=
  region_store (Region 0%uint63 (VL wone) false BGZero IMap.empty) 0%uint63 1%uint63 (sz_and7 n).
Definition tail_rhs (sh : int) (n : sv) : sv := sv_alu ALU_ADD (VP sh wzero) (sz_last n).
Definition tail_fact (s2 sh : int) (n : sv) : fact := FEq (VP s2 wzero) (tail_rhs sh n).

Definition al8 (o : w64) : bool := negb (wt o) && PrimInt63.eqb (PrimInt63.land (wl o) 7%uint63) 0%uint63.

Definition div8 (fs : list fact) (xs : sv) : bool := has_fact (FEq (VAlu ALU_AND xs (VL (wlit 7%uint63))) (VL wzero)) fs.

Definition and7_facts (n : sv) : list fact :=
  match n with VL _ => [] | _ => [FEq (VAlu ALU_AND n (VL (wlit 7%uint63))) (VL wzero)] end.
Definition addfacts (st : sstate) (l : list fact) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (l ++ s_facts st) (s_ops st) (s_priv st) (s_next st).

Definition alk_lit (k : int) (c : w64) : bool :=
  negb (wt c) && PrimInt63.eqb (PrimInt63.land (wl c) (PrimInt63.sub (PrimInt63.lsl 1%uint63 k) 1%uint63)) 0%uint63.
Fixpoint alk_sv (k : int) (fs : list fact) (v : sv) {struct v} : bool :=
  PrimInt63.eqb k 0%uint63 ||| div8 fs v |||
  match v with
  | VL c => alk_lit k c
  | VP n o => alk_lit k o && (PrimInt63.leb k (find_align fs n) ||| div8 fs (VP n wzero))
  | VAlu ALU_ADD a b => alk_sv k fs a &&& alk_sv k fs b
  | VAlu ALU_SLL a (VL s) => PrimInt63.leb k (shamt6 s) ||| alk_sv (PrimInt63.sub k (shamt6 s)) fs a
  | VMd M_MUL a (VL c) => alk_lit k c ||| alk_sv k fs a
  | _ => false
  end.
Definition al8_sv (fs : list fact) (v : sv) : bool := alk_sv 3%uint63 fs v.

Definition div8x (fs : list fact) (xs : sv) : bool := div8 fs xs ||| al8_sv fs xs.
Definition size_shape_ok (fs : list fact) (n : sv) : bool :=
  match n with
  | VL _ => true
  | _ => al8_sv fs n
         ||| KnownT.KnownT.known_eq_t fs (VAlu ALU_AND n (VL (wlit 7%uint63))) (VL wzero) ||| KnownT.KnownT.known_eq_t fs (sz_and7 n) (VL wzero)
         ||| KnownT.KnownT.known_leu_t fs (sz_and7 n) (VL wzero)
  end.

Definition size_tail_ok (fs : list fact) (n : sv) : bool :=
  match n with
  | VL _ => false
  | _ => KnownT.KnownT.known_ltu_t fs (VL wzero) n
  end.

Definition unw_stop (st : sstate) : bool := KnownT.KnownT.known_leu_t (s_facts st) (getr st X8) (getr st X2).

Definition cell_eqb (a b : cell) : bool := PrimInt63.eqb (c_idx a) (c_idx b) && PrimInt63.eqb (c_w a) (c_w b) && sv_eqb (c_v a) (c_v b).
Fixpoint slot_eqb (a b : list cell) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => cell_eqb x y && slot_eqb a' b' | _, _ => false end.
Definition gran_eqb (a b : gran) : bool := Bool.eqb (g_dirty a) (g_dirty b) && slot_eqb (g_cells a) (g_cells b).
Fixpoint grans_eqb (a b : list (int * gran)) : bool :=
  match a, b with
  | [], [] => true
  | (k, g) :: a', (k', g') :: b' => PrimInt63.eqb k k' && gran_eqb g g' && grans_eqb a' b'
  | _, _ => false
  end.
Definition is_twin_region (r : region) (n : sv) : bool :=
  let t := twin_region n in
  PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (rg_hi t) && negb (rg_w r)
  && match rg_bg r with BGZero => true | _ => false end
  && grans_eqb (IMap.elements (rg_cells r)) (IMap.elements (rg_cells t)).

Definition region_is (r t : region) : bool :=
  PrimInt63.eqb (rg_lo r) (rg_lo t) && sv_eqb (rg_hi r) (rg_hi t) && Bool.eqb (rg_w r) (rg_w t)
  && match rg_bg r, rg_bg t with BGZero, BGZero => true | _, _ => false end
  && grans_eqb (IMap.elements (rg_cells r)) (IMap.elements (rg_cells t)).
Definition is_twin_main (r : region) (n : sv) : bool := region_is r (twin_main n).
Definition is_tail_region (r : region) (n : sv) : bool := region_is r (tail_region n).
Definition find_tail (fs : list fact) (sh : int) (n : sv) : option int :=
  let rhs := tail_rhs sh n in
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP s z) b :: l' => if weqb z wzero && sv_eqb b rhs then Some s else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.
Definition tail_scan (fs : list fact) (R : IMap.t region) (sh : int) (n : sv) : option int :=
  match find_tail fs sh n with
  | Some s2 => match IMap.find s2 R with
               | Some r2 => if is_tail_region r2 n && negb (PrimInt63.eqb s2 0%uint63) && negb (PrimInt63.eqb s2 sh) then Some s2 else None
               | None => None
               end
  | None => None
  end.

Definition block_of_twin (fs : list fact) (sh : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh' o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb sh sh' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some k else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition PRIM_MAXw : w64 := wlit 64512%uint63.
Definition prim_decided (fs : list fact) (n : sv) : bool := KnownT.KnownT.known_leu_t fs n (VL PRIM_MAXw).

Definition C_EXHw : w64 := wlit 1048576%uint63.
Definition cred_pre (fs : list fact) (n cred : sv) : bool := KnownT.KnownT.known_leu_t fs (VL C_EXHw) cred && (prim_decided fs n || KnownT.KnownT.known_leu_t fs n cred).
Definition cred_post (fs : list fact) (n cred : sv) : sv := if prim_decided fs n then cred else sv_alu ALU_SUB cred n.

Definition cred_fact (fs : list fact) (n cred : sv) : fact := if prim_decided fs n then FULe (VL C_EXHw) cred else FULe n cred.

Definition ub_cand (fs : list fact) (n : int) (f : fact) : option (int * w64) :=
  match f with
  | FULe (VP n' oU) (VP k cU) =>
      if PrimInt63.eqb n' n && negb (wt oU) && negb (wt cU) && PrimInt63.leb (wl oU) (wl cU) && nowrap_kb fs n oU && nowrap_kb fs k cU
      then Some (k, wsub cU oU) else None
  | _ => None
  end.
Fixpoint find_ub_go (fsA : list fact) (n : int) (fs : list fact) (acc : option (int * w64)) : option (int * w64) :=
  match fs with
  | [] => acc
  | f :: fs' =>
      find_ub_go fsA n fs'
        (match ub_cand fsA n f, acc with
         | Some (k, o), None => Some (k, o)
         | Some (k, o), Some (k0, o0) => if PrimInt63.eqb k k0 && wltu o o0 then Some (k, o) else acc
         | None, _ => acc
         end)
  end.
Definition find_ub_g (fs : list fact) (n : int) : option (int * w64) :=
  match GTwinSub.GTwinSub.find_ub fs n with
  | Some x => Some x
  | None => find_ub_go fs n fs None
  end.

Fixpoint tie_of (fs : list fact) (len : sv) : option sv :=
  match fs with
  | FEq a (VAlu ALU_SRL xs (VL c3)) :: fs' => if sv_eqb a len && weqb c3 (wlit 3%uint63) then Some xs else tie_of fs' len
  | _ :: fs' => tie_of fs' len
  | [] => None
  end.
Fixpoint find_ub_sym (fs : list fact) (ks : int) : option (w64 * int * sv) :=
  match fs with
  | FULe (VP k oU) (VAlu ALU_ADD (VP kb z) xs) :: fs' =>
      if PrimInt63.eqb k ks && weqb z wzero && negb (wt oU) then Some (oU, kb, xs) else find_ub_sym fs' ks
  | _ :: fs' => find_ub_sym fs' ks
  | [] => None
  end.

Definition len_is_twin (fs : list fact) (len n : sv) : bool :=
  sv_eqb len (twin_len n) ||| match tie_of fs len with Some xs => sv_eqb xs n &&& div8x fs xs | None => false end.

Definition twin_arm_old (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (sh : int) (len : sv) : bool :=
  match block_of_twin fs sh, IMap.find sh R with
  | Some k, Some r =>
      match CtrA.win_lookup wl0 k with
      | Some (n, kdb) => weqb kdb CtrLib.K_BLOCK &&& len_is_twin fs len n
                         &&& ((is_twin_region r n &&& size_shape_ok fs n)
                              ||| (is_twin_main r n &&& match tail_scan fs R sh n with Some _ => true | None => false end)
                              ||| prim_decided fs n)
      | None => false
      end
  | _, _ => false
  end.
Definition own_ev1 (fs : list fact) (R : IMap.t region) (kb : int) (lw : w64) (kx : int) (e : int * sv * w64) : bool :=
  let '(ks, _, kd) := e in
  negb (PrimInt63.eqb ks kx) && negb (weqb kd CtrLib.K_BLOCK) && negb (weqb kd K_TWIN) &&
  match IMap.find ks R with
  | Some r =>
      rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63 && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
      && match GTwinSub.GTwinSub.find_lb fs ks kb, find_ub_g fs ks with
         | Some o2, Some (kb', o1) =>
             PrimInt63.eqb kb' kb && negb (wt o2) && negb (wt o1) && nowrap_kb fs kb o2
             && PrimInt63.leb (wl o1) 64512%uint63
             && PrimInt63.leb (PrimInt63.add (wl o1) 8%uint63) (PrimInt63.lsl (wl lw) 3%uint63)
         | _, _ => false
         end
  | None => false
  end.

Definition twin_lit (len : sv) : bool :=
  match len with VL lw => negb (wt lw) && PrimInt63.leb (wl lw) 8064%uint63 | _ => false end.

Definition twin_small (fs : list fact) (len : sv) : bool := twin_lit len ||| KnownT.KnownT.known_leu_t fs len (VL (wlit 8064%uint63)).

Definition VECS (md : Z) : list nat :=
  if (md =? 1) || (md =? 2) then [1%nat; 4%nat]
  else if md =? 3 then [6%nat]
  else [].
Definition carg_anchor (cargs : list sv) (i : nat) : list int :=
  match nth_error cargs i with Some (VP k o) => if weqb o wzero then [k] else [] | _ => [] end.
Definition carg_vecs (st : sstate) : list int :=
  match find_op HEAP_ID (s_ops st) with
  | Some (VL md :: _ :: VL nw :: rest) => flat_map (carg_anchor (skipn (3 * Z.to_nat (to_Z (wl nw))) rest)) (VECS (w2Z md))
  | _ => []
  end.
Definition twin_arm_ev (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (cv : list int) (sh : int) (len : sv) (kx : int) : bool :=
  match len, block_of_twin fs sh with
  | VL lw, Some kb =>
      negb (wt lw) &&& PrimInt63.leb (wl lw) 8064%uint63 &&& PrimInt63.leb 3%uint63 (find_align fs kb)
      &&& (existsb (PrimInt63.eqb kb) cv ||| existsb (own_ev1 fs R kb lw kx) wl0)
  | _, _ => false
  end.

Definition own_ev1s (fs : list fact) (R : IMap.t region) (kb : int) (xs : sv) (kx : int) (e : int * sv * w64) : bool :=
  let '(ks, _, kd) := e in
  negb (PrimInt63.eqb ks kx) && negb (weqb kd CtrLib.K_BLOCK) && negb (weqb kd K_TWIN) &&
  match IMap.find ks R with
  | Some r =>
      rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63 && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
      && match GTwinSub.GTwinSub.find_lb fs ks kb, find_ub_sym fs ks with
         | Some o2, Some (oU, kb', xs') =>
             PrimInt63.eqb kb' kb && sv_eqb xs' xs && negb (wt o2) && PrimInt63.leb 8%uint63 (wl oU) && nowrap_kb fs kb o2 && nowrap_kb fs ks oU
         | _, _ => false
         end
  | None => false
  end.
Definition twin_arm_evs (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (cv : list int) (sh : int) (len : sv) (kx : int) : bool :=
  match tie_of fs len, block_of_twin fs sh with
  | Some xs, Some kb =>
      KnownT.KnownT.known_leu_t fs len (VL (wlit 8064%uint63)) &&& div8x fs xs &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) &&& nowrap_kb fs kb SYMCAPw
      &&& PrimInt63.leb 3%uint63 (find_align fs kb)
      &&& (existsb (PrimInt63.eqb kb) cv ||| existsb (own_ev1s fs R kb xs kx) wl0)
  | _, _ => false
  end.

Definition twin_arm_evx (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (cv : list int) (sh : int) (len : sv) (kx : int) : bool :=
  twin_arm_ev fs R wl0 cv sh len kx ||| twin_arm_evs fs R wl0 cv sh len kx.
Fixpoint twins_scan (fs : list fact) (R : IMap.t region) (wl0 wl : list (int * sv * w64)) : bool :=
  match wl with
  | [] => true
  | (sh, len, kd) :: wl' =>
      (if weqb kd K_TWIN then twin_lit len ||| twin_arm_old fs R wl0 sh len ||| twin_small fs len else true) &&& twins_scan fs R wl0 wl'
  end.

Definition twins_apart (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (cv : list int) (kf sh : int) : bool :=
  forallb (fun e => let '(k, len, kd) := e in
     negb (weqb kd K_TWIN) ||| PrimInt63.eqb k sh ||| twin_arm_old fs R wl k len ||| twin_arm_evx fs R wl cv k len kf) wl.

Definition sp_region (st : sstate) : option (int * w64 * region) :=
  match getr st X2 with
  | VP k off => match IMap.find k (s_regs st) with
                | Some r => if negb (PrimInt63.eqb k 0%uint63) && rg_w r && PrimInt63.eqb (PrimInt63.land (wl off) 15%uint63) 0%uint63
                               && PrimInt63.leb 4%uint63 (find_align (s_facts st) k)
                               && is_bgnone (rg_bg r)
                            then Some (k, off, r) else None
                | None => None
                end
  | _ => None
  end.
Definition stack_room_g (st : sstate) (n : int) : bool :=
  match sp_region st with
  | Some (k, off, r) =>
      match okey (wsub off (wlit n)), okey off, rg_hi r with
      | Some klo, Some ksp, VL h =>

          match okey h with
          | Some kh => kleb (rg_lo r) klo && kleb klo ksp && kleb ksp kh
          | None => false
          end
      | _, _, _ => false
      end
  | None => false
  end.

Definition region_forget_below (r : region) (ksp : int) : region :=
  let gk := granule ksp in
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
    (IMap.fold (fun g gr acc => if kltb g gk then acc else IMap.add g gr acc) (rg_cells r) IMap.empty).
Definition forget_stack_below_sp_g (st : sstate) : option sstate :=
  match sp_region st with
  | Some (k, off, r) =>
      match okey off with
      | Some ksp => Some (setregs st (IMap.add k (region_forget_below r ksp) (s_regs st)))
      | None => None
      end
  | None => None
  end.

Definition key2w (o : int) : w64 := W64 (negb (PrimInt63.ltb o bit62i)) o.

Definition TOP47i : int := 140737488355328%uint63.
Definition below_top_fast (fs : list fact) (k : int) (r : region) : bool :=
  match rg_hi r, find_range fs k with
  | VL h, Some (_, hi) =>
      negb (wt hi) &&& negb (wt h) &&& PrimInt63.leb (wl hi) TOP47i &&& PrimInt63.leb (wl h) TOP47i &&& PrimInt63.leb (PrimInt63.add (wl hi) (wl h)) TOP47i
  | _, _ => false
  end.
Definition below_top (fs : list fact) (k : int) (r : region) : bool :=
  below_top_fast fs k r |||
  known_leu_qt fs (match rg_hi r with VL h => VP k h | hi => VAlu ALU_ADD (VP k wzero) hi end) (VL (wlit 140737488355328%uint63)).

Definition zero_view (r : region) : option Z :=
  match rg_hi r, rg_bg r, rg_cells r with
  | VL h, BGZero, IMap.Leaf => if negb (rg_w r) && negb (wt h) then Some (w2Z h) else None
  | _, _, _ => None
  end.
Definition ro_lit_hi (r : region) : option Z :=
  match rg_hi r with VL h => if negb (rg_w r) && negb (wt h) then Some (w2Z h) else None | _ => None end.
Definition lit_hi (r : region) : option Z := match rg_hi r with VL h => if wt h then None else Some (w2Z h) | _ => None end.
Definition find_pin (fs : list fact) (s : int) : option w64 :=
  let fix go (l : list fact) : option w64 :=
    match l with
    | FEq (VP s' z) (VL a) :: l' => if PrimInt63.eqb s s' && weqb z wzero then Some a else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition twin_of (fs : list fact) (k : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition IMGSH : list (Z * Z) := [(0x7fffa000, 0x7fffc66c)].
Definition in_imgsh (lo hi : Z) : bool := existsb (fun v => Z.leb (fst v) lo && Z.leb hi (snd v)) IMGSH && Z.leb lo hi.

Definition pad_side (fs : list fact) (sp : sv) (k : int) (r : region) : bool :=
  match sp with
  | VP n o => PrimInt63.eqb (rg_lo r) 0%uint63 &&& wt o &&& has_fact (FULe (VP n wzero) (VP k wzero)) fs &&& nowrap_kb fs n o
  | _ => false
  end.
Definition stack_side_just (fs : list fact) (sp : sv) (spok : bool) (ks : int) (k : int) (r : region) : bool :=
  if PrimInt63.eqb k ks then below_top fs k r else
  (known_leu_s fs sp (VP k (key2w (rg_lo r)))
   ||| pad_side fs sp k r
   ||| ((PrimInt63.eqb (rg_lo r) 0%uint63 &&& negb (PrimInt63.eqb k STACK_ID) &&& stack_side_t fs sp spok k)
        ||| KnownT.KnownT.known_leu_t fs sp (VP k (key2w (rg_lo r)))))
  &&& below_top fs k r.

Definition view_T1 (fs : list fact) (R : IMap.t region) (swlo : option w64) (n : int) (los hs : Z) : bool :=
  PrimInt63.eqb n STACK_ID &&&
  match swlo, IMap.find STACK_ID R with
  | Some wlo, Some r1 =>
      match lit_hi r1 with
      | Some h1 => Z.leb (w2Zs wlo) (8 * los) &&& Z.leb (8 * hs) (h1 + 7) &&& below_top fs STACK_ID r1
      | None => false
      end
  | _, _ => false
  end.
Definition view_T2 (fs : list fact) (R : IMap.t region) (sp : sv) (spok : bool) (ks : int) (n : int) (los hs : Z) : bool :=
  match IMap.find n R with
  | Some rn =>
      match lit_hi rn with
      | Some hn => Z.eqb (keyZ (rg_lo rn) mod 8) 0 &&& Z.leb (keyZ (rg_lo rn)) (8 * los) &&& Z.leb (8 * hs) (hn + 7)
                   &&& stack_side_just fs sp spok ks n rn
      | None => false
      end
  | None => false
  end.
Definition view_TH (fs : list fact) (wl : list (int * sv * w64)) (n : int) (los hs : Z) : bool :=
  match find_ub_g fs n with
  | Some (k, o1) =>
      match GTwinSub.GTwinSub.find_lb fs n k, twin_of fs k with
      | Some o2, Some sh =>
          match CtrA.win_lookup wl sh with
          | Some (len, kd) =>
              weqb kd K_TWIN &&& PrimInt63.leb 3%uint63 (find_align fs k) &&& negb (wt o1) &&& negb (wt o2)
              &&& nowrap_kb fs k o1 &&& nowrap_kb fs k o2
              &&& Z.leb 0 (w2Z o2 / 8 + los) &&& Z.leb los hs
              &&& known_leu_qt fs (VL (wlit (Uint63.of_Z (w2Z o1 / 8 + hs)))) len &&& Z.ltb (w2Z o1 / 8 + hs) 4611686018427387904
          | None => false
          end
      | _, _ => false
      end
  | None => false
  end.
Definition view_I (fs : list fact) (s : int) (r : region) : bool :=
  match ro_lit_hi r, find_pin fs s with
  | Some hs, Some a => negb (wt a) && in_imgsh (w2Z a + keyZ (rg_lo r)) (w2Z a + hs)
  | _, _ => false
  end.

Definition tail_win_ok (fs : list fact) (wl : list (int * sv * w64)) (rhs : sv) (e : int * sv * w64) : bool :=
  let sh := fst (fst e) in
  match CtrA.win_lookup wl sh, block_of_twin fs sh with
  | Some (len, kd), Some kb =>
      match CtrA.win_lookup wl kb with
      | Some (n, kdb) =>
          if weqb kd K_TWIN && weqb kdb CtrLib.K_BLOCK then
            if sv_eqb rhs (tail_rhs sh n) then sv_eqb len (twin_len n) && size_tail_ok fs n && KnownT.KnownT.known_leu_t fs n (VL AREQMAXw) else false
          else false
      | None => false
      end
  | _, _ => false
  end.
Fixpoint tail_fact_go (fs0 : list fact) (wl : list (int * sv * w64)) (s : int) (l : list fact) : bool :=
  match l with
  | FEq (VP s' z) rhs :: l' =>
      if PrimInt63.eqb s' s && weqb z wzero then (if existsb (tail_win_ok fs0 wl rhs) wl then true else tail_fact_go fs0 wl s l')
      else tail_fact_go fs0 wl s l'
  | _ :: l' => tail_fact_go fs0 wl s l'
  | [] => false
  end.
Definition view_tail (fs : list fact) (wl : list (int * sv * w64)) (s : int) (r : region) : bool :=
  if negb (rg_w r) && PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (VL wone) then tail_fact_go fs wl s fs else false.

Fixpoint find_lb_to (fs : list fact) (n k : int) : option w64 :=
  match fs with
  | [] => None
  | FULe (VP k' o) (VP n' z) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lb_to fs' n k
  | FEq (VP n' z) (VP k' o) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lb_to fs' n k
  | _ :: fs' => find_lb_to fs' n k
  end.
Fixpoint find_ub_to (fs : list fact) (n : int) (oA : w64) (k : int) : option w64 :=
  match fs with
  | [] => None
  | FULe (VP n' o) (VP k' c) :: fs' =>
      if PrimInt63.eqb n' n && weqb o oA && PrimInt63.eqb k' k then Some c else find_ub_to fs' n oA k
  | _ :: fs' => find_ub_to fs' n oA k
  end.
Definition vec_hi_in (fs : list fact) (h len : sv) : bool :=
  match h, len with
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k z)) (VL c3), VL wlen =>
      weqb z wzero && weqb c3 (wlit 3%uint63) && negb (wt wlen) && PrimInt63.ltb (wl wlen) 288230376151711744%uint63
      && match find_lb_to fs n k, find_ub_to fs n oA k with
         | Some o2, Some cU =>
             negb (wt cU) && PrimInt63.leb (wl cU) (PrimInt63.lsl (wl wlen) 3%uint63) && negb (wt oA) && negb (wt o2)
             && nowrap_kb fs n oA && nowrap_kb fs k cU && nowrap_kb fs k o2
         | _, _ => false
         end

  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k z)) (VL c3), _ =>
      weqb z wzero && weqb c3 (wlit 3%uint63)
      && match tie_of fs len, find_lb_to fs n k with
         | Some xs, Some o2 =>
             has_fact (FULe (VP n oA) (VAlu ALU_ADD (VP k wzero) xs)) fs
             && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw && negb (wt oA) && negb (wt o2)
             && nowrap_kb fs n oA && nowrap_kb fs k o2
         | _, _ => false
         end
  | _, _ => false
  end.

Definition hi_names (rsh : region) (n : int) : bool :=
  match rg_hi rsh with
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n' _) (VP _ z)) (VL c3) => PrimInt63.eqb n' n && weqb z wzero && weqb c3 (wlit 3%uint63)
  | _ => false
  end.
Definition view_TR1 (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (n : int) (los hs : Z) (sh : int) : bool :=
  match CtrA.win_lookup wl sh, IMap.find sh R, block_of_twin fs sh with
  | Some (len, kd), Some rsh, Some kB =>
      match rg_hi rsh with
      | VAlu ALU_SRL (VAlu ALU_SUB (VP n' oA) (VP k' z)) (VL c3) =>
          weqb kd K_TWIN &&& hi_names rsh n &&& PrimInt63.eqb k' kB &&& negb (wt oA)
          &&& PrimInt63.eqb (rg_lo rsh) 0%uint63 &&& Z.leb 0 los &&& Z.leb los hs &&& Z.leb (8 * hs) (w2Z oA)
          &&& PrimInt63.leb 3%uint63 (find_align fs kB) &&& nowrap_kb fs n oA
          &&& (match find_lb_to fs n kB with Some o2 => negb (wt o2) &&& nowrap_kb fs kB o2 | None => false end)
          &&& vec_hi_in fs (rg_hi rsh) len
      | _ => false
      end
  | _, _, _ => false
  end.
Definition view_TR (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (n : int) (los hs : Z) : bool :=
  existsb (fun e => view_TR1 fs R wl n los hs (fst (fst e))) wl.
Definition view_just (fs : list fact) (R : IMap.t region) (sp : sv) (spok : bool) (wl : list (int * sv * w64)) (ks : int)
                     (swlo : option w64) (s : int) (r : region) : bool :=
  match zero_view r, block_of_twin fs s with
  | Some hs, Some n =>
      let los := keyZ (rg_lo r) in
      PrimInt63.leb 3%uint63 (find_align fs n) &&& negb (PrimInt63.eqb n 0%uint63) &&& negb (PrimInt63.eqb n s)
      &&& (view_T1 fs R swlo n los hs ||| view_TH fs wl n los hs ||| view_TR fs R wl n los hs ||| view_T2 fs R sp spok ks n los hs)
  | _, _ => false
  end
  ||| view_I fs s r ||| view_tail fs wl s r.

Definition sliver_just (fs : list fact) (R : IMap.t region) (ks : int) (swlo : option w64) (flo : bool) (k : int) (r : region) : bool :=
  match swlo, IMap.find ks R with
  | Some wlo, Some rss =>
      flo && negb (PrimInt63.ltb (rg_lo rss) bit62i)
      && rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63
      && (match rg_cells r with IMap.Leaf => true | _ => false end)
      && (match rg_bg r with BGNone => true | _ => false end)
      && sv_eqb (rg_hi r) (VAlu ALU_SUB (VP ks (key2w (rg_lo rss))) (VP STACK_ID wlo))
      && has_fact (FEq (VP k wzero) (VP STACK_ID wlo)) fs
  | _, _ => false
  end.

Definition pair_main_in (fs : list fact) (wl : list (int * sv * w64)) (k : int) (h len : sv) : bool :=
  match block_of_twin fs k with
  | Some kb => match CtrA.win_lookup wl kb with
               | Some (n, kdb) => weqb kdb CtrLib.K_BLOCK &&& sv_eqb h (sz_last n) &&& sv_eqb len (twin_len n) &&& size_tail_ok fs n
                                  &&& KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)
               | None => false
               end
  | None => false
  end.

Definition twin_full_in (fs : list fact) (h len : sv) : bool :=
  match tie_of fs len with
  | Some xs => sv_eqb h (twin_len xs) &&& div8x fs xs &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw)
  | None => false
  end.
Definition aregion_just (fs : list fact) (R : IMap.t region) (sp : sv) (spok : bool) (wl : list (int * sv * w64)) (ks : int)
                        (swlo : option w64) (flo : bool) (k : int) (r : region) : bool :=
  if PrimInt63.eqb k 0%uint63 then true else
  if PrimInt63.eqb k ks then below_top fs k r else
  if (match CtrA.win_lookup wl k with
      | Some (len, _) => PrimInt63.eqb (rg_lo r) 0%uint63 &&& (sv_eqb (rg_hi r) len ||| vec_hi_in fs (rg_hi r) len ||| pair_main_in fs wl k (rg_hi r) len ||| twin_full_in fs (rg_hi r) len ||| known_leu_qt fs (rg_hi r) len)
      | None => false
      end) then true
  else if rg_w r
       then sliver_just fs R ks swlo flo k r ||| stack_side_just fs sp spok ks k r ||| view_just fs R sp spok wl ks swlo k r
       else view_just fs R sp spok wl ks swlo k r ||| stack_side_just fs sp spok ks k r ||| sliver_just fs R ks swlo flo k r.

Fixpoint stack_window_key (n : nat) (ws : list sv) : option w64 :=
  match n, ws with
  | S n', VP k wlo :: _ :: VL kd :: ws' => if PrimInt63.eqb k STACK_ID && weqb kd wzero then Some wlo else stack_window_key n' ws'
  | S n', _ :: _ :: _ :: ws' => stack_window_key n' ws'
  | _, _ => None
  end.
Definition stack_wlo (st : sstate) : option w64 :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          match stack_window_key n rest with
          | Some wlo => if nowrap_kb (s_facts st) STACK_ID wlo then Some wlo else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition sp_floor_ok (st : sstate) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs, sp_region st with
  | Some n, _ :: _ :: _ :: rest, Some (k, _, r) =>
      match stack_window_key n rest with
      | Some wlo =>
          match okey wlo with
          | Some kw =>
              nowrap_kb (s_facts st) STACK_ID wlo &&
              (if PrimInt63.eqb k STACK_ID then kleb kw (rg_lo r)
               else match GTwinSub.GTwinSub.find_lb (s_facts st) k STACK_ID with
                    | Some o2 => nowrap_kb (s_facts st) STACK_ID o2 && Z.leb (keyZ kw) (w2Zs o2 + keyZ (rg_lo r))
                    | None => false
                    end)
          | None => false
          end
      | None => false
      end
  | _, _, _ => false
  end.

Definition sliver_floor (st : sstate) : bool :=
  match find_op HEAP_ID (s_ops st) with Some hargs => sp_floor_ok st hargs | None => false end.
Definition aregions_justified (st : sstate) (wl : list (int * sv * w64)) : bool :=
  match sp_region st with
  | Some (ks, _, _) =>
      let fs := s_facts st in let sp := getr st X2 in
      let spok := sp_below_anchor_t fs sp in
      let swlo := stack_wlo st in
      let flo := sliver_floor st in
      IMap.forallb (aregion_just fs (s_regs st) sp spok wl ks swlo flo) (s_regs st)
  | None => false
  end.

Fixpoint stack_window_ok_g (n : nat) (ws : list sv) (klo : int) : bool :=
  match n, ws with
  | S n', VP k wlo :: _ :: VL kd :: ws' =>
      (PrimInt63.eqb k STACK_ID && weqb kd wzero && match okey wlo with Some kw => kleb kw klo | None => false end)
      || stack_window_ok_g n' ws' klo
  | S n', _ :: _ :: _ :: ws' => stack_window_ok_g n' ws' klo
  | _, _ => false
  end.
Definition aheap_windows (st : sstate) : option (list sv * list (int * sv * w64)) :=
  match find_op HEAP_ID (s_ops st), CtrA.count_op HEAP_ID (s_ops st), IMap.find STACK_ID (s_regs st) with
  | Some hargs, S O, Some r1 =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          if Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1) then
            match CtrA.nonstack_windows n rest with
            | Some wl => if CtrA.windows_anchored (s_regs st) wl &&& twins_scan (s_facts st) (s_regs st) wl wl &&& aregions_justified st wl
                         then Some (hargs, wl) else None
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _ => None
  end.
Definition twins_intact (st : sstate) (hargs : list sv) : bool :=
  match aheap_windows st with Some (h, _) => true | None => false end.
Definition regions_client (st : sstate) (hargs : list sv) : bool := true.

Fixpoint zlist_eqb (a b : list Z) : bool :=
  match a, b with [] , [] => true | x :: a', y :: b' => (x =? y) && zlist_eqb a' b' | _, _ => false end.
Definition univ_ok (UNIV : list (list Z)) (PC : Z) (r : int) : bool :=
  existsb (zlist_eqb [PC; to_Z r]) UNIV && existsb (zlist_eqb [PC]) UNIV.

Definition SP_TOPw : w64 := wlit 140737488355328%uint63.
Definition sp_top_ok (st : sstate) : bool := KnownT.KnownT.known_ltu_t (s_facts st) (getr st X2) (VL SP_TOPw).

Definition SPALT : Z := 8384352.
Definition sp_altop_ok (st : sstate) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs, getr st X2 with
  | Some n, _ :: _ :: _ :: rest, VP k off =>
      match stack_window_key n rest with
      | Some wlo =>
          nowrap_kb (s_facts st) STACK_ID wlo && nowrap_kb (s_facts st) k off &&
          (if PrimInt63.eqb k STACK_ID then Z.leb (w2Zs off - w2Zs wlo) SPALT
           else match GTwinSub.GTwinSub.find_ub (s_facts st) k with
                | Some (kb, o1) => PrimInt63.eqb kb STACK_ID && nowrap_kb (s_facts st) STACK_ID o1 && Z.leb (w2Zs o1 + w2Zs off - w2Zs wlo) SPALT
                | None => false
                end)
      | None => false
      end
  | _, _, _ => false
  end.

Definition altop_ok_v (st : sstate) (hargs : list sv) (v : sv) (slack : Z) : bool :=
  match heap_nwin hargs, hargs, v with
  | Some n, _ :: _ :: _ :: rest, VP k off =>
      match stack_window_key n rest with
      | Some wlo =>
          nowrap_kb (s_facts st) STACK_ID wlo && nowrap_kb (s_facts st) k off &&
          (if PrimInt63.eqb k STACK_ID then Z.leb (w2Zs off - w2Zs wlo + slack) SPALT
           else match GTwinSub.GTwinSub.find_ub (s_facts st) k with
                | Some (kb, o1) => PrimInt63.eqb kb STACK_ID && nowrap_kb (s_facts st) STACK_ID o1 && Z.leb (w2Zs o1 + w2Zs off - w2Zs wlo + slack) SPALT
                | None => false
                end)
      | None => false
      end
  | _, _, _ => false
  end.

Definition frame_al8 (fs : list fact) (v : sv) : option bool :=
  match v with
  | VL a => Some (PrimInt63.eqb (PrimInt63.land (wl a) 7%uint63) 0%uint63)
  | VP k off => if PrimInt63.leb 3%uint63 (find_align fs k) then Some (PrimInt63.eqb (PrimInt63.land (wl off) 7%uint63) 0%uint63) else None
  | _ => None
  end.

Definition cell8 (r : region) (key : int) : option sv :=
  if PrimInt63.eqb (gidx key) 0%uint63 then
    match IMap.find (granule key) (rg_cells r) with
    | Some (Gran _ [Cell i w v]) => if PrimInt63.eqb i 0%uint63 && PrimInt63.eqb w 8%uint63 then Some v else None
    | _ => None
    end
  else None.

Definition frame_rec (st : sstate) (frame : sv) : option (sv * sv) :=
  match frame with
  | VP kf off =>
      match IMap.find kf (s_regs st), okey (wsub off (wlit 16%uint63)), okey off, PrimInt63.eqb kf 0%uint63 with
      | Some rf, Some o16, Some o0, false =>
          if kleb (rg_lo rf) o16 && kltb o16 o0 &&
             match rg_hi rf with VL h => match okey h with Some hk => kleb o0 hk | None => false end | _ => false end
          then match cell8 rf o16, cell8 rf (PrimInt63.add o16 8%uint63) with
               | Some fp, Some ra => Some (fp, ra)
               | _, _ => None
               end
          else None
      | _, _, _, _ => None
      end
  | _ => None
  end.

Definition below_stack_w (fs : list fact) (wl : list (int * sv * w64)) (k : int) (off : w64) : bool :=
  match CtrA.win_lookup wl k with
  | Some (len, _) => negb (wt off) && (KnownT.KnownT.known_ltu_t fs (VL off) len
                                       ||| (negb (weqb off wzero) &&& KnownT.KnownT.known_leu_t fs (VL off) len))
  | None => false
  end.

Fixpoint anchor_aliases (fs : list fact) (k : int) : list (int * w64) :=
  match fs with
  | [] => []
  | FEq (VP a oa) (VP b ob) :: fs' =>
      if PrimInt63.eqb b k then (a, wsub oa ob) :: anchor_aliases fs' k
      else if PrimInt63.eqb a k then (b, wsub ob oa) :: anchor_aliases fs' k
      else anchor_aliases fs' k
  | _ :: fs' => anchor_aliases fs' k
  end.
Definition below_stack (fs : list fact) (wl : list (int * sv * w64)) (v : sv) : bool :=
  match v with
  | VP k off => below_stack_w fs wl k off ||| existsb (fun kd => below_stack_w fs wl (fst kd) (wadd off (snd kd))) (anchor_aliases fs k)
  | _ => false
  end.

Inductive ucls : Type := UCStop | UCIn | UCMaybe | UCUnk.
Definition TOP47m16 : Z := 140737488355312.
Definition unw_classify (st : sstate) (hargs : list sv) (wl : list (int * sv * w64)) (prev frame : sv) : ucls :=
  let fs := s_facts st in
  if below_stack fs wl frame then UCStop else
  match KnownT.KnownT.decide_ltu_tt fs prev frame with
  | Some false => UCStop
  | Some true =>
      match frame_al8 fs frame with
      | Some false => UCStop
      | Some true =>
          match frame with
          | VL a => if Z.leb TOP47m16 (w2Z a) then UCStop else UCUnk
          | _ => if altop_ok_v st hargs frame 17 then UCIn else UCMaybe
          end
      | None => UCUnk
      end
  | None => UCUnk
  end.

Fixpoint unw_walk (fuel : nat) (st : sstate) (hargs : list sv) (wl : list (int * sv * w64)) (PCz : Z) (prev frame : sv) (k : nat) : option (list (list Z)) :=
  match fuel with
  | O => None
  | S f =>
      match k with
      | O => Some [[]]
      | S k1 =>
          match unw_classify st hargs wl prev frame with
          | UCStop => Some [[]]
          | UCUnk => None
          | c =>
              match frame_rec st frame with
              | Some (fp, VL raw) =>
                  let rz := w2Z raw in
                  if Z.ltb rz 4096 then Some [[]]
                  else
                    match unw_walk f st hargs wl PCz frame fp (if Z.eqb rz PCz then k else k1) with
                    | Some cands =>
                        let cont := map (fun tr => (if Z.eqb rz PCz then [] else [rz]) ++ tr) cands in
                        Some (match c with UCMaybe => [] :: cont | _ => cont end)
                    | None => None
                    end
              | _ => None
              end
          end
      end
  end.

Definition s0_far (st : sstate) (wl : list (int * sv * w64)) : bool :=
  below_stack (s_facts st) wl (getr st X8)
  ||| KnownT.KnownT.known_leu_t (s_facts st) (getr st X8) (getr st X2)
  ||| KnownT.KnownT.known_leu_t (s_facts st) (sv_alu ALU_ADD (getr st X2) (VL (wlit 16%uint63))) (getr st X8).
Definition unw_ok (UNIV : list (list Z)) (PCz : Z) (r : int) (st : sstate) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs with
  | Some n, _ :: _ :: _ :: rest =>
      match CtrA.nonstack_windows n rest with
      | Some wl =>
          existsb (zlist_eqb [PCz]) UNIV && s0_far st wl &&
          match unw_walk 32%nat st hargs wl PCz (getr st X2) (getr st X8) 28%nat with
          | Some cands => forallb (fun tr => Nat.leb (length tr) 28%nat && existsb (zlist_eqb (PCz :: to_Z r :: tr)) UNIV) cands
          | None => false
          end
      | None => false
      end
  | _, _ => false
  end.

Definition ret_ok (PCz : Z) (r : int) : bool := PrimInt63.leb 4096%uint63 r && negb (Z.eqb (to_Z r) PCz).

Definition sp_ok (st : sstate) : bool :=
  match getr st X2 with
  | VP k off => PrimInt63.eqb k STACK_ID && PrimInt63.eqb (PrimInt63.land (wl off) 15%uint63) 0%uint63
  | _ => false
  end.

Definition PRIST_BASEw : w64 := wlit 211106232532992%uint63.
Definition win_not_prist (fs : list fact) (l sz kd : sv) : bool :=
  match kd with
  | VL k0 =>
      if weqb k0 wzero then
        match sz with
        | VL z => if weqb z wzero then
                    match l with
                    | VL a => negb (weqb a PRIST_BASEw)
                    | _ => KnownT.KnownT.known_ltu_t fs l (VL PRIST_BASEw) || KnownT.KnownT.known_ltu_t fs (VL PRIST_BASEw) l
                    end
                  else true
        | _ => false
        end
      else true
  | _ => false
  end.
Fixpoint wins_not_prist (fs : list fact) (n : nat) (ws : list sv) : bool :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' => win_not_prist fs l sz kd && wins_not_prist fs n' ws'
  | O, _ => true
  | _, _ => false
  end.
Definition prist_absent (fs : list fact) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs with
  | Some n, _ :: _ :: _ :: rest => wins_not_prist fs n rest
  | _, _ => false
  end.

Definition sec_decided (fs : list fact) (n : sv) : bool := KnownT.KnownT.known_ltu_t fs (VL PRIM_MAXw) n.

Definition AERRNOi : int := 0x60cbdc%uint63.
Definition errno_havoc (st : sstate) : option sstate :=
  match IMap.find 0%uint63 (s_regs st) with
  | Some r0 =>
      if in_priv_b (s_priv st) AERRNOi 4%uint63 then None else
      let (e, st1) := fresh st in
      Some (SS (s_pc st1) (s_rf st1) (s_ff st1) (resv_after_store (s_facts st1) (s_resv st1) (VL (wlit AERRNOi)))
               (IMap.add 0%uint63 (Mem.region_store r0 AERRNOi 4%uint63 (VP e wzero)) (s_regs st1))
               (s_facts st1) (s_ops st1) (s_priv st1) (s_next st1))
  | None => None
  end.
Definition null_post (hargs : list sv) (cred : sv) (st2 : sstate) (r : int) : option sstate :=
  match errno_havoc (setr st2 X10 (VL wzero)), heap_set_A hargs (sv_alu ALU_SUB cred (VL C_EXHw)) with
  | Some stE, Some hN => Some (setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r)
  | _, _ => None
  end.

Definition AMALLOC_ROOM : int := 12288%uint63.

Definition amalloc_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st) with
  | Some r, VL tp, Some hargs =>
      match heap_A hargs with
      | Some cred =>
          let fs := s_facts st in let n := getr st X10 in
          if weqb tp (wlit ATPi) &&& stack_room_g st AMALLOC_ROOM &&& sp_floor_ok st hargs &&& unw_ok UNIV PCz r st hargs
             &&& sp_top_ok st &&& ret_ok PCz r
             &&& KnownT.KnownT.known_ltu_t fs (VL wzero) n &&& KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)
             &&& cred_pre fs n cred
             &&& (sec_decided fs n ||| prist_absent fs hargs)
             &&& twins_intact st hargs &&& regions_client st hargs
          then
            match forget_stack_below_sp_g st with
            | Some st1 =>
                let st2 := clobber st1 in
                match null_post hargs cred st2 r with
                | None => None
                | Some stN =>
                let (k, st3) := fresh st2 in
                let (sh, st4) := fresh st3 in
                match heap_set_A hargs (cred_post fs n cred) with
                | Some h1 =>
                    match heap_add_window h1 (VP k wzero) n (VL CtrLib.K_BLOCK) with
                    | Some h2 =>
                        match heap_add_window h2 (VP sh wzero) (twin_len n) (VL K_TWIN) with
                        | Some h3 =>

                            let R' := IMap.add sh (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4)) in
                            let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h3 (s_ops st4)) in
                            let st6 := addfact (addfact (addfact (addfact st5 (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                         (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
                            let stB := setpc (setr st6 X10 (VP k wzero)) r in

                            let (s2, st4b) := fresh st4 in
                            let Rb := IMap.add s2 (tail_region n) (IMap.add sh (twin_main n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4b))) in
                            let st5b := set_ops (setregs st4b Rb) (set_op HEAP_ID h3 (s_ops st4b)) in
                            let st6b := addfact (addfact (addfact (addfact (addfact (addfact st5b (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                         (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))))
                                         (tail_fact s2 sh n)) (FULt (VL wzero) n) in
                            let stBb := setpc (setr st6b X10 (VP k wzero)) r in
                            Some (if size_shape_ok fs n then [stN; stB]
                                  else [stN; stBb])
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Definition amalloc_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (amalloc_apply UNIV PCz).

Definition ALIGNED_NMAX : int := 4096%uint63.
Definition aligned_size_ok (n : sv) : bool :=
  match n with
  | VL w => negb (wt w) && PrimInt63.leb 16%uint63 (wl w) && PrimInt63.leb (wl w) ALIGNED_NMAX
            && PrimInt63.eqb (PrimInt63.land (wl w) 15%uint63) 0%uint63
  | _ => false
  end.
Definition aaligned_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st), getr st X10 with
  | Some r, VL tp, Some hargs, VL al =>
      match heap_A hargs with
      | Some cred =>
          let fs := s_facts st in let n := getr st X11 in
          if weqb al (wlit 16%uint63) &&& aligned_size_ok n
             &&& weqb tp (wlit ATPi) &&& stack_room_g st AMALLOC_ROOM &&& sp_floor_ok st hargs &&& unw_ok UNIV PCz r st hargs
             &&& sp_top_ok st &&& ret_ok PCz r
             &&& cred_pre fs n cred
             &&& prist_absent fs hargs
             &&& twins_intact st hargs &&& regions_client st hargs
          then
            match forget_stack_below_sp_g st with
            | Some st1 =>
                let st2 := clobber st1 in
                match null_post hargs cred st2 r with
                | None => None
                | Some stN =>
                let (k, st3) := fresh st2 in
                let (sh, st4) := fresh st3 in
                match heap_set_A hargs (cred_post fs n cred) with
                | Some h1 =>
                    match heap_add_window h1 (VP k wzero) n (VL CtrLib.K_BLOCK) with
                    | Some h2 =>
                        match heap_add_window h2 (VP sh wzero) (twin_len n) (VL K_TWIN) with
                        | Some h3 =>
                            let R' := IMap.add sh (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4)) in
                            let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h3 (s_ops st4)) in
                            let st6 := addfact (addfact (addfact (addfact st5 (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                         (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
                            Some [stN; setpc (setr st6 X10 (VP k wzero)) r]
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _, _ => None
  end.
Definition aaligned_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (aaligned_apply UNIV PCz).

Fixpoint del_window_k (n : nat) (ws : list sv) (lo : sv) (kd0 : w64) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      if sv_eqb l lo && sv_eqb kd (VL kd0) then Some ws'
      else match del_window_k n' ws' lo kd0 with Some ws'' => Some (l :: sz :: kd :: ws'') | None => None end
  | _, _ => None
  end.
Definition heap_del_window_k (args : list sv) (lo : sv) (kd0 : w64) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match del_window_k n (firstn (3 * n) rest) lo kd0 with
      | Some ws => Some (VL md :: a :: VL (wsub nw wone) :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.

Definition find_twin (fs : list fact) (k : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition acall_pre (room : int) (unw : option (list (list Z) * Z)) (st : sstate)
    : option (int * list sv * list (int * sv * w64) * sstate) :=
  match call_pre st, getr st X4, aheap_windows st with
  | Some r, VL tp, Some (hargs, wl) =>
      if weqb tp (wlit ATPi) &&& stack_room_g st room &&& sp_floor_ok st hargs &&& sp_top_ok st
         &&& match unw with
            | Some (UNIV, PCz) => unw_ok UNIV PCz r st hargs &&& ret_ok PCz r
            | None => true
            end
      then match forget_stack_below_sp_g st with
           | Some st1 => Some (r, hargs, wl, st1)
           | None => None
           end
      else None
  | _, _, _ => None
  end.

Definition aheap_windows_nt (st : sstate) : option (list sv * list (int * sv * w64)) :=
  match find_op HEAP_ID (s_ops st), CtrA.count_op HEAP_ID (s_ops st), IMap.find STACK_ID (s_regs st) with
  | Some hargs, S O, Some r1 =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          if Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1) then
            match CtrA.nonstack_windows n rest with
            | Some wl => if CtrA.windows_anchored (s_regs st) wl &&& aregions_justified st wl then Some (hargs, wl) else None
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _ => None
  end.
Definition acall_pre_nt (room : int) (unw : option (list (list Z) * Z)) (st : sstate)
    : option (int * list sv * list (int * sv * w64) * sstate) :=
  match call_pre st, getr st X4, aheap_windows_nt st with
  | Some r, VL tp, Some (hargs, wl) =>
      if weqb tp (wlit ATPi) &&& stack_room_g st room &&& sp_floor_ok st hargs &&& sp_top_ok st
         &&& match unw with
            | Some (UNIV, PCz) => unw_ok UNIV PCz r st hargs &&& ret_ok PCz r
            | None => true
            end
      then match forget_stack_below_sp_g st with
           | Some st1 => Some (r, hargs, wl, st1)
           | None => None
           end
      else None
  | _, _, _ => None
  end.

Definition afree_ok_k (kdB kdT : w64) (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : bool :=
  let fs := s_facts st in
  match IMap.find kf (s_regs st), CtrA.win_lookup wl kf, CtrA.win_lookup wl sh, block_of_twin fs sh with
  | Some rf, Some (lenf, kdf), Some (_, kdt), Some kb =>
      let full := KnownT.KnownT.known_eq_t fs (rg_hi rf) lenf in
      weqb kdf kdB && weqb kdt kdT && PrimInt63.eqb kb kf
      && PrimInt63.eqb (rg_lo rf) 0%uint63 && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi rf) && known_leu_qt fs (rg_hi rf) lenf
      && forallb (fun t : int * sv * w64 =>
                    let '(k, len, kd) := t in
                    PrimInt63.eqb k kf || PrimInt63.eqb k sh ||

                    if weqb kd K_TWIN
                    then match block_of_twin fs k with Some kb' => negb (PrimInt63.eqb kb' kf) | None => false end
                    else match IMap.find k (s_regs st) with
                         | Some r => PrimInt63.eqb (rg_lo r) 0%uint63 && known_leu_qt fs (rg_hi r) len && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
                                     && rg_w r && (weqb kd kdB || full)
                         | None => false
                         end) wl
  | _, _, _, _ => false
  end.

Definition afree_ok (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : bool := afree_ok_k CtrLib.K_BLOCK K_TWIN st wl kf sh.

Definition no_views_on (fs : list fact) (R : IMap.t region) (kf sh : int) : bool :=
  IMap.forallb (fun s r =>
     PrimInt63.eqb s sh ||
     match zero_view r, block_of_twin fs s with
     | Some _, Some n => match find_ub_g fs n with
                         | Some (k, _) => match twin_of fs k with Some s' => negb (PrimInt63.eqb s' sh) | None => true end
                         | None => true
                         end
                         && negb (PrimInt63.eqb n kf)
                         && match IMap.find sh R with Some rsh => negb (hi_names rsh n) | None => true end
     | _, _ => true
     end) R.

Fixpoint tail_named (rhs : sv) (s : int) (l : list fact) : bool :=
  match l with
  | FEq (VP s' z) b :: l' => if PrimInt63.eqb s' s && weqb z wzero && sv_eqb b rhs then true else tail_named rhs s l'
  | _ :: l' => tail_named rhs s l'
  | [] => false
  end.
Definition no_tail_at (fs : list fact) (R : IMap.t region) (sh : int) (n : sv) : bool :=
  IMap.forallb (fun s _ => negb (tail_named (tail_rhs sh n) s fs)) R.
Definition twin_canon (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : bool :=
  match IMap.find sh (s_regs st), CtrA.win_lookup wl kf, CtrA.win_lookup wl sh with
  | Some r, Some (n, _), Some (lent, _) =>
      is_twin_region r n &&& size_shape_ok (s_facts st) n &&& len_is_twin (s_facts st) lent n &&& twins_apart (s_facts st) (s_regs st) wl (carg_vecs st) kf sh
      &&& no_tail_at (s_facts st) (s_regs st) sh n
  | _, _, _ => false
  end.

Definition no_tails_on (fs : list fact) (R : IMap.t region) (sh : int) (n : sv) (s2 : int) : bool :=
  IMap.forallb (fun s _ => PrimInt63.eqb s s2 || negb (tail_named (tail_rhs sh n) s fs)) R.
Definition twin_canon_pair (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : option int :=
  match IMap.find sh (s_regs st), CtrA.win_lookup wl kf, CtrA.win_lookup wl sh with
  | Some r, Some (n, _), Some (lent, _) =>
      if is_twin_main r n &&& sv_eqb lent (twin_len n) &&& twins_apart (s_facts st) (s_regs st) wl (carg_vecs st) kf sh then
        match tail_scan (s_facts st) (s_regs st) sh n with
        | Some s2 => if no_tails_on (s_facts st) (s_regs st) sh n s2 && negb (PrimInt63.eqb s2 kf)
                        && (match CtrA.win_lookup wl s2 with None => true | Some _ => false end)
                     then Some s2 else None
        | None => None
        end
      else None
  | _, _, _ => None
  end.

Definition twin_consume (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : option (option int) :=
  if twin_canon st wl kf sh then Some None
  else match twin_canon_pair st wl kf sh with Some s2 => Some (Some s2) | None => None end.
Definition remove_opt (o : option int) (R : IMap.t region) : IMap.t region := match o with Some s2 => IMap.remove s2 R | None => R end.

Definition twin_shape_ok (st : sstate) (sh : int) (n : sv) : bool :=
  match IMap.find sh (s_regs st) with
  | Some r => (is_twin_region r n &&& size_shape_ok (s_facts st) n)
              ||| (is_twin_main r n &&& match tail_scan (s_facts st) (s_regs st) sh n with Some _ => true | None => false end)
  | None => false
  end.
Definition twin_pat_ok_t (st : sstate) (wl : list (int * sv * w64)) (kb : int) (n : sv) : bool :=
  match twin_of (s_facts st) kb with
  | Some sh => match CtrA.win_lookup wl sh with
               | Some (lent, kd) => weqb kd K_TWIN &&& sv_eqb lent (twin_len n) &&& negb (PrimInt63.eqb sh 0%uint63) &&& twin_shape_ok st sh n
               | None => false
               end
  | None => false
  end.
Definition twin_pat_ok (st : sstate) (wl : list (int * sv * w64)) (kb : int) : bool :=
  match CtrA.win_lookup wl kb with
  | Some (n, kd) => weqb kd CtrLib.K_BLOCK &&& twin_pat_ok_t st wl kb n
  | None => false
  end.

Definition afree_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match acall_pre ASTACK (Some (UNIV, PCz)) st, getr st X10 with
  | Some (r, hargs, wl, st1), VP kf off =>
      match find_twin (s_facts st) kf with
      | Some sh =>
          match twin_consume st wl kf sh with
          | Some tl =>
              if weqb off wzero && afree_ok st wl kf sh && no_views_on (s_facts st) (s_regs st) kf sh then
                match heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK with
                | Some h1 =>
                    match heap_del_window_k h1 (VP sh wzero) K_TWIN with
                    | Some h2 =>
                        let st2 := clobber st1 in
                        let (x, st3) := fresh st2 in
                        let R' := remove_opt tl (IMap.remove sh (IMap.remove kf (s_regs st3))) in
                        Some [setpc (setr (set_ops (setregs st3 R') (set_op HEAP_ID h2 (s_ops st3))) X10 (VP x wzero)) r]
                    | None => None
                    end
                | None => None
                end
              else None
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.
Definition afree_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (afree_apply UNIV PCz).

Definition afree0_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match acall_pre ASTACK (Some (UNIV, PCz)) st, getr st X10 with
  | Some (r, hargs, wl, st1), VL w =>
      if weqb w wzero then
        let st2 := clobber st1 in
        let (x, st3) := fresh st2 in
        Some [setpc (setr st3 X10 (VP x wzero)) r]
      else None
  | _, _ => None
  end.
Definition afree0_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (afree0_apply UNIV PCz).

Inductive twsel : Type := TwReg (rs : r5) (off : w64) | TwLen (n : w64).
Definition fact_on (sh : int) (f : fact) : bool :=
  match f with
  | FEq (VP s _) _ => PrimInt63.eqb s sh
  | FRange s _ _ => PrimInt63.eqb s sh
  | FAlign s _ => PrimInt63.eqb s sh
  | _ => false
  end.
Definition drop_anchor_facts (sh : int) (fs : list fact) : list fact := List.filter (fun f => negb (fact_on sh f)) fs.
Definition set_facts (st : sstate) (fs : list fact) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) fs (s_ops st) (s_priv st) (s_next st).

Definition tw_out (fs : list fact) (wl : list (int * sv * w64)) (k : int) : option (int * int) :=
  match find_twin fs k with
  | Some sh => match CtrA.win_lookup wl sh with Some _ => Some (k, sh) | None => None end
  | None => None
  end.
Fixpoint twlen_go (fs : list fact) (wl : list (int * sv * w64)) (n : w64) (l : list (int * sv * w64)) : option (int * int) :=
  match l with
  | (k, VL len, kd) :: l' => if weqb kd CtrLib.K_BLOCK && weqb len n then match tw_out fs wl k with Some p => Some p | None => twlen_go fs wl n l' end
                             else twlen_go fs wl n l'
  | _ :: l' => twlen_go fs wl n l'
  | [] => None
  end.
Definition twsel_pair (sel : twsel) (st : sstate) (wl : list (int * sv * w64)) : option (int * int) :=
  match sel with
  | TwReg rs off => match getr st rs with
                    | VP k o => if weqb o off then tw_out (s_facts st) wl k else None
                    | _ => None
                    end
  | TwLen n => twlen_go (s_facts st) wl n wl
  end.
Definition twin_in_apply (sel : twsel) (st : sstate) : option (list sstate) :=
  match aheap_windows st with
  | Some (hargs, wl) =>
      match twsel_pair sel st wl with
      | None => Some [st]
      | Some (kf, sh) =>
          if (match s_resv st with RNone => true | _ => false end) && fresh_ok st
             && stack_room_g st 0%uint63 && sp_floor_ok st hargs
             && afree_ok st wl kf sh && twin_canon st wl kf sh && no_views_on (s_facts st) (s_regs st) kf sh then
            match heap_del_window_k hargs (VP sh wzero) K_TWIN with
            | Some h1 => Some [set_facts (set_ops (setregs st (IMap.remove sh (s_regs st))) (set_op HEAP_ID h1 (s_ops st)))
                                         (drop_anchor_facts sh (s_facts st))]
            | None => None
            end
          else None
      end
  | None => None
  end.
Definition twin_in_c (pc : int) (sel : twsel) : contract := Contract pc (twin_in_apply sel).

Definition blk_reg_ok (fs : list fact) (R : IMap.t region) (k : int) : bool :=
  match IMap.find k R with
  | Some r => rg_w r &&& PrimInt63.eqb (rg_lo r) 0%uint63 &&& KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
  | None => false
  end.
Definition tw_other_ok (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (cv : list int) (kf : int) (full : bool)
    (e : int * sv * w64) : bool :=
  let '(k, len, kd) := e in
  if weqb kd K_TWIN then
    match block_of_twin fs k with
    | Some kb => negb (PrimInt63.eqb kb kf)
                 &&& ((match CtrA.win_lookup wl kb with Some (_, kdb) => weqb kdb CtrLib.K_BLOCK | None => false end &&& blk_reg_ok fs R kb)
                      ||| (full &&& twin_arm_evx fs R wl cv k len kf))
    | None => false
    end
  else true.
Fixpoint twlen_in_go (fs : list fact) (wl : list (int * sv * w64)) (n : w64) (l : list (int * sv * w64)) : option int :=
  match l with
  | (k, VL len, kd) :: l' => if weqb kd CtrLib.K_BLOCK && weqb len n
                             then match tw_out fs wl k with Some _ => twlen_in_go fs wl n l' | None => Some k end
                             else twlen_in_go fs wl n l'
  | _ :: l' => twlen_in_go fs wl n l'
  | [] => None
  end.
Definition twsel_blk (sel : twsel) (st : sstate) (wl : list (int * sv * w64)) : option int :=
  match sel with
  | TwReg rs off => match getr st rs with
                    | VP k o => if weqb o off then Some k else None
                    | _ => None
                    end
  | TwLen n => twlen_in_go (s_facts st) wl n wl
  end.
Definition link_fact (sh k : int) : fact :=
  FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)).
Definition twin_out_apply (sel : twsel) (st : sstate) : option (list sstate) :=
  match aheap_windows st with
  | Some (hargs, wl) =>
      match twsel_blk sel st wl with
      | None => Some [st]
      | Some kf =>
          match tw_out (s_facts st) wl kf with
          | Some _ => Some [st]
          | None =>
              match CtrA.win_lookup wl kf, IMap.find kf (s_regs st) with
              | Some (n, kd), Some rf =>
                  let fs := s_facts st in
                  if (match s_resv st with RNone => true | _ => false end) &&& fresh_ok st
                     &&& stack_room_g st 0%uint63 &&& sp_floor_ok st hargs
                     &&& weqb kd CtrLib.K_BLOCK &&& (match find_twin fs kf with None => true | Some _ => false end)
                     &&& rg_w rf &&& PrimInt63.eqb (rg_lo rf) 0%uint63 &&& KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi rf)
                     &&& size_shape_ok fs n
                     &&& forallb (tw_other_ok fs (s_regs st) wl (carg_vecs st) kf (KnownT.KnownT.known_eq_t fs (rg_hi rf) n)) wl
                  then
                    let (sh, st1) := fresh st in
                    match heap_add_window hargs (VP sh wzero) (twin_len n) (VL K_TWIN) with
                    | Some h1 =>
                        Some [addfact (set_ops (setregs st1 (IMap.add sh (twin_region n) (s_regs st1))) (set_op HEAP_ID h1 (s_ops st1)))
                                      (link_fact sh kf)]
                    | None => None
                    end
                  else None
              | _, _ => None
              end
          end
      end
  | None => None
  end.
Definition twin_out_c (pc : int) (sel : twsel) : contract := Contract pc (twin_out_apply sel).

Definition B61w : w64 := wlit 0x2000000000000000%uint63.
Definition AREQMAX4w : w64 := wlit 0x3FFC00000%uint63.

Definition tier1 {A} (fs : list fact) (vs : list int) (q : list fact -> option A) : option A := q (rel_facts vs fs).
Definition tiers12 {A} (fs : list fact) (vs : list int) (q : list fact -> option A) : option A :=
  match q (rel_facts vs fs) with Some r => Some r | None => q (rel_facts (close_vs fs vs vs) fs) end.
Definition known_ltu_t1 (fs : list fact) (a b : sv) : bool := Step.dec_true (tier1 fs (sv_vs a (sv_vs b [])) (fun l => decide_ltu l a b)).
Definition known_leu_t1 (fs : list fact) (a b : sv) : bool := Step.dec_false (tier1 fs (sv_vs b (sv_vs a [])) (fun l => decide_ltu l b a)).
Definition known_leu_t12 (fs : list fact) (a b : sv) : bool := Step.dec_false (tiers12 fs (sv_vs b (sv_vs a [])) (fun l => decide_ltu l b a)).
Definition reqmax_x4 (fs : list fact) (n : sv) : bool :=
  KnownT.KnownT.known_ltu_t fs n (VL B61w) &&& KnownT.KnownT.known_leu_t fs (VAlu ALU_SLL n (VL (wlit 2%uint63))) (VL AREQMAX4w).
Definition reqmax_x4_t1 (fs : list fact) (n : sv) : bool :=
  known_ltu_t1 fs n (VL B61w) &&& known_leu_t1 fs (VAlu ALU_SLL n (VL (wlit 2%uint63))) (VL AREQMAX4w).

Definition reqmax_ok_spec (fs : list fact) (n : sv) : bool :=
  KnownT.KnownT.known_leu_t fs n (VL AREQMAXw) ||| reqmax_x4 fs n.
Definition reqmax_ok (fs : list fact) (n : sv) : bool :=
  reqmax_x4_t1 fs n ||| known_leu_t12 fs n (VL AREQMAXw) ||| reqmax_x4 fs n ||| KnownT.KnownT.known_leu_t fs n (VL AREQMAXw).
Definition AREALLOC_ROOM : int := 12288%uint63.
Definition arealloc_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match acall_pre AREALLOC_ROOM (Some (UNIV, PCz)) st, getr st X10 with
  | Some (r, hargs, wl, st1), VP kf off =>
      match find_twin (s_facts st) kf, heap_A hargs with
      | Some sh, Some cred =>
          let fs := s_facts st in let n := getr st X11 in
          if weqb off wzero && afree_ok st wl kf sh && twin_canon st wl kf sh && no_views_on fs (s_regs st) kf sh
             && KnownT.KnownT.known_ltu_t fs (VL wzero) n && reqmax_ok fs n && size_shape_ok fs n && cred_pre fs n cred
             && prist_absent fs hargs
          then
            let st2 := clobber st1 in
            match null_post hargs cred st2 r with
            | None => None
            | Some stN =>
            match heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK with
            | Some h1 =>
                match heap_del_window_k h1 (VP sh wzero) K_TWIN with
                | Some h2 =>
                    let (k, st3) := fresh st2 in
                    let (sh', st4) := fresh st3 in
                    match heap_set_A h2 (cred_post fs n cred) with
                    | Some h3 =>
                        match heap_add_window h3 (VP k wzero) n (VL CtrLib.K_BLOCK) with
                        | Some h4 =>
                            match heap_add_window h4 (VP sh' wzero) (twin_len n) (VL K_TWIN) with
                            | Some h5 =>
                                let R' := IMap.add sh' (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty)
                                            (IMap.remove sh (IMap.remove kf (s_regs st4)))) in
                                let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h5 (s_ops st4)) in
                                let st6 := addfact (addfact (addfact (addfact st5 (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                             (FEq (VP sh' wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
                                let st7 := addfacts st6 (and7_facts n) in
                                Some [stN; setpc (setr st7 X10 (VP k wzero)) r]
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Definition arealloc_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (arealloc_apply UNIV PCz).

Definition vec_hi (n : int) (oA : w64) (k : int) : sv := VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k wzero)) (VL (wlit 3%uint63)).

Definition hi_mid (k : int) (h : sv) : option sv :=
  match h with
  | VL g => if negb (wt g) && PrimInt63.ltb (wl g) 288230376151711744%uint63
            then Some (VP k (wlit (PrimInt63.lsl (wl g) 3%uint63))) else None
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k' z)) (VL c) =>
      if PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63) then Some (VP n oA) else None
  | _ => None
  end.

Definition mid_hi (fs : list fact) (k : int) (mid : sv) : option sv :=
  match mid with
  | VP n o =>
      if PrimInt63.eqb n k then (if al8 o then Some (VL (wlit (PrimInt63.lsr (wl o) 3%uint63))) else None)
      else match find_lb_to fs n k with
           | Some o2 =>
               if al8 o && al8 o2 && PrimInt63.leb 3%uint63 (find_align fs n) && nowrap_kb fs n o && nowrap_kb fs k o2
               then Some (vec_hi n o k) else None
           | None => None
           end
  | VAlu ALU_ADD (VP k' z) xs =>
      if PrimInt63.eqb k' k && weqb z wzero && div8x fs xs && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw
      then Some (twin_len xs) else None
  | _ => None
  end.
Definition annot_tails_ok (st : sstate) (wnl : list (int * sv * w64)) (k sh : int) : bool :=
  match CtrA.win_lookup wnl k with
  | Some (n, _) => IMap.forallb (fun s _ => negb (tail_named (tail_rhs sh n) s (s_facts st))) (s_regs st)
  | None => true
  end.

Definition blk_win_pos (st : sstate) (wnl : list (int * sv * w64)) (x : int) : bool :=
  match CtrA.win_lookup wnl x with
  | Some (n, kd) => weqb kd CtrLib.K_BLOCK &&& KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) n
  | None => false
  end.
Definition blk_reg_w (st : sstate) (x : int) : bool :=
  match IMap.find x (s_regs st) with
  | Some r => rg_w r &&& PrimInt63.eqb (rg_lo r) 0%uint63 &&& KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (rg_hi r)
  | None => false
  end.
Definition annot_other_ok (st : sstate) (wnl : list (int * sv * w64)) (cv : list int) (k sh : int) (len : sv) (e : int * sv * w64) : bool :=
  let '(k0, len0, kd0) := e in
  PrimInt63.eqb k0 sh |||
  (if weqb kd0 K_TWIN then
     (match len0, len with VL l0, VL wlen => negb (weqb l0 wlen) | _, _ => false end)
     ||| match block_of_twin (s_facts st) k0 with
         | Some k2 =>
             negb (PrimInt63.eqb k2 k) &&& PrimInt63.leb 3%uint63 (find_align (s_facts st) k2)
             &&& ((existsb (PrimInt63.eqb k) cv &&& existsb (PrimInt63.eqb k2) cv)
                  ||| (existsb (PrimInt63.eqb k) cv &&& blk_win_pos st wnl k2)
                  ||| (blk_win_pos st wnl k &&& existsb (PrimInt63.eqb k2) cv)
                  ||| (blk_reg_w st k &&& blk_reg_w st k2))
         | None => false
         end
   else negb (wt kd0) &&& PrimInt63.leb (wl kd0) 8%uint63).
Definition annot_others_ok (st : sstate) (wnl : list (int * sv * w64)) (k sh : int) (len : sv) : bool :=
  let cv := carg_vecs st in forallb (annot_other_ok st wnl cv k sh len) wnl.

Definition annot_end_ok (fs : list fact) (k : int) (len x11 : sv) : bool :=
  match len with
  | VL wlen => negb (wt wlen) &&& KnownT.KnownT.known_leu_t fs x11 (VP k (wlit (PrimInt63.lsl (wl wlen) 3%uint63)))
  | _ => match tie_of fs len with
         | Some xs => (sv_eqb x11 (VAlu ALU_ADD (VP k wzero) xs) ||| has_fact (FULe x11 (VAlu ALU_ADD (VP k wzero) xs)) fs)
                      &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) &&& nowrap_kb fs k SYMCAPw
         | None => false
         end
  end.
Definition ANNOT_ROOM : int := 4096%uint63.
Definition ANNOT_WMAX : int := 8064%uint63.
Definition annotate_apply (st : sstate) : option (list sstate) :=
  match acall_pre ANNOT_ROOM None st, getr st X10 with
  | Some (r, hargs, wnl, st1), VP k zb =>
      let fs := s_facts st in
      match find_twin fs k with
      | Some sh =>
          match IMap.find sh (s_regs st), CtrA.win_lookup wnl sh with
          | Some rsh, Some (len, kd) =>
              match hi_mid k (rg_hi rsh), mid_hi fs k (getr st X13) with
              | Some om, Some h' =>
                  if weqb zb wzero &&& weqb kd K_TWIN &&& negb (PrimInt63.eqb sh 0%uint63)
                     &&& PrimInt63.leb 3%uint63 (find_align fs k)
                     &&& (match block_of_twin fs sh with Some kb => PrimInt63.eqb kb k | None => false end)
                     &&& twin_small fs len
                     &&& negb (rg_w rsh) &&& PrimInt63.eqb (rg_lo rsh) 0%uint63
                     &&& (match rg_cells rsh, rg_bg rsh with IMap.Leaf, BGZero => true | _, _ => false end)
                     &&& (match mid_hi fs k om with Some hO => sv_eqb hO (rg_hi rsh) | None => false end)
                     &&& KnownT.KnownT.known_eq_t fs (getr st X12) om
                     &&& KnownT.KnownT.known_leu_t fs (getr st X13) (getr st X11)
                     &&& KnownT.KnownT.known_leu_t fs (getr st X12) (getr st X11)
                     &&& al8_sv fs (getr st X11)
                     &&& annot_end_ok fs k len (getr st X11)
                     &&& no_views_on fs (s_regs st) k sh
                     &&& annot_tails_ok st wnl k sh
                     &&& annot_others_ok st wnl k sh len
                  then
                    let rsh' := Region 0%uint63 h' false BGZero IMap.empty in
                    let st2 := setregs (clobber st1) (IMap.add sh rsh' (IMap.remove sh (s_regs st1))) in
                    let (v, st3) := fresh st2 in Some [setpc (setr st3 X10 (VP v wzero)) r]
                  else None
              | _, _ => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.
Definition annotate_c (pc : int) : contract := Contract pc annotate_apply.
End ActrA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module ActrA.
Definition ATPi : int := 0x60ee40%uint63.
Definition SBw : w64 := wlit 0x7fff8000%uint63.
Definition K_TWIN : w64 := wlit 9%uint63.
Definition ASTACK : int := 8192%uint63.
Definition AREQMAXw : w64 := wlit 0xFFF00000%uint63.

Definition SYMCAPw : w64 := wlit 65536%uint63.
Definition BLK_LO : w64 := wlit 0x631000%uint63.
Definition BLK_HI : w64 := wlit 140737488355327%uint63.

Definition twin_len (n : sv) : sv :=
  match n with
  | VL w => VL (wlit (PrimInt63.lsr (PrimInt63.add (wl w) 7%uint63) 3%uint63))
  | _ => sv_alu ALU_SRL (sv_alu ALU_ADD n (VL (wlit 7%uint63))) (VL (wlit 3%uint63))
  end.
Definition twin_region (n : sv) : region :=
  let r := Region 0%uint63 (twin_len n) false BGZero IMap.empty in
  match n with
  | VL w => let t := PrimInt63.land (wl w) 7%uint63 in
            if PrimInt63.eqb t 0%uint63 then r
            else region_store r (PrimInt63.lsr (wl w) 3%uint63) 1%uint63 (VL (wlit t))
  | _ => r
  end.

Notation "a &&& b" := (if a then b else false) (at level 40, left associativity, only parsing).
Notation "a ||| b" := (if a then true else b) (at level 50, left associativity, only parsing).
Definition known_leu_s (fs : list fact) (a b : sv) : bool := dec_false (decide_ltu_s fs b a).

Definition sp_below_anchor_t (fs : list fact) (sp : sv) : bool := KnownT.KnownT.known_leu_t fs sp (VP STACK_ID wzero).
Definition stack_side_t (fs : list fact) (sp : sv) (spok : bool) (k : int) : bool :=
  if (if spok then (if CtrA.anchored_above fs k then true else KnownT.KnownT.known_leu_t fs (VP STACK_ID wzero) (VP k wzero)) else false) then true
  else KnownT.KnownT.known_leu_t fs sp (VP k wzero).
Definition known_leu_qt (fs : list fact) (a b : sv) : bool :=
  if sv_eqb a b then true else
  if fact_lookup fs (is_FULe a b) then true else
  if fact_lookup fs (is_FULt a b) then true else KnownT.KnownT.known_leu_t fs a b.

Definition sz_and7 (n : sv) : sv := sv_alu ALU_AND n (VL (wlit 7%uint63)).
Definition sz_last (n : sv) : sv := sv_alu ALU_SRL (sv_alu ALU_ADD n (VL wones)) (VL (wlit 3%uint63)).
Definition twin_main (n : sv) : region := Region 0%uint63 (sz_last n) false BGZero IMap.empty.
Definition tail_region (n : sv) : region :=
  region_store (Region 0%uint63 (VL wone) false BGZero IMap.empty) 0%uint63 1%uint63 (sz_and7 n).
Definition tail_rhs (sh : int) (n : sv) : sv := sv_alu ALU_ADD (VP sh wzero) (sz_last n).
Definition tail_fact (s2 sh : int) (n : sv) : fact := FEq (VP s2 wzero) (tail_rhs sh n).

Definition al8 (o : w64) : bool := negb (wt o) && PrimInt63.eqb (PrimInt63.land (wl o) 7%uint63) 0%uint63.

Definition div8 (fs : list fact) (xs : sv) : bool := has_fact (FEq (VAlu ALU_AND xs (VL (wlit 7%uint63))) (VL wzero)) fs.

Definition and7_facts (n : sv) : list fact :=
  match n with VL _ => [] | _ => [FEq (VAlu ALU_AND n (VL (wlit 7%uint63))) (VL wzero)] end.
Definition addfacts (st : sstate) (l : list fact) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (l ++ s_facts st) (s_ops st) (s_priv st) (s_next st).

Definition alk_lit (k : int) (c : w64) : bool :=
  negb (wt c) && PrimInt63.eqb (PrimInt63.land (wl c) (PrimInt63.sub (PrimInt63.lsl 1%uint63 k) 1%uint63)) 0%uint63.
Fixpoint alk_sv (k : int) (fs : list fact) (v : sv) {struct v} : bool :=
  PrimInt63.eqb k 0%uint63 ||| div8 fs v |||
  match v with
  | VL c => alk_lit k c
  | VP n o => alk_lit k o && (PrimInt63.leb k (find_align fs n) ||| div8 fs (VP n wzero))
  | VAlu ALU_ADD a b => alk_sv k fs a &&& alk_sv k fs b
  | VAlu ALU_SLL a (VL s) => PrimInt63.leb k (shamt6 s) ||| alk_sv (PrimInt63.sub k (shamt6 s)) fs a
  | VMd M_MUL a (VL c) => alk_lit k c ||| alk_sv k fs a
  | _ => false
  end.
Definition al8_sv (fs : list fact) (v : sv) : bool := alk_sv 3%uint63 fs v.

Definition div8x (fs : list fact) (xs : sv) : bool := div8 fs xs ||| al8_sv fs xs.
Definition size_shape_ok (fs : list fact) (n : sv) : bool :=
  match n with
  | VL _ => true
  | _ => al8_sv fs n
         ||| KnownT.KnownT.known_eq_t fs (VAlu ALU_AND n (VL (wlit 7%uint63))) (VL wzero) ||| KnownT.KnownT.known_eq_t fs (sz_and7 n) (VL wzero)
         ||| KnownT.KnownT.known_leu_t fs (sz_and7 n) (VL wzero)
  end.

Definition size_tail_ok (fs : list fact) (n : sv) : bool :=
  match n with
  | VL _ => false
  | _ => KnownT.KnownT.known_ltu_t fs (VL wzero) n
  end.

Definition unw_stop (st : sstate) : bool := KnownT.KnownT.known_leu_t (s_facts st) (getr st X8) (getr st X2).

Definition cell_eqb (a b : cell) : bool := PrimInt63.eqb (c_idx a) (c_idx b) && PrimInt63.eqb (c_w a) (c_w b) && sv_eqb (c_v a) (c_v b).
Fixpoint slot_eqb (a b : list cell) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => cell_eqb x y && slot_eqb a' b' | _, _ => false end.
Definition gran_eqb (a b : gran) : bool := Bool.eqb (g_dirty a) (g_dirty b) && slot_eqb (g_cells a) (g_cells b).
Fixpoint grans_eqb (a b : list (int * gran)) : bool :=
  match a, b with
  | [], [] => true
  | (k, g) :: a', (k', g') :: b' => PrimInt63.eqb k k' && gran_eqb g g' && grans_eqb a' b'
  | _, _ => false
  end.
Definition is_twin_region (r : region) (n : sv) : bool :=
  let t := twin_region n in
  PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (rg_hi t) && negb (rg_w r)
  && match rg_bg r with BGZero => true | _ => false end
  && grans_eqb (IMap.elements (rg_cells r)) (IMap.elements (rg_cells t)).

Definition region_is (r t : region) : bool :=
  PrimInt63.eqb (rg_lo r) (rg_lo t) && sv_eqb (rg_hi r) (rg_hi t) && Bool.eqb (rg_w r) (rg_w t)
  && match rg_bg r, rg_bg t with BGZero, BGZero => true | _, _ => false end
  && grans_eqb (IMap.elements (rg_cells r)) (IMap.elements (rg_cells t)).
Definition is_twin_main (r : region) (n : sv) : bool := region_is r (twin_main n).
Definition is_tail_region (r : region) (n : sv) : bool := region_is r (tail_region n).
Definition find_tail (fs : list fact) (sh : int) (n : sv) : option int :=
  let rhs := tail_rhs sh n in
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP s z) b :: l' => if weqb z wzero && sv_eqb b rhs then Some s else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.
Definition tail_scan (fs : list fact) (R : IMap.t region) (sh : int) (n : sv) : option int :=
  match find_tail fs sh n with
  | Some s2 => match IMap.find s2 R with
               | Some r2 => if is_tail_region r2 n && negb (PrimInt63.eqb s2 0%uint63) && negb (PrimInt63.eqb s2 sh) then Some s2 else None
               | None => None
               end
  | None => None
  end.

Definition block_of_twin (fs : list fact) (sh : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh' o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb sh sh' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some k else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition PRIM_MAXw : w64 := wlit 64512%uint63.
Definition prim_decided (fs : list fact) (n : sv) : bool := KnownT.KnownT.known_leu_t fs n (VL PRIM_MAXw).

Definition C_EXHw : w64 := wlit 1048576%uint63.
Definition cred_pre (fs : list fact) (n cred : sv) : bool := KnownT.KnownT.known_leu_t fs (VL C_EXHw) cred && (prim_decided fs n || KnownT.KnownT.known_leu_t fs n cred).
Definition cred_post (fs : list fact) (n cred : sv) : sv := if prim_decided fs n then cred else sv_alu ALU_SUB cred n.

Definition cred_fact (fs : list fact) (n cred : sv) : fact := if prim_decided fs n then FULe (VL C_EXHw) cred else FULe n cred.

Definition ub_cand (fs : list fact) (n : int) (f : fact) : option (int * w64) :=
  match f with
  | FULe (VP n' oU) (VP k cU) =>
      if PrimInt63.eqb n' n && negb (wt oU) && negb (wt cU) && PrimInt63.leb (wl oU) (wl cU) && nowrap_kb fs n oU && nowrap_kb fs k cU
      then Some (k, wsub cU oU) else None
  | _ => None
  end.
Fixpoint find_ub_go (fsA : list fact) (n : int) (fs : list fact) (acc : option (int * w64)) : option (int * w64) :=
  match fs with
  | [] => acc
  | f :: fs' =>
      find_ub_go fsA n fs'
        (match ub_cand fsA n f, acc with
         | Some (k, o), None => Some (k, o)
         | Some (k, o), Some (k0, o0) => if PrimInt63.eqb k k0 && wltu o o0 then Some (k, o) else acc
         | None, _ => acc
         end)
  end.
Definition find_ub_g (fs : list fact) (n : int) : option (int * w64) :=
  match GTwinSub.GTwinSub.find_ub fs n with
  | Some x => Some x
  | None => find_ub_go fs n fs None
  end.

Fixpoint tie_of (fs : list fact) (len : sv) : option sv :=
  match fs with
  | FEq a (VAlu ALU_SRL xs (VL c3)) :: fs' => if sv_eqb a len && weqb c3 (wlit 3%uint63) then Some xs else tie_of fs' len
  | _ :: fs' => tie_of fs' len
  | [] => None
  end.
Fixpoint find_ub_sym (fs : list fact) (ks : int) : option (w64 * int * sv) :=
  match fs with
  | FULe (VP k oU) (VAlu ALU_ADD (VP kb z) xs) :: fs' =>
      if PrimInt63.eqb k ks && weqb z wzero && negb (wt oU) then Some (oU, kb, xs) else find_ub_sym fs' ks
  | _ :: fs' => find_ub_sym fs' ks
  | [] => None
  end.

Definition len_is_twin (fs : list fact) (len n : sv) : bool :=
  sv_eqb len (twin_len n) ||| match tie_of fs len with Some xs => sv_eqb xs n &&& div8x fs xs | None => false end.

Definition twin_arm_old (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (sh : int) (len : sv) : bool :=
  match block_of_twin fs sh, IMap.find sh R with
  | Some k, Some r =>
      match CtrA.win_lookup wl0 k with
      | Some (n, kdb) => weqb kdb CtrLib.K_BLOCK &&& len_is_twin fs len n
                         &&& ((is_twin_region r n &&& size_shape_ok fs n)
                              ||| (is_twin_main r n &&& match tail_scan fs R sh n with Some _ => true | None => false end)
                              ||| prim_decided fs n)
      | None => false
      end
  | _, _ => false
  end.
Definition own_ev1 (fs : list fact) (R : IMap.t region) (kb : int) (lw : w64) (kx : int) (e : int * sv * w64) : bool :=
  let '(ks, _, kd) := e in
  negb (PrimInt63.eqb ks kx) && negb (weqb kd CtrLib.K_BLOCK) && negb (weqb kd K_TWIN) &&
  match IMap.find ks R with
  | Some r =>
      rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63 && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
      && match GTwinSub.GTwinSub.find_lb fs ks kb, find_ub_g fs ks with
         | Some o2, Some (kb', o1) =>
             PrimInt63.eqb kb' kb && negb (wt o2) && negb (wt o1) && nowrap_kb fs kb o2
             && PrimInt63.leb (wl o1) 64512%uint63
             && PrimInt63.leb (PrimInt63.add (wl o1) 8%uint63) (PrimInt63.lsl (wl lw) 3%uint63)
         | _, _ => false
         end
  | None => false
  end.

Definition twin_lit (len : sv) : bool :=
  match len with VL lw => negb (wt lw) && PrimInt63.leb (wl lw) 8064%uint63 | _ => false end.

Definition twin_small (fs : list fact) (len : sv) : bool := twin_lit len ||| KnownT.KnownT.known_leu_t fs len (VL (wlit 8064%uint63)).

Definition VECS (md : Z) : list nat :=
  if (md =? 1) || (md =? 2) then [1%nat; 4%nat]
  else if md =? 3 then [6%nat]
  else [].
Definition carg_anchor (cargs : list sv) (i : nat) : list int :=
  match nth_error cargs i with Some (VP k o) => if weqb o wzero then [k] else [] | _ => [] end.
Definition carg_vecs (st : sstate) : list int :=
  match find_op HEAP_ID (s_ops st) with
  | Some (VL md :: _ :: VL nw :: rest) => flat_map (carg_anchor (skipn (3 * Z.to_nat (to_Z (wl nw))) rest)) (VECS (w2Z md))
  | _ => []
  end.
Definition twin_arm_ev (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (cv : list int) (sh : int) (len : sv) (kx : int) : bool :=
  match len, block_of_twin fs sh with
  | VL lw, Some kb =>
      negb (wt lw) &&& PrimInt63.leb (wl lw) 8064%uint63 &&& PrimInt63.leb 3%uint63 (find_align fs kb)
      &&& (existsb (PrimInt63.eqb kb) cv ||| existsb (own_ev1 fs R kb lw kx) wl0)
  | _, _ => false
  end.

Definition own_ev1s (fs : list fact) (R : IMap.t region) (kb : int) (xs : sv) (kx : int) (e : int * sv * w64) : bool :=
  let '(ks, _, kd) := e in
  negb (PrimInt63.eqb ks kx) && negb (weqb kd CtrLib.K_BLOCK) && negb (weqb kd K_TWIN) &&
  match IMap.find ks R with
  | Some r =>
      rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63 && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
      && match GTwinSub.GTwinSub.find_lb fs ks kb, find_ub_sym fs ks with
         | Some o2, Some (oU, kb', xs') =>
             PrimInt63.eqb kb' kb && sv_eqb xs' xs && negb (wt o2) && PrimInt63.leb 8%uint63 (wl oU) && nowrap_kb fs kb o2 && nowrap_kb fs ks oU
         | _, _ => false
         end
  | None => false
  end.
Definition twin_arm_evs (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (cv : list int) (sh : int) (len : sv) (kx : int) : bool :=
  match tie_of fs len, block_of_twin fs sh with
  | Some xs, Some kb =>
      KnownT.KnownT.known_leu_t fs len (VL (wlit 8064%uint63)) &&& div8x fs xs &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) &&& nowrap_kb fs kb SYMCAPw
      &&& PrimInt63.leb 3%uint63 (find_align fs kb)
      &&& (existsb (PrimInt63.eqb kb) cv ||| existsb (own_ev1s fs R kb xs kx) wl0)
  | _, _ => false
  end.

Definition twin_arm_evx (fs : list fact) (R : IMap.t region) (wl0 : list (int * sv * w64)) (cv : list int) (sh : int) (len : sv) (kx : int) : bool :=
  twin_arm_ev fs R wl0 cv sh len kx ||| twin_arm_evs fs R wl0 cv sh len kx.
Fixpoint twins_scan (fs : list fact) (R : IMap.t region) (wl0 wl : list (int * sv * w64)) : bool :=
  match wl with
  | [] => true
  | (sh, len, kd) :: wl' =>
      (if weqb kd K_TWIN then twin_lit len ||| twin_arm_old fs R wl0 sh len ||| twin_small fs len else true) &&& twins_scan fs R wl0 wl'
  end.

Definition twins_apart (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (cv : list int) (kf sh : int) : bool :=
  forallb (fun e => let '(k, len, kd) := e in
     negb (weqb kd K_TWIN) ||| PrimInt63.eqb k sh ||| twin_arm_old fs R wl k len ||| twin_arm_evx fs R wl cv k len kf) wl.

Definition sp_region (st : sstate) : option (int * w64 * region) :=
  match getr st X2 with
  | VP k off => match IMap.find k (s_regs st) with
                | Some r => if negb (PrimInt63.eqb k 0%uint63) && rg_w r && PrimInt63.eqb (PrimInt63.land (wl off) 15%uint63) 0%uint63
                               && PrimInt63.leb 4%uint63 (find_align (s_facts st) k)
                               && is_bgnone (rg_bg r)
                            then Some (k, off, r) else None
                | None => None
                end
  | _ => None
  end.
Definition stack_room_g (st : sstate) (n : int) : bool :=
  match sp_region st with
  | Some (k, off, r) =>
      match okey (wsub off (wlit n)), okey off, rg_hi r with
      | Some klo, Some ksp, VL h =>

          match okey h with
          | Some kh => kleb (rg_lo r) klo && kleb klo ksp && kleb ksp kh
          | None => false
          end
      | _, _, _ => false
      end
  | None => false
  end.

Definition region_forget_below (r : region) (ksp : int) : region :=
  let gk := granule ksp in
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r)
    (IMap.fold (fun g gr acc => if kltb g gk then acc else IMap.add g gr acc) (rg_cells r) IMap.empty).
Definition forget_stack_below_sp_g (st : sstate) : option sstate :=
  match sp_region st with
  | Some (k, off, r) =>
      match okey off with
      | Some ksp => Some (setregs st (IMap.add k (region_forget_below r ksp) (s_regs st)))
      | None => None
      end
  | None => None
  end.

Definition key2w (o : int) : w64 := W64 (negb (PrimInt63.ltb o bit62i)) o.

Definition TOP47i : int := 140737488355328%uint63.
Definition below_top_fast (fs : list fact) (k : int) (r : region) : bool :=
  match rg_hi r, find_range fs k with
  | VL h, Some (_, hi) =>
      negb (wt hi) &&& negb (wt h) &&& PrimInt63.leb (wl hi) TOP47i &&& PrimInt63.leb (wl h) TOP47i &&& PrimInt63.leb (PrimInt63.add (wl hi) (wl h)) TOP47i
  | _, _ => false
  end.
Definition below_top (fs : list fact) (k : int) (r : region) : bool :=
  below_top_fast fs k r |||
  known_leu_qt fs (match rg_hi r with VL h => VP k h | hi => VAlu ALU_ADD (VP k wzero) hi end) (VL (wlit 140737488355328%uint63)).

Definition zero_view (r : region) : option Z :=
  match rg_hi r, rg_bg r, rg_cells r with
  | VL h, BGZero, IMap.Leaf => if negb (rg_w r) && negb (wt h) then Some (w2Z h) else None
  | _, _, _ => None
  end.
Definition ro_lit_hi (r : region) : option Z :=
  match rg_hi r with VL h => if negb (rg_w r) && negb (wt h) then Some (w2Z h) else None | _ => None end.
Definition lit_hi (r : region) : option Z := match rg_hi r with VL h => if wt h then None else Some (w2Z h) | _ => None end.
Definition find_pin (fs : list fact) (s : int) : option w64 :=
  let fix go (l : list fact) : option w64 :=
    match l with
    | FEq (VP s' z) (VL a) :: l' => if PrimInt63.eqb s s' && weqb z wzero then Some a else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition twin_of (fs : list fact) (k : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition IMGSH : list (Z * Z) := [(0x7fffa000, 0x7fffc6a0)].
Definition in_imgsh (lo hi : Z) : bool := existsb (fun v => Z.leb (fst v) lo && Z.leb hi (snd v)) IMGSH && Z.leb lo hi.

Definition pad_side (fs : list fact) (sp : sv) (k : int) (r : region) : bool :=
  match sp with
  | VP n o => PrimInt63.eqb (rg_lo r) 0%uint63 &&& wt o &&& has_fact (FULe (VP n wzero) (VP k wzero)) fs &&& nowrap_kb fs n o
  | _ => false
  end.
Definition stack_side_just (fs : list fact) (sp : sv) (spok : bool) (ks : int) (k : int) (r : region) : bool :=
  if PrimInt63.eqb k ks then below_top fs k r else
  (known_leu_s fs sp (VP k (key2w (rg_lo r)))
   ||| pad_side fs sp k r
   ||| ((PrimInt63.eqb (rg_lo r) 0%uint63 &&& negb (PrimInt63.eqb k STACK_ID) &&& stack_side_t fs sp spok k)
        ||| KnownT.KnownT.known_leu_t fs sp (VP k (key2w (rg_lo r)))))
  &&& below_top fs k r.

Definition view_T1 (fs : list fact) (R : IMap.t region) (swlo : option w64) (n : int) (los hs : Z) : bool :=
  PrimInt63.eqb n STACK_ID &&&
  match swlo, IMap.find STACK_ID R with
  | Some wlo, Some r1 =>
      match lit_hi r1 with
      | Some h1 => Z.leb (w2Zs wlo) (8 * los) &&& Z.leb (8 * hs) (h1 + 7) &&& below_top fs STACK_ID r1
      | None => false
      end
  | _, _ => false
  end.
Definition view_T2 (fs : list fact) (R : IMap.t region) (sp : sv) (spok : bool) (ks : int) (n : int) (los hs : Z) : bool :=
  match IMap.find n R with
  | Some rn =>
      match lit_hi rn with
      | Some hn => Z.eqb (keyZ (rg_lo rn) mod 8) 0 &&& Z.leb (keyZ (rg_lo rn)) (8 * los) &&& Z.leb (8 * hs) (hn + 7)
                   &&& stack_side_just fs sp spok ks n rn
      | None => false
      end
  | None => false
  end.
Definition view_TH (fs : list fact) (wl : list (int * sv * w64)) (n : int) (los hs : Z) : bool :=
  match find_ub_g fs n with
  | Some (k, o1) =>
      match GTwinSub.GTwinSub.find_lb fs n k, twin_of fs k with
      | Some o2, Some sh =>
          match CtrA.win_lookup wl sh with
          | Some (len, kd) =>
              weqb kd K_TWIN &&& PrimInt63.leb 3%uint63 (find_align fs k) &&& negb (wt o1) &&& negb (wt o2)
              &&& nowrap_kb fs k o1 &&& nowrap_kb fs k o2
              &&& Z.leb 0 (w2Z o2 / 8 + los) &&& Z.leb los hs
              &&& known_leu_qt fs (VL (wlit (Uint63.of_Z (w2Z o1 / 8 + hs)))) len &&& Z.ltb (w2Z o1 / 8 + hs) 4611686018427387904
          | None => false
          end
      | _, _ => false
      end
  | None => false
  end.
Definition view_I (fs : list fact) (s : int) (r : region) : bool :=
  match ro_lit_hi r, find_pin fs s with
  | Some hs, Some a => negb (wt a) && in_imgsh (w2Z a + keyZ (rg_lo r)) (w2Z a + hs)
  | _, _ => false
  end.

Definition tail_win_ok (fs : list fact) (wl : list (int * sv * w64)) (rhs : sv) (e : int * sv * w64) : bool :=
  let sh := fst (fst e) in
  match CtrA.win_lookup wl sh, block_of_twin fs sh with
  | Some (len, kd), Some kb =>
      match CtrA.win_lookup wl kb with
      | Some (n, kdb) =>
          if weqb kd K_TWIN && weqb kdb CtrLib.K_BLOCK then
            if sv_eqb rhs (tail_rhs sh n) then sv_eqb len (twin_len n) && size_tail_ok fs n && KnownT.KnownT.known_leu_t fs n (VL AREQMAXw) else false
          else false
      | None => false
      end
  | _, _ => false
  end.
Fixpoint tail_fact_go (fs0 : list fact) (wl : list (int * sv * w64)) (s : int) (l : list fact) : bool :=
  match l with
  | FEq (VP s' z) rhs :: l' =>
      if PrimInt63.eqb s' s && weqb z wzero then (if existsb (tail_win_ok fs0 wl rhs) wl then true else tail_fact_go fs0 wl s l')
      else tail_fact_go fs0 wl s l'
  | _ :: l' => tail_fact_go fs0 wl s l'
  | [] => false
  end.
Definition view_tail (fs : list fact) (wl : list (int * sv * w64)) (s : int) (r : region) : bool :=
  if negb (rg_w r) && PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (VL wone) then tail_fact_go fs wl s fs else false.

Fixpoint find_lb_to (fs : list fact) (n k : int) : option w64 :=
  match fs with
  | [] => None
  | FULe (VP k' o) (VP n' z) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lb_to fs' n k
  | FEq (VP n' z) (VP k' o) :: fs' =>
      if PrimInt63.eqb n' n && PrimInt63.eqb k' k && weqb z wzero then Some o else find_lb_to fs' n k
  | _ :: fs' => find_lb_to fs' n k
  end.
Fixpoint find_ub_to (fs : list fact) (n : int) (oA : w64) (k : int) : option w64 :=
  match fs with
  | [] => None
  | FULe (VP n' o) (VP k' c) :: fs' =>
      if PrimInt63.eqb n' n && weqb o oA && PrimInt63.eqb k' k then Some c else find_ub_to fs' n oA k
  | _ :: fs' => find_ub_to fs' n oA k
  end.
Definition vec_hi_in (fs : list fact) (h len : sv) : bool :=
  match h, len with
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k z)) (VL c3), VL wlen =>
      weqb z wzero && weqb c3 (wlit 3%uint63) && negb (wt wlen) && PrimInt63.ltb (wl wlen) 288230376151711744%uint63
      && match find_lb_to fs n k, find_ub_to fs n oA k with
         | Some o2, Some cU =>
             negb (wt cU) && PrimInt63.leb (wl cU) (PrimInt63.lsl (wl wlen) 3%uint63) && negb (wt oA) && negb (wt o2)
             && nowrap_kb fs n oA && nowrap_kb fs k cU && nowrap_kb fs k o2
         | _, _ => false
         end

  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k z)) (VL c3), _ =>
      weqb z wzero && weqb c3 (wlit 3%uint63)
      && match tie_of fs len, find_lb_to fs n k with
         | Some xs, Some o2 =>
             has_fact (FULe (VP n oA) (VAlu ALU_ADD (VP k wzero) xs)) fs
             && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw && negb (wt oA) && negb (wt o2)
             && nowrap_kb fs n oA && nowrap_kb fs k o2
         | _, _ => false
         end
  | _, _ => false
  end.

Definition hi_names (rsh : region) (n : int) : bool :=
  match rg_hi rsh with
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n' _) (VP _ z)) (VL c3) => PrimInt63.eqb n' n && weqb z wzero && weqb c3 (wlit 3%uint63)
  | _ => false
  end.
Definition view_TR1 (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (n : int) (los hs : Z) (sh : int) : bool :=
  match CtrA.win_lookup wl sh, IMap.find sh R, block_of_twin fs sh with
  | Some (len, kd), Some rsh, Some kB =>
      match rg_hi rsh with
      | VAlu ALU_SRL (VAlu ALU_SUB (VP n' oA) (VP k' z)) (VL c3) =>
          weqb kd K_TWIN &&& hi_names rsh n &&& PrimInt63.eqb k' kB &&& negb (wt oA)
          &&& PrimInt63.eqb (rg_lo rsh) 0%uint63 &&& Z.leb 0 los &&& Z.leb los hs &&& Z.leb (8 * hs) (w2Z oA)
          &&& PrimInt63.leb 3%uint63 (find_align fs kB) &&& nowrap_kb fs n oA
          &&& (match find_lb_to fs n kB with Some o2 => negb (wt o2) &&& nowrap_kb fs kB o2 | None => false end)
          &&& vec_hi_in fs (rg_hi rsh) len
      | _ => false
      end
  | _, _, _ => false
  end.
Definition view_TR (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (n : int) (los hs : Z) : bool :=
  existsb (fun e => view_TR1 fs R wl n los hs (fst (fst e))) wl.
Definition view_just (fs : list fact) (R : IMap.t region) (sp : sv) (spok : bool) (wl : list (int * sv * w64)) (ks : int)
                     (swlo : option w64) (s : int) (r : region) : bool :=
  match zero_view r, block_of_twin fs s with
  | Some hs, Some n =>
      let los := keyZ (rg_lo r) in
      PrimInt63.leb 3%uint63 (find_align fs n) &&& negb (PrimInt63.eqb n 0%uint63) &&& negb (PrimInt63.eqb n s)
      &&& (view_T1 fs R swlo n los hs ||| view_TH fs wl n los hs ||| view_TR fs R wl n los hs ||| view_T2 fs R sp spok ks n los hs)
  | _, _ => false
  end
  ||| view_I fs s r ||| view_tail fs wl s r.

Definition sliver_just (fs : list fact) (R : IMap.t region) (ks : int) (swlo : option w64) (flo : bool) (k : int) (r : region) : bool :=
  match swlo, IMap.find ks R with
  | Some wlo, Some rss =>
      flo && negb (PrimInt63.ltb (rg_lo rss) bit62i)
      && rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63
      && (match rg_cells r with IMap.Leaf => true | _ => false end)
      && (match rg_bg r with BGNone => true | _ => false end)
      && sv_eqb (rg_hi r) (VAlu ALU_SUB (VP ks (key2w (rg_lo rss))) (VP STACK_ID wlo))
      && has_fact (FEq (VP k wzero) (VP STACK_ID wlo)) fs
  | _, _ => false
  end.

Definition pair_main_in (fs : list fact) (wl : list (int * sv * w64)) (k : int) (h len : sv) : bool :=
  match block_of_twin fs k with
  | Some kb => match CtrA.win_lookup wl kb with
               | Some (n, kdb) => weqb kdb CtrLib.K_BLOCK &&& sv_eqb h (sz_last n) &&& sv_eqb len (twin_len n) &&& size_tail_ok fs n
                                  &&& KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)
               | None => false
               end
  | None => false
  end.

Definition twin_full_in (fs : list fact) (h len : sv) : bool :=
  match tie_of fs len with
  | Some xs => sv_eqb h (twin_len xs) &&& div8x fs xs &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw)
  | None => false
  end.
Definition aregion_just (fs : list fact) (R : IMap.t region) (sp : sv) (spok : bool) (wl : list (int * sv * w64)) (ks : int)
                        (swlo : option w64) (flo : bool) (k : int) (r : region) : bool :=
  if PrimInt63.eqb k 0%uint63 then true else
  if PrimInt63.eqb k ks then below_top fs k r else
  if (match CtrA.win_lookup wl k with
      | Some (len, _) => PrimInt63.eqb (rg_lo r) 0%uint63 &&& (sv_eqb (rg_hi r) len ||| vec_hi_in fs (rg_hi r) len ||| pair_main_in fs wl k (rg_hi r) len ||| twin_full_in fs (rg_hi r) len ||| known_leu_qt fs (rg_hi r) len)
      | None => false
      end) then true
  else if rg_w r
       then sliver_just fs R ks swlo flo k r ||| stack_side_just fs sp spok ks k r ||| view_just fs R sp spok wl ks swlo k r
       else view_just fs R sp spok wl ks swlo k r ||| stack_side_just fs sp spok ks k r ||| sliver_just fs R ks swlo flo k r.

Fixpoint stack_window_key (n : nat) (ws : list sv) : option w64 :=
  match n, ws with
  | S n', VP k wlo :: _ :: VL kd :: ws' => if PrimInt63.eqb k STACK_ID && weqb kd wzero then Some wlo else stack_window_key n' ws'
  | S n', _ :: _ :: _ :: ws' => stack_window_key n' ws'
  | _, _ => None
  end.
Definition stack_wlo (st : sstate) : option w64 :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          match stack_window_key n rest with
          | Some wlo => if nowrap_kb (s_facts st) STACK_ID wlo then Some wlo else None
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition sp_floor_ok (st : sstate) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs, sp_region st with
  | Some n, _ :: _ :: _ :: rest, Some (k, _, r) =>
      match stack_window_key n rest with
      | Some wlo =>
          match okey wlo with
          | Some kw =>
              nowrap_kb (s_facts st) STACK_ID wlo &&
              (if PrimInt63.eqb k STACK_ID then kleb kw (rg_lo r)
               else match GTwinSub.GTwinSub.find_lb (s_facts st) k STACK_ID with
                    | Some o2 => nowrap_kb (s_facts st) STACK_ID o2 && Z.leb (keyZ kw) (w2Zs o2 + keyZ (rg_lo r))
                    | None => false
                    end)
          | None => false
          end
      | None => false
      end
  | _, _, _ => false
  end.

Definition sliver_floor (st : sstate) : bool :=
  match find_op HEAP_ID (s_ops st) with Some hargs => sp_floor_ok st hargs | None => false end.
Definition aregions_justified (st : sstate) (wl : list (int * sv * w64)) : bool :=
  match sp_region st with
  | Some (ks, _, _) =>
      let fs := s_facts st in let sp := getr st X2 in
      let spok := sp_below_anchor_t fs sp in
      let swlo := stack_wlo st in
      let flo := sliver_floor st in
      IMap.forallb (aregion_just fs (s_regs st) sp spok wl ks swlo flo) (s_regs st)
  | None => false
  end.

Fixpoint stack_window_ok_g (n : nat) (ws : list sv) (klo : int) : bool :=
  match n, ws with
  | S n', VP k wlo :: _ :: VL kd :: ws' =>
      (PrimInt63.eqb k STACK_ID && weqb kd wzero && match okey wlo with Some kw => kleb kw klo | None => false end)
      || stack_window_ok_g n' ws' klo
  | S n', _ :: _ :: _ :: ws' => stack_window_ok_g n' ws' klo
  | _, _ => false
  end.
Definition aheap_windows (st : sstate) : option (list sv * list (int * sv * w64)) :=
  match find_op HEAP_ID (s_ops st), CtrA.count_op HEAP_ID (s_ops st), IMap.find STACK_ID (s_regs st) with
  | Some hargs, S O, Some r1 =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          if Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1) then
            match CtrA.nonstack_windows n rest with
            | Some wl => if CtrA.windows_anchored (s_regs st) wl &&& twins_scan (s_facts st) (s_regs st) wl wl &&& aregions_justified st wl
                         then Some (hargs, wl) else None
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _ => None
  end.
Definition twins_intact (st : sstate) (hargs : list sv) : bool :=
  match aheap_windows st with Some (h, _) => true | None => false end.
Definition regions_client (st : sstate) (hargs : list sv) : bool := true.

Fixpoint zlist_eqb (a b : list Z) : bool :=
  match a, b with [] , [] => true | x :: a', y :: b' => (x =? y) && zlist_eqb a' b' | _, _ => false end.
Definition univ_ok (UNIV : list (list Z)) (PC : Z) (r : int) : bool :=
  existsb (zlist_eqb [PC; to_Z r]) UNIV && existsb (zlist_eqb [PC]) UNIV.

Definition SP_TOPw : w64 := wlit 140737488355328%uint63.
Definition sp_top_ok (st : sstate) : bool := KnownT.KnownT.known_ltu_t (s_facts st) (getr st X2) (VL SP_TOPw).

Definition SPALT : Z := 8384352.
Definition sp_altop_ok (st : sstate) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs, getr st X2 with
  | Some n, _ :: _ :: _ :: rest, VP k off =>
      match stack_window_key n rest with
      | Some wlo =>
          nowrap_kb (s_facts st) STACK_ID wlo && nowrap_kb (s_facts st) k off &&
          (if PrimInt63.eqb k STACK_ID then Z.leb (w2Zs off - w2Zs wlo) SPALT
           else match GTwinSub.GTwinSub.find_ub (s_facts st) k with
                | Some (kb, o1) => PrimInt63.eqb kb STACK_ID && nowrap_kb (s_facts st) STACK_ID o1 && Z.leb (w2Zs o1 + w2Zs off - w2Zs wlo) SPALT
                | None => false
                end)
      | None => false
      end
  | _, _, _ => false
  end.

Definition altop_ok_v (st : sstate) (hargs : list sv) (v : sv) (slack : Z) : bool :=
  match heap_nwin hargs, hargs, v with
  | Some n, _ :: _ :: _ :: rest, VP k off =>
      match stack_window_key n rest with
      | Some wlo =>
          nowrap_kb (s_facts st) STACK_ID wlo && nowrap_kb (s_facts st) k off &&
          (if PrimInt63.eqb k STACK_ID then Z.leb (w2Zs off - w2Zs wlo + slack) SPALT
           else match GTwinSub.GTwinSub.find_ub (s_facts st) k with
                | Some (kb, o1) => PrimInt63.eqb kb STACK_ID && nowrap_kb (s_facts st) STACK_ID o1 && Z.leb (w2Zs o1 + w2Zs off - w2Zs wlo + slack) SPALT
                | None => false
                end)
      | None => false
      end
  | _, _, _ => false
  end.

Definition frame_al8 (fs : list fact) (v : sv) : option bool :=
  match v with
  | VL a => Some (PrimInt63.eqb (PrimInt63.land (wl a) 7%uint63) 0%uint63)
  | VP k off => if PrimInt63.leb 3%uint63 (find_align fs k) then Some (PrimInt63.eqb (PrimInt63.land (wl off) 7%uint63) 0%uint63) else None
  | _ => None
  end.

Definition cell8 (r : region) (key : int) : option sv :=
  if PrimInt63.eqb (gidx key) 0%uint63 then
    match IMap.find (granule key) (rg_cells r) with
    | Some (Gran _ [Cell i w v]) => if PrimInt63.eqb i 0%uint63 && PrimInt63.eqb w 8%uint63 then Some v else None
    | _ => None
    end
  else None.

Definition frame_rec (st : sstate) (frame : sv) : option (sv * sv) :=
  match frame with
  | VP kf off =>
      match IMap.find kf (s_regs st), okey (wsub off (wlit 16%uint63)), okey off, PrimInt63.eqb kf 0%uint63 with
      | Some rf, Some o16, Some o0, false =>
          if kleb (rg_lo rf) o16 && kltb o16 o0 &&
             match rg_hi rf with VL h => match okey h with Some hk => kleb o0 hk | None => false end | _ => false end
          then match cell8 rf o16, cell8 rf (PrimInt63.add o16 8%uint63) with
               | Some fp, Some ra => Some (fp, ra)
               | _, _ => None
               end
          else None
      | _, _, _, _ => None
      end
  | _ => None
  end.

Definition below_stack_w (fs : list fact) (wl : list (int * sv * w64)) (k : int) (off : w64) : bool :=
  match CtrA.win_lookup wl k with
  | Some (len, _) => negb (wt off) && (KnownT.KnownT.known_ltu_t fs (VL off) len
                                       ||| (negb (weqb off wzero) &&& KnownT.KnownT.known_leu_t fs (VL off) len))
  | None => false
  end.

Fixpoint anchor_aliases (fs : list fact) (k : int) : list (int * w64) :=
  match fs with
  | [] => []
  | FEq (VP a oa) (VP b ob) :: fs' =>
      if PrimInt63.eqb b k then (a, wsub oa ob) :: anchor_aliases fs' k
      else if PrimInt63.eqb a k then (b, wsub ob oa) :: anchor_aliases fs' k
      else anchor_aliases fs' k
  | _ :: fs' => anchor_aliases fs' k
  end.
Definition below_stack (fs : list fact) (wl : list (int * sv * w64)) (v : sv) : bool :=
  match v with
  | VP k off => below_stack_w fs wl k off ||| existsb (fun kd => below_stack_w fs wl (fst kd) (wadd off (snd kd))) (anchor_aliases fs k)
  | _ => false
  end.

Inductive ucls : Type := UCStop | UCIn | UCMaybe | UCUnk.
Definition TOP47m16 : Z := 140737488355312.
Definition unw_classify (st : sstate) (hargs : list sv) (wl : list (int * sv * w64)) (prev frame : sv) : ucls :=
  let fs := s_facts st in
  if below_stack fs wl frame then UCStop else
  match KnownT.KnownT.decide_ltu_tt fs prev frame with
  | Some false => UCStop
  | Some true =>
      match frame_al8 fs frame with
      | Some false => UCStop
      | Some true =>
          match frame with
          | VL a => if Z.leb TOP47m16 (w2Z a) then UCStop else UCUnk
          | _ => if altop_ok_v st hargs frame 17 then UCIn else UCMaybe
          end
      | None => UCUnk
      end
  | None => UCUnk
  end.

Fixpoint unw_walk (fuel : nat) (st : sstate) (hargs : list sv) (wl : list (int * sv * w64)) (PCz : Z) (prev frame : sv) (k : nat) : option (list (list Z)) :=
  match fuel with
  | O => None
  | S f =>
      match k with
      | O => Some [[]]
      | S k1 =>
          match unw_classify st hargs wl prev frame with
          | UCStop => Some [[]]
          | UCUnk => None
          | c =>
              match frame_rec st frame with
              | Some (fp, VL raw) =>
                  let rz := w2Z raw in
                  if Z.ltb rz 4096 then Some [[]]
                  else
                    match unw_walk f st hargs wl PCz frame fp (if Z.eqb rz PCz then k else k1) with
                    | Some cands =>
                        let cont := map (fun tr => (if Z.eqb rz PCz then [] else [rz]) ++ tr) cands in
                        Some (match c with UCMaybe => [] :: cont | _ => cont end)
                    | None => None
                    end
              | _ => None
              end
          end
      end
  end.

Definition s0_far (st : sstate) (wl : list (int * sv * w64)) : bool :=
  below_stack (s_facts st) wl (getr st X8)
  ||| KnownT.KnownT.known_leu_t (s_facts st) (getr st X8) (getr st X2)
  ||| KnownT.KnownT.known_leu_t (s_facts st) (sv_alu ALU_ADD (getr st X2) (VL (wlit 16%uint63))) (getr st X8).
Definition unw_ok (UNIV : list (list Z)) (PCz : Z) (r : int) (st : sstate) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs with
  | Some n, _ :: _ :: _ :: rest =>
      match CtrA.nonstack_windows n rest with
      | Some wl =>
          existsb (zlist_eqb [PCz]) UNIV && s0_far st wl &&
          match unw_walk 32%nat st hargs wl PCz (getr st X2) (getr st X8) 28%nat with
          | Some cands => forallb (fun tr => Nat.leb (length tr) 28%nat && existsb (zlist_eqb (PCz :: to_Z r :: tr)) UNIV) cands
          | None => false
          end
      | None => false
      end
  | _, _ => false
  end.

Definition ret_ok (PCz : Z) (r : int) : bool := PrimInt63.leb 4096%uint63 r && negb (Z.eqb (to_Z r) PCz).

Definition sp_ok (st : sstate) : bool :=
  match getr st X2 with
  | VP k off => PrimInt63.eqb k STACK_ID && PrimInt63.eqb (PrimInt63.land (wl off) 15%uint63) 0%uint63
  | _ => false
  end.

Definition PRIST_BASEw : w64 := wlit 211106232532992%uint63.
Definition win_not_prist (fs : list fact) (l sz kd : sv) : bool :=
  match kd with
  | VL k0 =>
      if weqb k0 wzero then
        match sz with
        | VL z => if weqb z wzero then
                    match l with
                    | VL a => negb (weqb a PRIST_BASEw)
                    | _ => KnownT.KnownT.known_ltu_t fs l (VL PRIST_BASEw) || KnownT.KnownT.known_ltu_t fs (VL PRIST_BASEw) l
                    end
                  else true
        | _ => false
        end
      else true
  | _ => false
  end.
Fixpoint wins_not_prist (fs : list fact) (n : nat) (ws : list sv) : bool :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' => win_not_prist fs l sz kd && wins_not_prist fs n' ws'
  | O, _ => true
  | _, _ => false
  end.
Definition prist_absent (fs : list fact) (hargs : list sv) : bool :=
  match heap_nwin hargs, hargs with
  | Some n, _ :: _ :: _ :: rest => wins_not_prist fs n rest
  | _, _ => false
  end.

Definition sec_decided (fs : list fact) (n : sv) : bool := KnownT.KnownT.known_ltu_t fs (VL PRIM_MAXw) n.

Definition AERRNOi : int := 0x60ed9c%uint63.
Definition errno_havoc (st : sstate) : option sstate :=
  match IMap.find 0%uint63 (s_regs st) with
  | Some r0 =>
      if in_priv_b (s_priv st) AERRNOi 4%uint63 then None else
      let (e, st1) := fresh st in
      Some (SS (s_pc st1) (s_rf st1) (s_ff st1) (resv_after_store (s_facts st1) (s_resv st1) (VL (wlit AERRNOi)))
               (IMap.add 0%uint63 (Mem.region_store r0 AERRNOi 4%uint63 (VP e wzero)) (s_regs st1))
               (s_facts st1) (s_ops st1) (s_priv st1) (s_next st1))
  | None => None
  end.
Definition null_post (hargs : list sv) (cred : sv) (st2 : sstate) (r : int) : option sstate :=
  match errno_havoc (setr st2 X10 (VL wzero)), heap_set_A hargs (sv_alu ALU_SUB cred (VL C_EXHw)) with
  | Some stE, Some hN => Some (setpc (set_ops stE (set_op HEAP_ID hN (s_ops stE))) r)
  | _, _ => None
  end.

Definition AMALLOC_ROOM : int := 12288%uint63.

Definition amalloc_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st) with
  | Some r, VL tp, Some hargs =>
      match heap_A hargs with
      | Some cred =>
          let fs := s_facts st in let n := getr st X10 in
          if weqb tp (wlit ATPi) &&& stack_room_g st AMALLOC_ROOM &&& sp_floor_ok st hargs &&& unw_ok UNIV PCz r st hargs
             &&& sp_top_ok st &&& ret_ok PCz r
             &&& KnownT.KnownT.known_ltu_t fs (VL wzero) n &&& KnownT.KnownT.known_leu_t fs n (VL AREQMAXw)
             &&& cred_pre fs n cred
             &&& (sec_decided fs n ||| prist_absent fs hargs)
             &&& twins_intact st hargs &&& regions_client st hargs
          then
            match forget_stack_below_sp_g st with
            | Some st1 =>
                let st2 := clobber st1 in
                match null_post hargs cred st2 r with
                | None => None
                | Some stN =>
                let (k, st3) := fresh st2 in
                let (sh, st4) := fresh st3 in
                match heap_set_A hargs (cred_post fs n cred) with
                | Some h1 =>
                    match heap_add_window h1 (VP k wzero) n (VL CtrLib.K_BLOCK) with
                    | Some h2 =>
                        match heap_add_window h2 (VP sh wzero) (twin_len n) (VL K_TWIN) with
                        | Some h3 =>

                            let R' := IMap.add sh (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4)) in
                            let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h3 (s_ops st4)) in
                            let st6 := addfact (addfact (addfact (addfact st5 (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                         (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
                            let stB := setpc (setr st6 X10 (VP k wzero)) r in

                            let (s2, st4b) := fresh st4 in
                            let Rb := IMap.add s2 (tail_region n) (IMap.add sh (twin_main n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4b))) in
                            let st5b := set_ops (setregs st4b Rb) (set_op HEAP_ID h3 (s_ops st4b)) in
                            let st6b := addfact (addfact (addfact (addfact (addfact (addfact st5b (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                         (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))))
                                         (tail_fact s2 sh n)) (FULt (VL wzero) n) in
                            let stBb := setpc (setr st6b X10 (VP k wzero)) r in
                            Some (if size_shape_ok fs n then [stN; stB]
                                  else [stN; stBb])
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Definition amalloc_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (amalloc_apply UNIV PCz).

Definition ALIGNED_NMAX : int := 4096%uint63.
Definition aligned_size_ok (n : sv) : bool :=
  match n with
  | VL w => negb (wt w) && PrimInt63.leb 16%uint63 (wl w) && PrimInt63.leb (wl w) ALIGNED_NMAX
            && PrimInt63.eqb (PrimInt63.land (wl w) 15%uint63) 0%uint63
  | _ => false
  end.
Definition aaligned_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X4, find_op HEAP_ID (s_ops st), getr st X10 with
  | Some r, VL tp, Some hargs, VL al =>
      match heap_A hargs with
      | Some cred =>
          let fs := s_facts st in let n := getr st X11 in
          if weqb al (wlit 16%uint63) &&& aligned_size_ok n
             &&& weqb tp (wlit ATPi) &&& stack_room_g st AMALLOC_ROOM &&& sp_floor_ok st hargs &&& unw_ok UNIV PCz r st hargs
             &&& sp_top_ok st &&& ret_ok PCz r
             &&& cred_pre fs n cred
             &&& prist_absent fs hargs
             &&& twins_intact st hargs &&& regions_client st hargs
          then
            match forget_stack_below_sp_g st with
            | Some st1 =>
                let st2 := clobber st1 in
                match null_post hargs cred st2 r with
                | None => None
                | Some stN =>
                let (k, st3) := fresh st2 in
                let (sh, st4) := fresh st3 in
                match heap_set_A hargs (cred_post fs n cred) with
                | Some h1 =>
                    match heap_add_window h1 (VP k wzero) n (VL CtrLib.K_BLOCK) with
                    | Some h2 =>
                        match heap_add_window h2 (VP sh wzero) (twin_len n) (VL K_TWIN) with
                        | Some h3 =>
                            let R' := IMap.add sh (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs st4)) in
                            let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h3 (s_ops st4)) in
                            let st6 := addfact (addfact (addfact (addfact st5 (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                         (FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
                            Some [stN; setpc (setr st6 X10 (VP k wzero)) r]
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
                end
            | None => None
            end
          else None
      | None => None
      end
  | _, _, _, _ => None
  end.
Definition aaligned_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (aaligned_apply UNIV PCz).

Fixpoint del_window_k (n : nat) (ws : list sv) (lo : sv) (kd0 : w64) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      if sv_eqb l lo && sv_eqb kd (VL kd0) then Some ws'
      else match del_window_k n' ws' lo kd0 with Some ws'' => Some (l :: sz :: kd :: ws'') | None => None end
  | _, _ => None
  end.
Definition heap_del_window_k (args : list sv) (lo : sv) (kd0 : w64) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match del_window_k n (firstn (3 * n) rest) lo kd0 with
      | Some ws => Some (VL md :: a :: VL (wsub nw wone) :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.

Definition find_twin (fs : list fact) (k : int) : option int :=
  let fix go (l : list fact) : option int :=
    match l with
    | FEq (VP sh o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c3)) (VL sb)) :: l' =>
        if PrimInt63.eqb k k' && weqb o wzero && weqb o' wzero && weqb c3 (wlit 3%uint63) && weqb sb SBw then Some sh else go l'
    | _ :: l' => go l'
    | [] => None
    end in go fs.

Definition acall_pre (room : int) (unw : option (list (list Z) * Z)) (st : sstate)
    : option (int * list sv * list (int * sv * w64) * sstate) :=
  match call_pre st, getr st X4, aheap_windows st with
  | Some r, VL tp, Some (hargs, wl) =>
      if weqb tp (wlit ATPi) &&& stack_room_g st room &&& sp_floor_ok st hargs &&& sp_top_ok st
         &&& match unw with
            | Some (UNIV, PCz) => unw_ok UNIV PCz r st hargs &&& ret_ok PCz r
            | None => true
            end
      then match forget_stack_below_sp_g st with
           | Some st1 => Some (r, hargs, wl, st1)
           | None => None
           end
      else None
  | _, _, _ => None
  end.

Definition aheap_windows_nt (st : sstate) : option (list sv * list (int * sv * w64)) :=
  match find_op HEAP_ID (s_ops st), CtrA.count_op HEAP_ID (s_ops st), IMap.find STACK_ID (s_regs st) with
  | Some hargs, S O, Some r1 =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          if Nat.leb n 255 && stack_window_ok_g n rest (rg_lo r1) then
            match CtrA.nonstack_windows n rest with
            | Some wl => if CtrA.windows_anchored (s_regs st) wl &&& aregions_justified st wl then Some (hargs, wl) else None
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _, _ => None
  end.
Definition acall_pre_nt (room : int) (unw : option (list (list Z) * Z)) (st : sstate)
    : option (int * list sv * list (int * sv * w64) * sstate) :=
  match call_pre st, getr st X4, aheap_windows_nt st with
  | Some r, VL tp, Some (hargs, wl) =>
      if weqb tp (wlit ATPi) &&& stack_room_g st room &&& sp_floor_ok st hargs &&& sp_top_ok st
         &&& match unw with
            | Some (UNIV, PCz) => unw_ok UNIV PCz r st hargs &&& ret_ok PCz r
            | None => true
            end
      then match forget_stack_below_sp_g st with
           | Some st1 => Some (r, hargs, wl, st1)
           | None => None
           end
      else None
  | _, _, _ => None
  end.

Definition afree_ok_k (kdB kdT : w64) (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : bool :=
  let fs := s_facts st in
  match IMap.find kf (s_regs st), CtrA.win_lookup wl kf, CtrA.win_lookup wl sh, block_of_twin fs sh with
  | Some rf, Some (lenf, kdf), Some (_, kdt), Some kb =>
      let full := KnownT.KnownT.known_eq_t fs (rg_hi rf) lenf in
      weqb kdf kdB && weqb kdt kdT && PrimInt63.eqb kb kf
      && PrimInt63.eqb (rg_lo rf) 0%uint63 && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi rf) && known_leu_qt fs (rg_hi rf) lenf
      && forallb (fun t : int * sv * w64 =>
                    let '(k, len, kd) := t in
                    PrimInt63.eqb k kf || PrimInt63.eqb k sh ||

                    if weqb kd K_TWIN
                    then match block_of_twin fs k with Some kb' => negb (PrimInt63.eqb kb' kf) | None => false end
                    else match IMap.find k (s_regs st) with
                         | Some r => PrimInt63.eqb (rg_lo r) 0%uint63 && known_leu_qt fs (rg_hi r) len && KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
                                     && rg_w r && (weqb kd kdB || full)
                         | None => false
                         end) wl
  | _, _, _, _ => false
  end.

Definition afree_ok (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : bool := afree_ok_k CtrLib.K_BLOCK K_TWIN st wl kf sh.

Definition no_views_on (fs : list fact) (R : IMap.t region) (kf sh : int) : bool :=
  IMap.forallb (fun s r =>
     PrimInt63.eqb s sh ||
     match zero_view r, block_of_twin fs s with
     | Some _, Some n => match find_ub_g fs n with
                         | Some (k, _) => match twin_of fs k with Some s' => negb (PrimInt63.eqb s' sh) | None => true end
                         | None => true
                         end
                         && negb (PrimInt63.eqb n kf)
                         && match IMap.find sh R with Some rsh => negb (hi_names rsh n) | None => true end
     | _, _ => true
     end) R.

Fixpoint tail_named (rhs : sv) (s : int) (l : list fact) : bool :=
  match l with
  | FEq (VP s' z) b :: l' => if PrimInt63.eqb s' s && weqb z wzero && sv_eqb b rhs then true else tail_named rhs s l'
  | _ :: l' => tail_named rhs s l'
  | [] => false
  end.
Definition no_tail_at (fs : list fact) (R : IMap.t region) (sh : int) (n : sv) : bool :=
  IMap.forallb (fun s _ => negb (tail_named (tail_rhs sh n) s fs)) R.
Definition twin_canon (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : bool :=
  match IMap.find sh (s_regs st), CtrA.win_lookup wl kf, CtrA.win_lookup wl sh with
  | Some r, Some (n, _), Some (lent, _) =>
      is_twin_region r n &&& size_shape_ok (s_facts st) n &&& len_is_twin (s_facts st) lent n &&& twins_apart (s_facts st) (s_regs st) wl (carg_vecs st) kf sh
      &&& no_tail_at (s_facts st) (s_regs st) sh n
  | _, _, _ => false
  end.

Definition no_tails_on (fs : list fact) (R : IMap.t region) (sh : int) (n : sv) (s2 : int) : bool :=
  IMap.forallb (fun s _ => PrimInt63.eqb s s2 || negb (tail_named (tail_rhs sh n) s fs)) R.
Definition twin_canon_pair (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : option int :=
  match IMap.find sh (s_regs st), CtrA.win_lookup wl kf, CtrA.win_lookup wl sh with
  | Some r, Some (n, _), Some (lent, _) =>
      if is_twin_main r n &&& sv_eqb lent (twin_len n) &&& twins_apart (s_facts st) (s_regs st) wl (carg_vecs st) kf sh then
        match tail_scan (s_facts st) (s_regs st) sh n with
        | Some s2 => if no_tails_on (s_facts st) (s_regs st) sh n s2 && negb (PrimInt63.eqb s2 kf)
                        && (match CtrA.win_lookup wl s2 with None => true | Some _ => false end)
                     then Some s2 else None
        | None => None
        end
      else None
  | _, _, _ => None
  end.

Definition twin_consume (st : sstate) (wl : list (int * sv * w64)) (kf sh : int) : option (option int) :=
  if twin_canon st wl kf sh then Some None
  else match twin_canon_pair st wl kf sh with Some s2 => Some (Some s2) | None => None end.
Definition remove_opt (o : option int) (R : IMap.t region) : IMap.t region := match o with Some s2 => IMap.remove s2 R | None => R end.

Definition twin_shape_ok (st : sstate) (sh : int) (n : sv) : bool :=
  match IMap.find sh (s_regs st) with
  | Some r => (is_twin_region r n &&& size_shape_ok (s_facts st) n)
              ||| (is_twin_main r n &&& match tail_scan (s_facts st) (s_regs st) sh n with Some _ => true | None => false end)
  | None => false
  end.
Definition twin_pat_ok_t (st : sstate) (wl : list (int * sv * w64)) (kb : int) (n : sv) : bool :=
  match twin_of (s_facts st) kb with
  | Some sh => match CtrA.win_lookup wl sh with
               | Some (lent, kd) => weqb kd K_TWIN &&& sv_eqb lent (twin_len n) &&& negb (PrimInt63.eqb sh 0%uint63) &&& twin_shape_ok st sh n
               | None => false
               end
  | None => false
  end.
Definition twin_pat_ok (st : sstate) (wl : list (int * sv * w64)) (kb : int) : bool :=
  match CtrA.win_lookup wl kb with
  | Some (n, kd) => weqb kd CtrLib.K_BLOCK &&& twin_pat_ok_t st wl kb n
  | None => false
  end.

Definition afree_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match acall_pre ASTACK (Some (UNIV, PCz)) st, getr st X10 with
  | Some (r, hargs, wl, st1), VP kf off =>
      match find_twin (s_facts st) kf with
      | Some sh =>
          match twin_consume st wl kf sh with
          | Some tl =>
              if weqb off wzero && afree_ok st wl kf sh && no_views_on (s_facts st) (s_regs st) kf sh then
                match heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK with
                | Some h1 =>
                    match heap_del_window_k h1 (VP sh wzero) K_TWIN with
                    | Some h2 =>
                        let st2 := clobber st1 in
                        let (x, st3) := fresh st2 in
                        let R' := remove_opt tl (IMap.remove sh (IMap.remove kf (s_regs st3))) in
                        Some [setpc (setr (set_ops (setregs st3 R') (set_op HEAP_ID h2 (s_ops st3))) X10 (VP x wzero)) r]
                    | None => None
                    end
                | None => None
                end
              else None
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.
Definition afree_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (afree_apply UNIV PCz).

Definition afree0_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match acall_pre ASTACK (Some (UNIV, PCz)) st, getr st X10 with
  | Some (r, hargs, wl, st1), VL w =>
      if weqb w wzero then
        let st2 := clobber st1 in
        let (x, st3) := fresh st2 in
        Some [setpc (setr st3 X10 (VP x wzero)) r]
      else None
  | _, _ => None
  end.
Definition afree0_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (afree0_apply UNIV PCz).

Inductive twsel : Type := TwReg (rs : r5) (off : w64) | TwLen (n : w64).
Definition fact_on (sh : int) (f : fact) : bool :=
  match f with
  | FEq (VP s _) _ => PrimInt63.eqb s sh
  | FRange s _ _ => PrimInt63.eqb s sh
  | FAlign s _ => PrimInt63.eqb s sh
  | _ => false
  end.
Definition drop_anchor_facts (sh : int) (fs : list fact) : list fact := List.filter (fun f => negb (fact_on sh f)) fs.
Definition set_facts (st : sstate) (fs : list fact) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) fs (s_ops st) (s_priv st) (s_next st).

Definition tw_out (fs : list fact) (wl : list (int * sv * w64)) (k : int) : option (int * int) :=
  match find_twin fs k with
  | Some sh => match CtrA.win_lookup wl sh with Some _ => Some (k, sh) | None => None end
  | None => None
  end.
Fixpoint twlen_go (fs : list fact) (wl : list (int * sv * w64)) (n : w64) (l : list (int * sv * w64)) : option (int * int) :=
  match l with
  | (k, VL len, kd) :: l' => if weqb kd CtrLib.K_BLOCK && weqb len n then match tw_out fs wl k with Some p => Some p | None => twlen_go fs wl n l' end
                             else twlen_go fs wl n l'
  | _ :: l' => twlen_go fs wl n l'
  | [] => None
  end.
Definition twsel_pair (sel : twsel) (st : sstate) (wl : list (int * sv * w64)) : option (int * int) :=
  match sel with
  | TwReg rs off => match getr st rs with
                    | VP k o => if weqb o off then tw_out (s_facts st) wl k else None
                    | _ => None
                    end
  | TwLen n => twlen_go (s_facts st) wl n wl
  end.
Definition twin_in_apply (sel : twsel) (st : sstate) : option (list sstate) :=
  match aheap_windows st with
  | Some (hargs, wl) =>
      match twsel_pair sel st wl with
      | None => Some [st]
      | Some (kf, sh) =>
          if (match s_resv st with RNone => true | _ => false end) && fresh_ok st
             && stack_room_g st 0%uint63 && sp_floor_ok st hargs
             && afree_ok st wl kf sh && twin_canon st wl kf sh && no_views_on (s_facts st) (s_regs st) kf sh then
            match heap_del_window_k hargs (VP sh wzero) K_TWIN with
            | Some h1 => Some [set_facts (set_ops (setregs st (IMap.remove sh (s_regs st))) (set_op HEAP_ID h1 (s_ops st)))
                                         (drop_anchor_facts sh (s_facts st))]
            | None => None
            end
          else None
      end
  | None => None
  end.
Definition twin_in_c (pc : int) (sel : twsel) : contract := Contract pc (twin_in_apply sel).

Definition blk_reg_ok (fs : list fact) (R : IMap.t region) (k : int) : bool :=
  match IMap.find k R with
  | Some r => rg_w r &&& PrimInt63.eqb (rg_lo r) 0%uint63 &&& KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi r)
  | None => false
  end.
Definition tw_other_ok (fs : list fact) (R : IMap.t region) (wl : list (int * sv * w64)) (cv : list int) (kf : int) (full : bool)
    (e : int * sv * w64) : bool :=
  let '(k, len, kd) := e in
  if weqb kd K_TWIN then
    match block_of_twin fs k with
    | Some kb => negb (PrimInt63.eqb kb kf)
                 &&& ((match CtrA.win_lookup wl kb with Some (_, kdb) => weqb kdb CtrLib.K_BLOCK | None => false end &&& blk_reg_ok fs R kb)
                      ||| (full &&& twin_arm_evx fs R wl cv k len kf))
    | None => false
    end
  else true.
Fixpoint twlen_in_go (fs : list fact) (wl : list (int * sv * w64)) (n : w64) (l : list (int * sv * w64)) : option int :=
  match l with
  | (k, VL len, kd) :: l' => if weqb kd CtrLib.K_BLOCK && weqb len n
                             then match tw_out fs wl k with Some _ => twlen_in_go fs wl n l' | None => Some k end
                             else twlen_in_go fs wl n l'
  | _ :: l' => twlen_in_go fs wl n l'
  | [] => None
  end.
Definition twsel_blk (sel : twsel) (st : sstate) (wl : list (int * sv * w64)) : option int :=
  match sel with
  | TwReg rs off => match getr st rs with
                    | VP k o => if weqb o off then Some k else None
                    | _ => None
                    end
  | TwLen n => twlen_in_go (s_facts st) wl n wl
  end.
Definition link_fact (sh k : int) : fact :=
  FEq (VP sh wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw)).
Definition twin_out_apply (sel : twsel) (st : sstate) : option (list sstate) :=
  match aheap_windows st with
  | Some (hargs, wl) =>
      match twsel_blk sel st wl with
      | None => Some [st]
      | Some kf =>
          match tw_out (s_facts st) wl kf with
          | Some _ => Some [st]
          | None =>
              match CtrA.win_lookup wl kf, IMap.find kf (s_regs st) with
              | Some (n, kd), Some rf =>
                  let fs := s_facts st in
                  if (match s_resv st with RNone => true | _ => false end) &&& fresh_ok st
                     &&& stack_room_g st 0%uint63 &&& sp_floor_ok st hargs
                     &&& weqb kd CtrLib.K_BLOCK &&& (match find_twin fs kf with None => true | Some _ => false end)
                     &&& rg_w rf &&& PrimInt63.eqb (rg_lo rf) 0%uint63 &&& KnownT.KnownT.known_ltu_t fs (VL wzero) (rg_hi rf)
                     &&& size_shape_ok fs n
                     &&& forallb (tw_other_ok fs (s_regs st) wl (carg_vecs st) kf (KnownT.KnownT.known_eq_t fs (rg_hi rf) n)) wl
                  then
                    let (sh, st1) := fresh st in
                    match heap_add_window hargs (VP sh wzero) (twin_len n) (VL K_TWIN) with
                    | Some h1 =>
                        Some [addfact (set_ops (setregs st1 (IMap.add sh (twin_region n) (s_regs st1))) (set_op HEAP_ID h1 (s_ops st1)))
                                      (link_fact sh kf)]
                    | None => None
                    end
                  else None
              | _, _ => None
              end
          end
      end
  | None => None
  end.
Definition twin_out_c (pc : int) (sel : twsel) : contract := Contract pc (twin_out_apply sel).

Definition B61w : w64 := wlit 0x2000000000000000%uint63.
Definition AREQMAX4w : w64 := wlit 0x3FFC00000%uint63.

Definition tier1 {A} (fs : list fact) (vs : list int) (q : list fact -> option A) : option A := q (rel_facts vs fs).
Definition tiers12 {A} (fs : list fact) (vs : list int) (q : list fact -> option A) : option A :=
  match q (rel_facts vs fs) with Some r => Some r | None => q (rel_facts (close_vs fs vs vs) fs) end.
Definition known_ltu_t1 (fs : list fact) (a b : sv) : bool := Step.dec_true (tier1 fs (sv_vs a (sv_vs b [])) (fun l => decide_ltu l a b)).
Definition known_leu_t1 (fs : list fact) (a b : sv) : bool := Step.dec_false (tier1 fs (sv_vs b (sv_vs a [])) (fun l => decide_ltu l b a)).
Definition known_leu_t12 (fs : list fact) (a b : sv) : bool := Step.dec_false (tiers12 fs (sv_vs b (sv_vs a [])) (fun l => decide_ltu l b a)).
Definition reqmax_x4 (fs : list fact) (n : sv) : bool :=
  KnownT.KnownT.known_ltu_t fs n (VL B61w) &&& KnownT.KnownT.known_leu_t fs (VAlu ALU_SLL n (VL (wlit 2%uint63))) (VL AREQMAX4w).
Definition reqmax_x4_t1 (fs : list fact) (n : sv) : bool :=
  known_ltu_t1 fs n (VL B61w) &&& known_leu_t1 fs (VAlu ALU_SLL n (VL (wlit 2%uint63))) (VL AREQMAX4w).

Definition reqmax_ok_spec (fs : list fact) (n : sv) : bool :=
  KnownT.KnownT.known_leu_t fs n (VL AREQMAXw) ||| reqmax_x4 fs n.
Definition reqmax_ok (fs : list fact) (n : sv) : bool :=
  reqmax_x4_t1 fs n ||| known_leu_t12 fs n (VL AREQMAXw) ||| reqmax_x4 fs n ||| KnownT.KnownT.known_leu_t fs n (VL AREQMAXw).
Definition AREALLOC_ROOM : int := 12288%uint63.
Definition arealloc_apply (UNIV : list (list Z)) (PCz : Z) (st : sstate) : option (list sstate) :=
  match acall_pre AREALLOC_ROOM (Some (UNIV, PCz)) st, getr st X10 with
  | Some (r, hargs, wl, st1), VP kf off =>
      match find_twin (s_facts st) kf, heap_A hargs with
      | Some sh, Some cred =>
          let fs := s_facts st in let n := getr st X11 in
          if weqb off wzero && afree_ok st wl kf sh && twin_canon st wl kf sh && no_views_on fs (s_regs st) kf sh
             && KnownT.KnownT.known_ltu_t fs (VL wzero) n && reqmax_ok fs n && size_shape_ok fs n && cred_pre fs n cred
             && prist_absent fs hargs
          then
            let st2 := clobber st1 in
            match null_post hargs cred st2 r with
            | None => None
            | Some stN =>
            match heap_del_window_k hargs (VP kf wzero) CtrLib.K_BLOCK with
            | Some h1 =>
                match heap_del_window_k h1 (VP sh wzero) K_TWIN with
                | Some h2 =>
                    let (k, st3) := fresh st2 in
                    let (sh', st4) := fresh st3 in
                    match heap_set_A h2 (cred_post fs n cred) with
                    | Some h3 =>
                        match heap_add_window h3 (VP k wzero) n (VL CtrLib.K_BLOCK) with
                        | Some h4 =>
                            match heap_add_window h4 (VP sh' wzero) (twin_len n) (VL K_TWIN) with
                            | Some h5 =>
                                let R' := IMap.add sh' (twin_region n) (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty)
                                            (IMap.remove sh (IMap.remove kf (s_regs st4)))) in
                                let st5 := set_ops (setregs st4 R') (set_op HEAP_ID h5 (s_ops st4)) in
                                let st6 := addfact (addfact (addfact (addfact st5 (cred_fact fs n cred)) (FRange k BLK_LO BLK_HI)) (FAlign k 4%uint63))
                                             (FEq (VP sh' wzero) (VAlu ALU_ADD (VAlu ALU_SRL (VP k wzero) (VL (wlit 3%uint63))) (VL SBw))) in
                                let st7 := addfacts st6 (and7_facts n) in
                                Some [stN; setpc (setr st7 X10 (VP k wzero)) r]
                            | None => None
                            end
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Definition arealloc_c (UNIV : list (list Z)) (PCz : Z) (pc : int) : contract := Contract pc (arealloc_apply UNIV PCz).

Definition vec_hi (n : int) (oA : w64) (k : int) : sv := VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k wzero)) (VL (wlit 3%uint63)).

Definition hi_mid (k : int) (h : sv) : option sv :=
  match h with
  | VL g => if negb (wt g) && PrimInt63.ltb (wl g) 288230376151711744%uint63
            then Some (VP k (wlit (PrimInt63.lsl (wl g) 3%uint63))) else None
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k' z)) (VL c) =>
      if PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63) then Some (VP n oA) else None
  | _ => None
  end.

Definition mid_hi (fs : list fact) (k : int) (mid : sv) : option sv :=
  match mid with
  | VP n o =>
      if PrimInt63.eqb n k then (if al8 o then Some (VL (wlit (PrimInt63.lsr (wl o) 3%uint63))) else None)
      else match find_lb_to fs n k with
           | Some o2 =>
               if al8 o && al8 o2 && PrimInt63.leb 3%uint63 (find_align fs n) && nowrap_kb fs n o && nowrap_kb fs k o2
               then Some (vec_hi n o k) else None
           | None => None
           end
  | VAlu ALU_ADD (VP k' z) xs =>
      if PrimInt63.eqb k' k && weqb z wzero && div8x fs xs && KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) && nowrap_kb fs k SYMCAPw
      then Some (twin_len xs) else None
  | _ => None
  end.
Definition annot_tails_ok (st : sstate) (wnl : list (int * sv * w64)) (k sh : int) : bool :=
  match CtrA.win_lookup wnl k with
  | Some (n, _) => IMap.forallb (fun s _ => negb (tail_named (tail_rhs sh n) s (s_facts st))) (s_regs st)
  | None => true
  end.

Definition blk_win_pos (st : sstate) (wnl : list (int * sv * w64)) (x : int) : bool :=
  match CtrA.win_lookup wnl x with
  | Some (n, kd) => weqb kd CtrLib.K_BLOCK &&& KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) n
  | None => false
  end.
Definition blk_reg_w (st : sstate) (x : int) : bool :=
  match IMap.find x (s_regs st) with
  | Some r => rg_w r &&& PrimInt63.eqb (rg_lo r) 0%uint63 &&& KnownT.KnownT.known_ltu_t (s_facts st) (VL wzero) (rg_hi r)
  | None => false
  end.
Definition annot_other_ok (st : sstate) (wnl : list (int * sv * w64)) (cv : list int) (k sh : int) (len : sv) (e : int * sv * w64) : bool :=
  let '(k0, len0, kd0) := e in
  PrimInt63.eqb k0 sh |||
  (if weqb kd0 K_TWIN then
     (match len0, len with VL l0, VL wlen => negb (weqb l0 wlen) | _, _ => false end)
     ||| match block_of_twin (s_facts st) k0 with
         | Some k2 =>
             negb (PrimInt63.eqb k2 k) &&& PrimInt63.leb 3%uint63 (find_align (s_facts st) k2)
             &&& ((existsb (PrimInt63.eqb k) cv &&& existsb (PrimInt63.eqb k2) cv)
                  ||| (existsb (PrimInt63.eqb k) cv &&& blk_win_pos st wnl k2)
                  ||| (blk_win_pos st wnl k &&& existsb (PrimInt63.eqb k2) cv)
                  ||| (blk_reg_w st k &&& blk_reg_w st k2))
         | None => false
         end
   else negb (wt kd0) &&& PrimInt63.leb (wl kd0) 8%uint63).
Definition annot_others_ok (st : sstate) (wnl : list (int * sv * w64)) (k sh : int) (len : sv) : bool :=
  let cv := carg_vecs st in forallb (annot_other_ok st wnl cv k sh len) wnl.

Definition annot_end_ok (fs : list fact) (k : int) (len x11 : sv) : bool :=
  match len with
  | VL wlen => negb (wt wlen) &&& KnownT.KnownT.known_leu_t fs x11 (VP k (wlit (PrimInt63.lsl (wl wlen) 3%uint63)))
  | _ => match tie_of fs len with
         | Some xs => (sv_eqb x11 (VAlu ALU_ADD (VP k wzero) xs) ||| has_fact (FULe x11 (VAlu ALU_ADD (VP k wzero) xs)) fs)
                      &&& KnownT.KnownT.known_leu_t fs xs (VL SYMCAPw) &&& nowrap_kb fs k SYMCAPw
         | None => false
         end
  end.
Definition ANNOT_ROOM : int := 4096%uint63.
Definition ANNOT_WMAX : int := 8064%uint63.
Definition annotate_apply (st : sstate) : option (list sstate) :=
  match acall_pre ANNOT_ROOM None st, getr st X10 with
  | Some (r, hargs, wnl, st1), VP k zb =>
      let fs := s_facts st in
      match find_twin fs k with
      | Some sh =>
          match IMap.find sh (s_regs st), CtrA.win_lookup wnl sh with
          | Some rsh, Some (len, kd) =>
              match hi_mid k (rg_hi rsh), mid_hi fs k (getr st X13) with
              | Some om, Some h' =>
                  if weqb zb wzero &&& weqb kd K_TWIN &&& negb (PrimInt63.eqb sh 0%uint63)
                     &&& PrimInt63.leb 3%uint63 (find_align fs k)
                     &&& (match block_of_twin fs sh with Some kb => PrimInt63.eqb kb k | None => false end)
                     &&& twin_small fs len
                     &&& negb (rg_w rsh) &&& PrimInt63.eqb (rg_lo rsh) 0%uint63
                     &&& (match rg_cells rsh, rg_bg rsh with IMap.Leaf, BGZero => true | _, _ => false end)
                     &&& (match mid_hi fs k om with Some hO => sv_eqb hO (rg_hi rsh) | None => false end)
                     &&& KnownT.KnownT.known_eq_t fs (getr st X12) om
                     &&& KnownT.KnownT.known_leu_t fs (getr st X13) (getr st X11)
                     &&& KnownT.KnownT.known_leu_t fs (getr st X12) (getr st X11)
                     &&& al8_sv fs (getr st X11)
                     &&& annot_end_ok fs k len (getr st X11)
                     &&& no_views_on fs (s_regs st) k sh
                     &&& annot_tails_ok st wnl k sh
                     &&& annot_others_ok st wnl k sh len
                  then
                    let rsh' := Region 0%uint63 h' false BGZero IMap.empty in
                    let st2 := setregs (clobber st1) (IMap.add sh rsh' (IMap.remove sh (s_regs st1))) in
                    let (v, st3) := fresh st2 in Some [setpc (setr st3 X10 (VP v wzero)) r]
                  else None
              | _, _ => None
              end
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.
Definition annotate_c (pc : int) : contract := Contract pc annotate_apply.
End ActrA.
End TwinB.
