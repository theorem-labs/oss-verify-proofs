(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrA.
Section WithImg.
Variable segs : list Segment.

Variables (ERRNO LIBC GOT GUARD TP : int) (CANARY : sv).

Definition STACK_ID : int := 1%uint63.
Definition AUXV_ID : int := 3%uint63.
Definition RND_ID : int := 6%uint63.

Definition ALLOC_STACK : int := 8192%uint63.
Definition ALIGNED_STACK : int := 8224%uint63.
Definition REALLOC_STACK : int := 8256%uint63.

Definition LIBC_GRANS : nat := 14%nat.

Definition aload (st : sstate) (a : int) (w : int) : option sv :=
  match do_load segs st (VL (wlit a)) w false with inl (Some v) => Some v | _ => None end.

Definition is_litv (v : option sv) (x : int) : bool :=
  match v with Some (VL w) => weqb w (wlit x) | _ => false end.
Definition is_sv (v : option sv) (x : sv) : bool :=
  match v with Some u => sv_eqb u x | _ => false end.

Definition statics_ok (st : sstate) : bool :=
  is_litv (aload st (PrimInt63.add LIBC 3%uint63) 1%uint63) 0%uint63
  && is_litv (aload st (PrimInt63.add LIBC 48%uint63) 8%uint63) 4096%uint63
  && is_sv (aload st (PrimInt63.add LIBC 8%uint63) 8%uint63) (VP AUXV_ID wzero)
  && is_litv (aload st GOT 8%uint63) GUARD
  && is_sv (aload st GUARD 8%uint63) CANARY
  && match aload st ERRNO 4%uint63 with Some _ => true | None => false end.

Definition stack_ok (st : sstate) (need : int) : option (int * int) :=
  match getr st X2, IMap.find STACK_ID (s_regs st) with
  | VP k off, Some r =>
      if negb (PrimInt63.eqb k STACK_ID) || negb (rg_w r) || negb (match rg_bg r with BGNone => true | _ => false end)
      then None else
      match okey off, okey (wsub off (wlit need)), rg_hi r with
      | Some ksp, Some klo, VL h =>
          match okey h with
          | Some kh => if kleb (rg_lo r) klo && kleb ksp kh && PrimInt63.eqb (PrimInt63.land ksp 15%uint63) 0%uint63
                          && PrimInt63.leb bit62i ksp
                       then Some (ksp, rg_lo r) else None
          | None => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.

Definition rload (st : sstate) (k : int) (off : int) (w : int) : option sv :=
  match do_load segs st (VP k (wlit off)) w false with inl (Some v) => Some v | _ => None end.
Definition AUXV_KEYS : list int := [3; 4; 5; 16; 6; 11; 12; 23; 25; 0]%uint63.
Fixpoint auxv_keys_ok (st : sstate) (ks : list int) (off : int) : bool :=
  match ks with
  | [] => true
  | k :: ks' => is_litv (rload st AUXV_ID off 8%uint63) k
                && match rload st AUXV_ID (PrimInt63.add off 8%uint63) 8%uint63 with Some _ => true | None => false end
                && auxv_keys_ok st ks' (PrimInt63.add off 16%uint63)
  end.

Definition rnd_region_ok (st : sstate) : bool :=
  match IMap.find RND_ID (s_regs st) with
  | Some r => match rg_cells r, rg_bg r with
              | IMap.Leaf, BGBlob j sh => PrimInt63.eqb j RND_ID && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo r) 0%uint63
                                         && match rload st RND_ID 8%uint63 8%uint63 with Some _ => true | None => false end
              | _, _ => false
              end
  | None => false
  end.
Definition auxv_ok (st : sstate) : bool :=
  auxv_keys_ok st AUXV_KEYS 0%uint63
  && is_sv (rload st AUXV_ID 136%uint63 8%uint63) (VP RND_ID wzero)
  && is_litv (rload st AUXV_ID 152%uint63 8%uint63) 0%uint63
  && rnd_region_ok st.

Definition sp_below_anchor (fs : list fact) (sp : sv) : bool := known_leu fs sp (VP STACK_ID wzero).

Definition anchored_above (fs : list fact) (k : int) : bool :=
  existsb (fun f => match f with
                    | FEq (VP k' z) (VP s o) =>
                        if PrimInt63.eqb k' k then weqb z wzero && PrimInt63.eqb s STACK_ID && negb (wt o) && nowrap_k fs STACK_ID o else false
                    | _ => false
                    end) fs.
Definition stack_side (fs : list fact) (sp : sv) (spok : bool) (k : int) : bool :=
  if (if spok then (if anchored_above fs k then true else known_leu fs (VP STACK_ID wzero) (VP k wzero)) else false) then true
  else known_leu fs sp (VP k wzero).
Definition above_stack_ok (st : sstate) : bool :=
  let fs := s_facts st in let sp := getr st X2 in
  let spok := sp_below_anchor fs sp in
  if stack_side fs sp spok AUXV_ID then stack_side fs sp spok RND_ID else false.

Fixpoint stack_window_ok (n : nat) (ws : list sv) (klo : int) : bool :=
  match n, ws with
  | S n', VP k wlo :: _ :: VL kd :: ws' =>
      (PrimInt63.eqb k STACK_ID && weqb kd wzero && match okey wlo with Some kw => PrimInt63.eqb kw klo | None => false end)
      || stack_window_ok n' ws' klo
  | S n', _ :: _ :: _ :: ws' => stack_window_ok n' ws' klo
  | _, _ => false
  end.

Fixpoint nonstack_windows (n : nat) (ws : list sv) : option (list (int * sv * w64)) :=
  match n, ws with
  | O, _ => Some []
  | S n', lo :: len :: VL kd :: ws' =>
      match nonstack_windows n' ws' with
      | Some l =>
          if weqb kd wzero then Some l
          else match lo with
               | VP k o => if weqb o wzero && negb (PrimInt63.eqb k 0%uint63) && negb (PrimInt63.eqb k STACK_ID)
                           then Some ((k, len, kd) :: l) else None
               | _ => None
               end
      | None => None
      end
  | _, _ => None
  end.

Fixpoint win_lookup (wl : list (int * sv * w64)) (k : int) : option (sv * w64) :=
  match wl with
  | [] => None
  | (k', len, kd) :: wl' => if PrimInt63.eqb k' k then Some (len, kd) else win_lookup wl' k
  end.

Fixpoint windows_anchored (R : IMap.t region) (wl : list (int * sv * w64)) : bool :=
  match wl with
  | [] => true
  | (k, _, _) :: wl' =>
      match IMap.find k R, win_lookup wl' k with
      | Some _, None => windows_anchored R wl'
      | _, _ => false
      end
  end.

Definition known_leu_q (fs : list fact) (a b : sv) : bool :=
  if sv_eqb a b then true else
  if fact_lookup fs (is_FULe a b) then true else
  if fact_lookup fs (is_FULt a b) then true else known_leu fs a b.
Definition region_justified (fs : list fact) (sp : sv) (spok : bool) (wl : list (int * sv * w64)) (k : int) (r : region) : bool :=
  if PrimInt63.eqb k 0%uint63 then true else
  if PrimInt63.eqb k STACK_ID then true else
  if PrimInt63.eqb (rg_lo r) 0%uint63 then
    match win_lookup wl k with
    | Some (len, _) => if known_leu_q fs (rg_hi r) len then true else stack_side fs sp spok k
    | None => stack_side fs sp spok k
    end
  else false.
Definition regions_justified (st : sstate) (wl : list (int * sv * w64)) : bool :=
  let fs := s_facts st in let sp := getr st X2 in
  let spok := sp_below_anchor fs sp in
  IMap.forallb (region_justified fs sp spok wl) (s_regs st).

Fixpoint count_op (id : int) (os : list opinst) : nat :=
  match os with
  | [] => O
  | o :: os' => if PrimInt63.eqb (op_id o) id then S (count_op id os') else count_op id os'
  end.

Definition heap_windows (st : sstate) (klo1 : int) : option (list sv * list (int * sv * w64)) :=
  match find_op HEAP_ID (s_ops st), count_op HEAP_ID (s_ops st) with
  | Some hargs, S O =>
      match heap_nwin hargs, hargs with
      | Some n, _ :: _ :: _ :: rest =>
          if Nat.leb n 255 && stack_window_ok n rest klo1 then
            match nonstack_windows n rest with
            | Some wl => if windows_anchored (s_regs st) wl && regions_justified st wl then Some (hargs, wl) else None
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

Definition alloc_call (need : int) (st : sstate) : option (int * int * list sv * list (int * sv * w64)) :=
  match s_resv st, call_pre st, getr st X1, getr st X4, stack_ok st need with
  | RNone, Some r, VL ra, VL tp, Some (ksp, klo1) =>
      if weqb tp (wlit TP) && PrimInt63.eqb (PrimInt63.land (wl ra) 1%uint63) 0%uint63
         && statics_ok st && auxv_ok st && above_stack_ok st && PrimInt63.ltb r bit62i
      then match heap_windows st klo1 with
           | Some (hargs, wl) => Some (r, ksp, hargs, wl)
           | None => None
           end
      else None
  | _, _, _, _, _ => None
  end.

Definition free_ok (st : sstate) (wl : list (int * sv * w64)) (kf : int) : option sv :=
  let fs := s_facts st in
  match IMap.find kf (s_regs st), win_lookup wl kf with
  | Some rf, Some (lenf, kdf) =>
      if negb (weqb kdf K_BLOCK) || negb (PrimInt63.eqb (rg_lo rf) 0%uint63)
         || negb (known_ltu fs (VL wzero) (rg_hi rf)) || negb (known_leu_q fs (rg_hi rf) lenf) then None else
      let full := known_eq fs (rg_hi rf) lenf in

      let other_block := existsb (fun t : int * sv * w64 => let '(k, len, kd) := t in negb (PrimInt63.eqb k kf) && weqb kd K_BLOCK) wl in
      if forallb (fun t : int * sv * w64 =>
                    let '(k, len, kd) := t in
                    PrimInt63.eqb k kf ||
                    match IMap.find k (s_regs st) with
                    | Some r => PrimInt63.eqb (rg_lo r) 0%uint63
                                && known_leu_q fs (rg_hi r) len && (rg_w rf || rg_w r) && (weqb kd K_BLOCK || full)
                                && (if known_ltu fs (VL wzero) (rg_hi r) then true
                                    else (negb (weqb kd K_BLOCK) && known_eq fs (rg_hi r) len && other_block))
                    | None => false
                    end) wl
      then Some lenf else None
  | _, _ => None
  end.

Definition forget_r1 (r1 : region) (ksp : int) : region :=
  Mem.region_forget r1 (granule (rg_lo r1)) (granule ksp).

Definition dirty_r0 (r0 : region) : region :=
  Region (rg_lo r0) (rg_hi r0) (rg_w r0) (rg_bg r0) (Mem.dirty_range (granule LIBC) LIBC_GRANS (rg_cells r0)).
Definition store_pubs (q : region) : region :=
  Mem.region_store
    (Mem.region_store
       (Mem.region_store
          (Mem.region_store (Mem.region_store q (PrimInt63.add LIBC 3%uint63) 1%uint63 (VL wzero))
             (PrimInt63.add LIBC 8%uint63) 8%uint63 (VP AUXV_ID wzero))
          (PrimInt63.add LIBC 48%uint63) 8%uint63 (VL (wlit 4096%uint63)))
       GOT 8%uint63 (VL (wlit GUARD)))
    GUARD 8%uint63 CANARY.
Definition havoc_r0 (r0 : region) (e : int) : region :=
  store_pubs (Mem.region_store (dirty_r0 r0) ERRNO 4%uint63 (VP e wzero)).

Definition alloc_post_mk (st : sstate) (r ksp : int) (r0 r1 : region) : sstate :=
  SS r (s_rf (clobber st)) (s_ff st) (s_resv st)
     (IMap.add 0%uint63 (havoc_r0 r0 (PrimInt63.add (s_next st) 15%uint63))
        (IMap.add STACK_ID (forget_r1 r1 ksp) (s_regs st)))
     (s_facts st) (s_ops st) (s_priv st) (PrimInt63.add (s_next st) 16%uint63).

Definition alloc_post (st : sstate) (r ksp : int) : option sstate :=
  match IMap.find STACK_ID (s_regs st), IMap.find 0%uint63 (s_regs st) with
  | Some r1, Some r0 => Some (alloc_post_mk st r ksp r0 r1)
  | _, _ => None
  end.

Definition heap_drop_A (hargs : list sv) : option (list sv) := heap_set_A hargs (VL wones).

Definition two32 : w64 := wlit 4294967296%uint63.
Definition size_lim : w64 := wlit 281474976710656%uint63.
Definition two47 : w64 := wlit 140737488355328%uint63.
Definition BLK_LO : w64 := wlit 4096%uint63.
Definition BLK_HI : w64 := wlit 140737488355327%uint63.

Definition size_ok (fs : list fact) (sz : sv) : bool :=
  known_ltu fs (VL wzero) sz && known_ltu fs sz (VL size_lim).

Definition size_ok32 (fs : list fact) (sz : sv) : bool :=
  known_ltu fs (VL wzero) sz && known_ltu fs sz (VL two32).

Definition block_post (stA0 : sstate) (hargsB : list sv) (n : sv) (rg : w64 * w64) : option sstate :=
  let (k, stB0) := fresh stA0 in
  match heap_add_window hargsB (VP k wzero) n (VL K_BLOCK) with
  | Some hargs' =>
      let stB1 := setregs stB0 (IMap.add k (Region 0%uint63 n true BGUnk IMap.empty) (s_regs stB0)) in
      let stB2 := set_ops stB1 (set_op HEAP_ID hargs' (s_ops stB1)) in
      let stB3 := addfact (addfact (addfact stB2 (FRange k (fst rg) (snd rg))) (FAlign k 4%uint63)) (FULt n (VL two47)) in
      Some (setr stB3 X10 (VP k wzero))
  | None => None
  end.
Fixpoint block_posts (stA0 : sstate) (hargsB : list sv) (n : sv) (rgs : list (w64 * w64)) : option (list sstate) :=
  match rgs with
  | [] => Some []
  | rg :: rgs' =>
      match block_post stA0 hargsB n rg, block_posts stA0 hargsB n rgs' with
      | Some stB, Some sts => Some (stB :: sts)
      | _, _ => None
      end
  end.
Definition malloc_posts_rg (st : sstate) (r ksp : int) (hargsN hargsB : list sv) (n : sv) (rgs : list (w64 * w64))
  : option (list sstate) :=
  match alloc_post st r ksp with
  | Some stA0 =>
      let stA := setr (set_ops stA0 (set_op HEAP_ID hargsN (s_ops stA0))) X10 (VL wzero) in
      match block_posts stA0 hargsB n rgs with
      | Some sts => Some (stA :: sts)
      | None => None
      end
  | None => None
  end.
Definition malloc_posts (st : sstate) (r ksp : int) (hargsN hargsB : list sv) (n : sv) : option (list sstate) :=
  malloc_posts_rg st r ksp hargsN hargsB n [(BLK_LO, BLK_HI)].

Definition malloc_s_apply (st : sstate) : option (list sstate) :=
  match alloc_call ALLOC_STACK st with
  | Some (r, ksp, hargs0, _) =>
      match heap_drop_A hargs0 with
      | Some hargs => let n := getr st X10 in if size_ok (s_facts st) n then malloc_posts st r ksp hargs hargs n else None
      | None => None
      end
  | None => None
  end.

Definition PW_NB : int := 256%uint63.
Definition pw_j (a : w64) : int := PrimInt63.land (wl a) 255%uint63.
Definition pw_nb (a : w64) : int := PrimInt63.lsr (wl a) 8%uint63.

Definition pw_ok (a : w64) : bool := negb (wt a) && PrimInt63.ltb (wl a) 768%uint63.
Definition is_lib (a : w64) : bool := weqb a wones.
Definition J_MAX : int := 27%uint63.
Definition J_CAP : int := 21%uint63.
Definition CAP_MAX : w64 := wlit 67108864%uint63.

Fixpoint block_windows (wl : list (int * sv * w64)) : list (int * sv) :=
  match wl with
  | [] => []
  | (k, len, kd) :: wl' => if weqb kd K_BLOCK then (k, len) :: block_windows wl' else block_windows wl'
  end.

Definition cap_ok (c : w64) : bool :=
  existsb (fun k : Z => weqb c (wlit (of_Z (65536 * 2 ^ k)))) [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10].

Definition malloc_stage_ok (fs : list fact) (a : w64) (wnl : list (int * sv * w64)) (n : sv) : option bool :=
  if PrimInt63.eqb (pw_nb a) 0%uint63 then
    (if PrimInt63.eqb (pw_j a) 0%uint63 && sv_eqb n (VL (wlit 65536%uint63)) then Some true else None)
  else if PrimInt63.eqb (pw_nb a) 1%uint63 then
    match block_windows wnl with
    | [(_, VL c)] =>
        if negb (cap_ok c) then None
        else if sv_eqb n (VL (wadd c c)) && wltu c CAP_MAX then Some true
        else if known_ltu fs (VL wzero) n && known_ltu fs n (VL CAP_MAX) then Some false
        else None
    | _ => None
    end
  else None.

Definition malloc_apply (st : sstate) : option (list sstate) :=
  match alloc_call ALLOC_STACK st with
  | Some (r, ksp, hargs0, wnl) =>
      match heap_A hargs0 with
      | Some (VL a) =>
          let n := getr st X10 in
          if pw_ok a && PrimInt63.leb (pw_j a) J_MAX && size_ok32 (s_facts st) n then
            match malloc_stage_ok (s_facts st) a wnl n with
            | Some grow =>
                let aB := if grow then VL (wadd a (wlit 257%uint63)) else VL wones in
                match heap_set_A hargs0 (VL wones), heap_set_A hargs0 aB with
                | Some hargsN, Some hargsB => malloc_posts st r ksp hargsN hargsB n
                | _, _ => None
                end
            | None => None
            end
          else None
      | _ => None
      end
  | None => None
  end.

Definition roomcap_apply (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_A hargs with
      | Some (VL a) =>
          if pw_ok a && PrimInt63.leb (pw_j a) J_CAP then
            match heap_set_A hargs (VL (W64 false (PrimInt63.add (PrimInt63.sub (wl a) (pw_j a)) J_CAP))) with
            | Some hargs' => Some [set_ops st (set_op HEAP_ID hargs' (s_ops st))]
            | None => None
            end
          else None
      | _ => None
      end
  | None => None
  end.

Definition free_stage_ok (a : w64) (wnl : list (int * sv * w64)) (k : int) : bool :=
  PrimInt63.eqb (pw_nb a) 2%uint63 && PrimInt63.ltb (pw_j a) 255%uint63 &&
  match block_windows wnl with
  | [(k1, VL c1); (k2, VL c2)] =>
      if PrimInt63.eqb k1 k then weqb c2 (wadd c1 c1) && wleu c2 CAP_MAX && negb (PrimInt63.eqb k2 k)
      else PrimInt63.eqb k2 k && weqb c1 (wadd c2 c2) && wleu c1 CAP_MAX
  | _ => false
  end.

Definition free_apply (st : sstate) : option (list sstate) :=
  match alloc_call ALLOC_STACK st with
  | Some (r, ksp, hargs, wnl) =>
      match heap_A hargs with
      | Some (VL a) =>
      match getr st X10 with
      | VL w => if weqb w wzero && is_lib a then
                  match alloc_post st r ksp with
                  | Some st1 => let (x, st2) := fresh st1 in Some [setr st2 X10 (VP x wzero)]
                  | None => None
                  end
                else None
      | VP k o =>
          if negb (weqb o wzero) || PrimInt63.eqb k 0%uint63 || PrimInt63.eqb k STACK_ID then None else
          let newA := if is_lib a then Some (VL a)
                      else if pw_ok a && free_stage_ok a wnl k then Some (VL (W64 false (PrimInt63.sub (PrimInt63.add (wl a) 1%uint63) PW_NB)))
                      else None in
          match newA, free_ok st wnl k, heap_del_window hargs (VP k wzero), alloc_post st r ksp with
          | Some a', Some _, Some hargs1, Some st1 =>
              match heap_set_A hargs1 a' with
              | Some hargs' =>
                  let (x, st2) := fresh st1 in
                  let st3 := setregs st2 (IMap.remove k (s_regs st2)) in
                  Some [setr (set_ops st3 (set_op HEAP_ID hargs' (s_ops st3))) X10 (VP x wzero)]
              | None => None
              end
          | _, _, _, _ => None
          end
      | _ => None
      end
      | _ => None
      end
  | None => None
  end.

Variable IMG_HI : int.
Definition IMG_LO : w64 := wlit 65536%uint63.
Definition aligned_alloc_apply (st : sstate) : option (list sstate) :=
  match alloc_call ALIGNED_STACK st, getr st X10 with
  | Some (r, ksp, hargs0, _), VL al =>
      match heap_drop_A hargs0 with
      | Some hargs =>
          let n := getr st X11 in
          if weqb al (wlit 16%uint63) && size_ok (s_facts st) n
          then malloc_posts_rg st r ksp hargs hargs n [(BLK_LO, wsub IMG_LO wone); (wlit IMG_HI, BLK_HI)] else None
      | None => None
      end
  | _, _ => None
  end.

Definition realloc_apply (st : sstate) : option (list sstate) :=
  match alloc_call REALLOC_STACK st with
  | Some (r, ksp, hargs0, wnl) =>
      match heap_drop_A hargs0 with
      | Some hargs =>
      let n := getr st X11 in
      if negb (size_ok (s_facts st) n) then None else
      match getr st X10 with
      | VL w => if weqb w wzero then malloc_posts st r ksp hargs hargs n else None
      | VP k o =>
          if negb (weqb o wzero) || PrimInt63.eqb k 0%uint63 || PrimInt63.eqb k STACK_ID then None else
          match IMap.find k (s_regs st), free_ok st wnl k with
          | Some rg, Some old =>
              if negb (sv_eqb (rg_hi rg) old) || negb (rg_w rg)
              then None else
              match alloc_post st r ksp, heap_del_window hargs (VP k wzero) with
              | Some stA0, Some hargs1 =>
                  let stA := setr (set_ops stA0 (set_op HEAP_ID hargs (s_ops stA0))) X10 (VL wzero) in
                  let (k', stB0) := fresh stA0 in
                  match heap_add_window hargs1 (VP k' wzero) n (VL K_BLOCK) with
                  | Some hargs' =>
                      let stB1 := setregs stB0 (IMap.add k' (Region 0%uint63 n true BGUnk IMap.empty)
                                                   (IMap.remove k (s_regs stB0))) in
                      let stB2 := set_ops stB1 (set_op HEAP_ID hargs' (s_ops stB1)) in
                      let stB3 := addfact (addfact (addfact stB2 (FRange k' BLK_LO BLK_HI)) (FAlign k' 4%uint63)) (FULt n (VL two47)) in
                      Some [stA; setr stB3 X10 (VP k' wzero)]
                  | None => None
                  end
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
      | None => None
      end
  | None => None
  end.

Definition sym_offset (R : IMap.t region) (a : sv) : option (int * sv) :=
  match a with
  | VP k o => if weqb o wzero then Some (k, VL wzero) else Some (k, VL o)
  | _ => match sym_addr_of R a with Some (k, _, off) => Some (k, off) | None => None end
  end.

Definition memcpy_sink_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X10 with
  | Some r, VP ka oa =>
      if negb (weqb oa wzero) || PrimInt63.eqb ka 0%uint63 then None else
      match sym_offset (s_regs st) (getr st X11), IMap.find ka (s_regs st) with
      | Some (kd, OFF), Some ra =>
          match IMap.find kd (s_regs st), rg_cells ra with
          | Some rd, IMap.Leaf =>
              let n := getr st X12 in
              let fs := s_facts st in
              if is_bgnone (rg_bg ra) && PrimInt63.eqb (rg_lo ra) 0%uint63 && rg_w ra && PrimInt63.eqb (rg_lo rd) 0%uint63
                 && negb (PrimInt63.eqb kd ka) && negb (PrimInt63.eqb kd 0%uint63)
                 && known_leu fs n (rg_hi ra) && known_leu fs OFF (rg_hi rd) && known_leu fs n (sv_alu ALU_SUB (rg_hi rd) OFF)
              then
                match havoc_errno segs ERRNO (clobber st) with
                | Some st2 => Some [setpc st2 r]
                | None => None
                end
              else None
          | _, _ => None
          end
      | _, _ => None
      end
  | _, _ => None
  end.
Definition memcpy_sink_c (pc : int) : contract := Contract pc memcpy_sink_apply.

Definition STRS_ID : int := 12%uint63.
Definition STRNLEN_STACK : int := 32%uint63.
Definition SZ (b : int) : sv := VBlob false b (VL wzero) 8%uint63.
Definition str_blob_ok (j : int) (H : sv) : bool :=
  (PrimInt63.eqb j 1%uint63 && sv_eqb H (SZ 9%uint63)) || (PrimInt63.eqb j 3%uint63 && sv_eqb H (SZ 10%uint63)).

Definition strnlen_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X10, getr st X11, stack_ok st STRNLEN_STACK with
  | Some r, VP ks os, VL m, Some (ksp, _) =>
      if negb (weqb os wzero) || PrimInt63.eqb ks 0%uint63 || PrimInt63.eqb ks STACK_ID || PrimInt63.eqb ks STRS_ID then None else
      match IMap.find ks (s_regs st), IMap.find STRS_ID (s_regs st), IMap.find STACK_ID (s_regs st) with
      | Some rs, Some r12, Some r1 =>
          match rg_cells rs, rg_bg rs, rg_cells r12, rg_bg r12 with
          | IMap.Leaf, BGBlob j sh, IMap.Leaf, BGBlob j12 sh12 =>
              let H := rg_hi rs in
              let fs := s_facts st in
              if str_blob_ok j H && sv_eqb (rg_hi r12) (SZ 15%uint63) && PrimInt63.eqb j12 STRS_ID
                 && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb sh12 0%uint63
                 && PrimInt63.eqb (rg_lo rs) 0%uint63 && PrimInt63.eqb (rg_lo r12) 0%uint63
                 && known_ltu fs (VL wzero) H && known_leu fs H (VL m)
                 && known_ltu fs (VL wzero) (VP ks wzero)
                 && known_leu fs (VP STRS_ID wzero) (VP ks wzero)
                 && known_leu fs (sv_alu ALU_ADD (VP ks wzero) H) (sv_alu ALU_ADD (VP STRS_ID wzero) (SZ 15%uint63))
                 && aligned fs (VP STRS_ID wzero) 3%uint63
              then
                let L := sv_alu ALU_SUB H (VL wone) in
                let st1 := setregs st (IMap.add STACK_ID (forget_r1 r1 ksp) (s_regs st)) in
                let st2 := addfact (addfact (addfact (clobber st1) (FULt L H)) (FULt L (VL m)))
                                   (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero)) in
                match havoc_errno segs ERRNO (setr st2 X10 L) with
                | Some st3 => Some [setpc st3 r]
                | None => None
                end
              else None
          | _, _, _, _ => None
          end
      | _, _, _ => None
      end
  | _, _, _, _ => None
  end.
Definition strnlen_c (pc : int) : contract := Contract pc strnlen_apply.

Definition malloc_c (pc : int) : contract := Contract pc malloc_apply.
Definition free_c (pc : int) : contract := Contract pc free_apply.
Definition malloc_s_c (pc : int) : contract := Contract pc malloc_s_apply.
Definition realloc_c (pc : int) : contract := Contract pc realloc_apply.
Definition aligned_alloc_c (pc : int) : contract := Contract pc aligned_alloc_apply.
Definition roomcap_c (pc : int) : contract := Contract pc roomcap_apply.

End WithImg.
End CtrA.
