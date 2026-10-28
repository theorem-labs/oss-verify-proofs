(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import Malloc_fp AllocSlot_iface Malloc_iface.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocFacts_AS.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Malloc_fp.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS.MallocNat OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_AS OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.Malloc_fp.ASlot_W1.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Record ENTRY_REL (st0 st : mstate) : Prop := mkER {
  er_shadow : s_shadow st = s_shadow st0;
  er_groups : forall b, is_Some ((s_groups st) !! b) <-> is_Some ((s_groups st0) !! b);
  er_gregions : forall rid r, r_kind r = RKGroup -> ((s_regions st) !! rid = Some r <-> (s_regions st0) !! rid = Some r);
  er_mrel : mrel st0 st;
  er_mem : forall q, m_mem (get_meta_rec st q) = m_mem (get_meta_rec st0 q);
  er_geom : forall q, m_mem (get_meta_rec st0 q) <> None ->
      get_stride (get_meta_rec st q) = get_stride (get_meta_rec st0 q)
      /\ m_last_idx (get_meta_rec st q) = m_last_idx (get_meta_rec st0 q)
      /\ m_sizeclass (get_meta_rec st q) = m_sizeclass (get_meta_rec st0 q);
  er_bits : forall q i, 0 <= i ->
      Z.testbit (m_avail (get_meta_rec st q)) i || Z.testbit (m_freed (get_meta_rec st q)) i = true ->
      Z.testbit (m_avail (get_meta_rec st0 q)) i || Z.testbit (m_freed (get_meta_rec st0 q)) i = true;
  er_areas : forall a, is_Some ((s_areas st0) !! a) -> is_Some ((s_areas st) !! a)
}.

(* [comment removed for export] *)
Definition ALLC (st : mstate) : Prop :=
  forall rid sh o v t, (s_shadow st) !! rid = Some sh -> (r_cells sh) !! o = Some (v, t) -> (t < s_tick st)%N.

(* [comment removed for export] *)
Definition ret_span (st1 : mstate) (sc idx : Z) (rid : N) (S len : Z) : Prop :=
  exists g b, active st1 sc = Some g /\ m_mem (get_meta_rec st1 g) = Some b /\ rid = fst b
    /\ S = snd b + 16 + get_stride (get_meta_rec st1 g) * idx /\ len = get_stride (get_meta_rec st1 g) - 4.

Record as_inv2 (st0 st st1 : mstate) (sc idx : Z) : Prop := mkAI {
  ai_act : forall c, 0 <= c < sc -> active st1 c = active st c;
  ai_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  ai_tick : s_tick st1 = s_tick st;
  (* [comment removed for export] *)
  ai_fresh : 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o v t, S <= o < S + len -> (r_cells (get_shadow st1 rid)) !! o = Some (v, t) -> (t < s_tick st1)%N;
  (* [comment removed for export] *)
  ai_virgin : s_regions st0 = ∅ -> 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o, S <= o < S + len ->
        (r_cells (get_shadow st1 rid)) !! o = None /\ (r_hav (get_shadow st1 rid)) !! (o / 16) = None
        /\ (r_havp (get_shadow st1 rid)) !! (o / 4096) = None
}.

Definition as_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, AREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition as_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ auxv_ok m' (bv_unsigned sp)
    /\ rw_cells asegs m' MEDTAB medtab_cells
    /\ mrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
    /\ pres_except (malloc_fp st0 st1 lo (bv_unsigned sp)) m m'
    /\ mrel st st1 /\ brk_link_ps st1 s'
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ as_inv2 st0 st st1 sc idx
    /\ 0 <= c_mmap_counter (ctx st1) < 2^32
    /\ (idx = -1
        \/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
              /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
                           < r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
                    malloc_fp st0 st1 lo (bv_unsigned sp) a)
              /\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Definition alloc_slot_stmt2 (fuel : nat) : Prop :=
  forall (R : Type) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
  as_pre2 st0 st sc req fuel ->
  mrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
  auxv_ok m (bv_unsigned sp) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AS_STACK fuel ->
  rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> rw_cells asegs m MEDTAB medtab_cells ->
  gp = Z_to_bv 64 AGP -> tp = Z_to_bv 64 0x1a620 ->
  a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
  (forall st1 idx s' ms',
     as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
     implT o (k st1 idx) s' Q ms') ->
  implT o (alloc_slot full_lay fuel st sc req k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 alloc_slot_entry) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
Section AGB.
Context {R : Type}.
Variables (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_kq (st2 : mstate) (go : optr) : Malloc.M R :=
  match go with
  | None => k st2 (-1)
  | Some g =>
    let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
  end.

(* [comment removed for export] *)
Definition ag_body (st : mstate) (m : aptr) : Malloc.M R :=
  let size := UNIT * size_class sc in
    let usage0 := usage st sc in
    let cnt :=
      if sc <? 9 then small_cnt_pick sc usage0
      else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
    let cnt := if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt in
    let tail (st : mstate) (p : aptr) (cnt active_idx : Z) : Malloc.M R := ag_tail full_lay st sc m p cnt active_idx as_kq in
    if PGSZ / 2 <? size * cnt + UNIT then
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          tail st4 (rid, 0) cnt ai)
    else
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest full_lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            tail st3 p cnt (cnt - 1)
          end) bail.

(* [comment removed for export] *)
Definition ag_cnt1 (st : mstate) : Z :=
  let size := UNIT * size_class sc in
  let usage0 := usage st sc in
  let cnt :=
    if sc <? 9 then small_cnt_pick sc usage0
    else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) usage0) size in
  if (cnt =? 1) && (size * cnt + UNIT <=? PGSZ / 2) then 2 else cnt.

Definition ag_mmap (st : mstate) (m : aptr) (cnt : Z) : Malloc.M R :=
  let size := UNIT * size_class sc in
  let usage0 := usage st sc in
      let nosmall := is_bouncing sc st in
      let st1 := step_seq (account_bounce sc st) in
      let usage1 := if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0 in
      let cnt :=
        if (usage1 <? 4 * cnt) && negb nosmall then
          if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
          else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
          else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
          else cnt
        else cnt in
      let needed := round_up_pg (size * cnt + UNIT) in
      let '(cnt, needed) :=
        if negb nosmall && (cnt <=? 7) then
          let req := round_up_pg (req + IB + UNIT) in
          if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed)
        else (cnt, needed) in
      SVis (EMmap 0 needed PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
        if negb (mmap_answer_ok (live_ranges st1) needed r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r needed st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr needed 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if cnt - 1 <? ai then cnt - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) cnt ai as_kq).

Definition ag_nest (st : mstate) (m : aptr) (cnt : Z) : Malloc.M R :=
  let size := UNIT * size_class sc in
      let j := size_to_class (UNIT + cnt * size - IB) in
      alloc_slot full_lay f st j (UNIT + cnt * size - IB) (fun st1 idx =>
        if idx <? 0 then free_meta m st1 (fun st2 => as_kq st2 None) bail
        else
          match active st1 j with
          | None => SVis (EUndef UBadPtr) (fun _ => bail)
          | Some g =>
            let p := slot_of st1 g idx in
            let st2 := lh_nest full_lay st1 g idx j size cnt in
            let st3 := upd_meta m (m_set_maplen 0) st2 in
            ag_tail full_lay st3 sc m p cnt (cnt - 1) as_kq
          end) bail.

Lemma ag_body_eq st m :
  ag_body st m = if PGSZ / 2 <? UNIT * size_class sc * ag_cnt1 st + UNIT then ag_mmap st m (ag_cnt1 st) else ag_nest st m (ag_cnt1 st).
Proof. reflexivity. Qed.

Lemma as_grp_eq st1 :
  as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
  unfold as_grp, alloc_group, ag_body, as_kq. f_equal.
Qed.
End AGB.

End ACeilS1.
