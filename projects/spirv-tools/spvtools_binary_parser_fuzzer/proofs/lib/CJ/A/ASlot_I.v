(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocNat MallocFacts_AS ASlot_W1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ASlot_I () := "C35stdpp4base7is_SomeC35stdpp4base6LookupC69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A7ASlot_I@alloc_slot_stmt2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC69OSSVerify5KrLib2CJ4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulc69OSSVerify5KrLib2CJ1A7ASlot_I7ag_cnt1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbc69OSSVerify5KrLib2CJ1A7ASlot_I7ag_mmapC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A7ASlot_I7ag_nestC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib2CJ4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2CJ4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A:MallocTree5implTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A8ASlot_W16as_grpC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2CJ4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z4landC69OSSVerify5KrLib2CJ4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes4prod00C69OSSVerify5KrLib2CJ4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z4evenC69OSSVerify5KrLib2CJ4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init9Datatypes4prod01K69OSSVerify5KrLib2CJ4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C69OSSVerify5KrLib2CJ4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC69OSSVerify5KrLib2CJ4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK69OSSVerify5KrLib2CJ4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A7ASlot_I7ag_bodyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2CJ4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K69OSSVerify5KrLib2CJ4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

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

Definition ALLC (st : mstate) : Prop :=
  forall rid sh o v t, (s_shadow st) !! rid = Some sh -> (r_cells sh) !! o = Some (v, t) -> (t < s_tick st)%N.

Definition ret_span (st1 : mstate) (sc idx : Z) (rid : N) (S len : Z) : Prop :=
  exists g b, active st1 sc = Some g /\ m_mem (get_meta_rec st1 g) = Some b /\ rid = fst b
    /\ S = snd b + 16 + get_stride (get_meta_rec st1 g) * idx /\ len = get_stride (get_meta_rec st1 g) - 4.

Record as_inv2 (st0 st st1 : mstate) (sc idx : Z) : Prop := mkAI {
  ai_act : forall c, 0 <= c < sc -> active st1 c = active st c;
  ai_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  ai_tick : s_tick st1 = s_tick st;

  ai_fresh : 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o v t, S <= o < S + len -> (r_cells (get_shadow st1 rid)) !! o = Some (v, t) -> (t < s_tick st1)%N;

  ai_virgin : s_regions st0 = ∅ -> 0 <= idx -> forall rid S len, ret_span st1 sc idx rid S len ->
      forall o, S <= o < S + len ->
        (r_cells (get_shadow st1 rid)) !! o = None /\ (r_hav (get_shadow st1 rid)) !! (o / 16) = None
        /\ (r_havp (get_shadow st1 rid)) !! (o / 4096) = None
}.

Definition as_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
  (exists LB, AREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
  /\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

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

Section AGB.
Context {R : Type}.
Variables (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition as_kq (st2 : mstate) (go : optr) : Malloc.M R :=
  match go with
  | None => k st2 (-1)
  | Some g =>
    let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
    queue (LActive sc) g st3 (fun st4 => k st4 0) bail
  end.

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
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_I ()) ["AC_1"; "AGB"] "h01mh12stp;1p;2p;3p-1R0p10000p4p710R1p8P0p1000ER2p4p710R3p8P0P2p4p7210R0p8g000YR4p4p70R5p1001Qp4p710p8P5p1002Kp4p710p8P5p1002iR6p4p710p8P5P6p4p7210p8P5p1003BR6p4p710p8P5p1003[p4p73110p8P5P3p8p1003mp4p70R3P6p4p741110p8P3P1p8P3P0p8P3P2p4p73110p8p1004ep6164111001R2g005gR3p4p710R0p8P2p1006\p4p7210R2p8p,1RR1p4p300R6P0p8P6p1007Zp4p710p8P6p1008Xp4p710p8P6p1009Qp4p710p8P6p100:Np4p7210R5p8P6p100;Lp4p710p8P6P2p8P5P0p8P3j1;Tg00<Gj1:Tg00<lj12Tg00=Jj21Tg00=gj19Tg00>ej20Tg00?Bj13Tg00@;j24Tg00@Xj25Tg00A5j36Tg00Anj37Tg00Bgj28Tg00CA%;1R1g00D=P1g00D]g00EU#:#2'1g00F:R1p,2sc#9'0f1R3#3R0'0/41'5f0R1=630A7310n0100000020000'8X04W1o"). Qed.

Lemma as_grp_eq st1 :
  as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_I ()) ["AC_1"; "AGB"] "p'0h02moi002moh11rh22sth33st1h43st2i013st2h51ch62goi022goh73idxh83st4i033cnti041gi051mi066neededi073ridi081xp;1p;2p;3p;4p;5p;6p;9p;7p1004ep6164111001p100G2p4p7210p8p,1RR0p4p300g00GlR1p4p7210p8g005gj1oTg00<Gj18Tg00<lj12Tg00=Jj2ETg00=gj1nTg00>ej20Tg00Hej1<Tg00@Xj21Tg00IJj2=Tg00JCj2?Tg00KEj15Tg00Kdj2RTg00LBj1NTg00M=j3CTg00N;j3@Tg00O8j29Tg00OUj2:Tg00P2j23Tg00PPR2j2]Tg00Q0j2[Tg00Qoj1ITg00RMj1ZTg00Rkj2GTg00Smj1FTg00@;j24Tg00Tij1HTg00Uhj2YTg00VEj4BTg00Vej4XTg001Qj3WTg00W]j1VTg00X\j4UTg007Zj2QTg00Y^j1OTg00ZXj1PTg009Qj5DTg00[6j4STg00\4j1TTg00]6j1mTg00]mj2lTg00_1j2kTg00_Qj1KTg00`Qj3>Tg00aMj2fTg00bHj26Tg00bej1cTg00c`j1bTg00d[j2aTg008Xj6`Tg00;Ll9JTg00eZj5LTg00fTj1ATg00gUj2_Tg00hOj7^Tg00iJj3dTg00jEj1eTg006\l9\Tg00:Nj5MTg00Bgj2gTP1l9hTg00k=j2iTg00l6j3jTf0R1g00F:R3'4p=7%81#8p=;g00CAR4%o0R5p,5ACEILR6P0P1g003mR7g00lPR8g000YR9P5P1g00D=R:P5g00D]R;g00EUR<#8R=#2R>'ER?p,2scR@#n,03RAP:g00m2RBP:PB%8=RC#<#2,1@RDf2RE/=@RF,?@g00mP#5#5#5#5#5#5#5#5RG%<<RH#2RI,R@RJ#NRK=CGF;@An0100000020000RL%2<RM'910AL#7/:?'3P>PLn0100000020000RL'0RN#7'1P2PBPBP5P:1]BBRO1[@E#IRPP:PBP:PB%Z@%8CRQ#;RR#2,1@'31G@E#F14@M'=,4FPFn0100000020000RF%2CRC/0L'1/3PP:PB19JM%2Q/0;/1NRQ'3P>P:PB19J>10C;RC/1N'3PIP:PBg00moRP,9JRJ/3QPIP:PB10>;/1N,3J%<=#2PLn0100000020000n0100000020001n0100000020001n0100000020001PLn0100000020100R=%<H#2':'3P:POp,3reqROg00nMRJ'4#7#HRN%7A'11:CN10>=,1F'3'YPBPBPMPNCBPBPBP=10A=#7#HCBR=n0100000020001P=n0100000020101g00oCR=PBP0PPP1g010;g0116g0125'4CXP:AW=B0RNP6f5RF,G@#FRC#Vf1R;P1CU#Ip,4bailRI,Q0P:PN%O1P0f3RQPCp,1kRSP1%P<R<O2X44RTPIDDP2P4g0131R2PNg013OP1P;PCCSP0g014JRCg015F%T1/4M#m/l1W5%;H#2,kQ#K=>F;'fP@PFP2PBP1PPCBf4R2P:PBP:PB162MRH%8R#;#;#;#2/63/EA/6MRR'1PHPRn0100000020000RR/1PPPPRn0100000020000P8P9P5P1P0%c@P1g016@%b1/6M/a1W1=>1EPSP1PPO2X84PIE`PSP;P<O2R<n10110200021010400X67X44RRM9Jn2001108000121101107n0100000020001n0100000020001X1BDLn2001108000121103106P6P0PCp,1fRHPE10LA,43/6JRL#APLP:P5111PP0PEP;PTPIDDP8P9P5P:PBP:PBPD1=2@R2,?@ACGK2=@GAn0100000020000R2/9M10A2#7/:?'3P>P2n0100000020000/0A,43/6J#A,_;P0PC%KPPCPEP1P;P:PBP:PBPD1=F@RF,?@ACGKF=@GAn0100000020000RG/9M10AG#7/:?'3P>PGn0100000020000RG/0A,43/6J#APAPGF^5>QP@PQAdE1;PG16GMPRM9JP=PBP0g017:#ePIVBDLn10110800021110400n0100000020001X7BX34PIM9\n0100000020101P<n10110000021110500W0X24PIDM'gP6P0PCPHP@POPSPIP1M9hP6P0P1P8P9P5P11iE1P<n10110000021010500X07X24PIDM5j5eW3o"). Qed.
End AGB.

End AC_1.
