(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocNat MallocFacts_AS ASlot_W1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_I () := "C35stdpp4base7is_SomeC35stdpp4base6LookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree00C13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:bad_answerC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5queueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9free_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:alloc_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7ag_tailC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:alloc_slotC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:size_classC13~~~C56Stdlib6ZArith6BinInt1Z3mulc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7ASlot_I7ag_cnt1C13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7ASlot_I7ag_mmapC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7ASlot_I7ag_nestC13~~~K47Corelib4Init5Logic2eq01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~I47Corelib4Init9Datatypes4bool00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4PGSZC13~~~K47Corelib7Numbers7BinNums8positive03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4UNITC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W16as_grpC13~~~K47Corelib7Numbers7BinNums8positive01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5usageC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>small_cnt_pickC13~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z4landC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7med_cntC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:halve_evenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9halve_bigC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes4prod00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;is_bouncingC13~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z4evenC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>account_bounceC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8step_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init9Datatypes4prod01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;live_rangesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>mmap_answer_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6is_errC13~~~K47Corelib7Numbers7BinNums1Z03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:new_regionC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>c_mmap_counterC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc3u32C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc@set_mmap_counterC13~~~C56Stdlib6ZArith6BinInt1Z6shiftrC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<m_set_maplenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~C56Stdlib6ZArith6BinInt1Z3subK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_set_availC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc=size_to_classC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7lh_nestC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7slot_ofC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev06C13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7ASlot_I7ag_bodyC13~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2IBC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7PROT_RWC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;MAP_PRIVATEC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8MAP_ANONC13~~~I47Corelib7Numbers7BinNums1N00K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8full_layC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<undef_reason03C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


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
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_I ()) ["CEIL_WRAP_1"; "AGB"] "h01mh12stp;1p;2p;3p-1R0p10000p4p710R1p8P0p1000ER2p4p710R3p8P0P2p4p7210R0p8g000YR4p4p70R5p1001gp4p710p8P5p10037p4p710p8P5p1003UR6p4p710p8P5P6p4p7210p8P5p1003nR6p4p710p8P5p1004Gp4p73110p8P5P3p8p1004Yp4p70R3P6p4p741110p8P3P1p8P3P0p8P3P2p4p73110p8p,1RR2p4p300R3g005gR0p4p710R1p8P3p10072p4p710p8P3p1008Fp4p710p8P3p1009Up4p710p8P3p100:hp4p7210R6p8P3p100<<p4p710p8P3p100=Mp4p7210p8P6P1p8P0j1;Tg00>aj1:Tg00?Fj12Tg00?dj21Tg00@Aj19Tg00AUj20Tg00B2j13Tg00CEj24Tg00Cbj25Tg00D?j36Tg00ERj37Tg00Fej28Tg00G?R0%;2R2g00HQP2g00I1g00J?#:#2'1g00JdR2p,2sc#9'0f1R1#3R6'0/42'5f0R2=616A7126n0100000020000'8X04X10P1P2O2X04W1o"). Qed.

Lemma as_grp_eq st1 :
  as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_I ()) ["CEIL_WRAP_1"; "AGB"] "p'0h03st1h12moi002moh21rh32sth43st2i013st2h51ch62goi022goh73idxh83st4i033cnti041gi051mi066neededi073ridi081xp;1p;2p;3p;4p;5p;6p;9p;7p,1RR0p4p300g00L2R1p4p7210p8g005gj1oTg00>aj18Tg00?Fj12Tg00?dj2ETg00@Aj1nTg00AUj20Tg00MEj1<Tg00Cbj21Tg00Mjj2=Tg00O9j2?Tg00PQj15Tg00Q0j2RTg00QNj1NTg00R_j3CTg00T3j3@Tg00UFj29Tg00Ucj2:Tg00V@j23Tg00V^R2j2]Tg00W>j2[Tg00XSj1ITg00Y1j1ZTg00YOj2GTg00Zgj1FTg00CEj24Tg00\9j1HTg00]Nj2YTg00]kj4BTg00^Kj4XTg001gj3WTg00_Yj1VTg00`nj4UTg0072j2QTg00bFj1OTg00cVj1PTg009Uj5DTg00d4j4STg00eHj1TTg00f`j1mTg00gmj2lTg00iGj2kTg00igj1KTg00k=j3>Tg00lOj2fTg00m`j26Tg00n=j1cTg00oNj1bTg010_j2aTg008Fj6`Tg00<<l9JTg0124j5LTg013Dj1ATg014[j2_Tg015kj7^Tg017<j3dTg018Mj1eTg00=Ml9\Tg00:hj5MTg00Fej2gTP1l9hTg019[j2iTg01:nj3jTf0R1g00JdR3'4p=7%81#8p=;g00G?R4%o0R5p,4RUNpR6P0P1g004YR7g01;HR8g000YR9P5P1g00HQR:P5g00I1R;g00J?R<#8R=#2R>'ER?p,2scR@#n,03RAP:g01;jRBP:PB%8=RC#<#2,1@RDf2RE/=@RF,?@g01<H#5#5#5#5#5#5#5#5RG%<<RH#2RI,R@RJ#NRK=CGF;@An0100000020000RL%2<RM'910AL#7/:?'3P>PLn0100000020000RL'0RN#7'1P2PBPBP5P:1]BBRO1[@E#IRPP:PBP:PB%Z@%8CRQ#;RR#2,1@'31G@E#F14@M'=,4FPFn0100000020000RF%2CRC/0L'1/3PP:PB19JM%2Q/0;/1NRQ'3P>P:PB19J>10C;RC/1N'3PIP:PBg01<gRP,9JRJ/3QPIP:PB10>;/1N,3J%<=#2PLn0100000020000n0100000020001n0100000020001n0100000020001PLn0100000020100R=%<H#2':'3P:POp,3reqROg01=ERJ'4#7#HRN%7A'11:CN10>=,1F'3'YPBPBPMPNCBPBPBP=10A=#7#HCBR=n0100000020001P=n0100000020101g01>QR=PBP0PPP1g01?_g01A0g01BE'4CXP:AW=B0RNP6f5RF,G@#FRC#Vf1R;P1CU#Ip,4bailRI,Q0P:PN%O1P0f3RQPCp,1kRSP1%P<R<O2X44RTPIDDP2P4g01CWR2PNg01D5P1P;PCCSP0g01EFRCg01FX%T1/4M#m/l1W5%;H#2,kQ#K=>F;'fP@PFP2PBP1PPCBf4R2P:PBP:PB162MRH%8R#;#;#;#2/63/EA/6MRR'1PHPRn0100000020000RR/1PPPPRn0100000020000P8P9P5P1P0%c@P1g01Gh%b1/6M/a1W2=>1EPSP1PPO2X84PIE`PSP;P<O2R<n10110200021010400X67X44RRM9Jn2001108000121101107n0100000020001n0100000020001X2BDLn2001108000121103106P6P0PCp,1fRHPE10LA,43/6JRL#APLP:P5111PP0PEP;PTPIDDP8P9P5P:PBP:PBPD1=2@R2,?@ACGK2=@GAn0100000020000R2/9M10A2#7/:?'3P>P2n0100000020000/0A,43/6J#A,_;P0PC%KPPCPEP1P;P:PBP:PBPD1=F@RF,?@ACGKF=@GAn0100000020000RG/9M10AG#7/:?'3P>PGn0100000020000RG/0A,43/6J#APAPGF^5>QP@PQAdE1;PG16GMPRM9JP=PBP0g01I8#ePIVBDLn10110800021110400n0100000020001X7BX04PIM9\n0100000020101P<n10110000021110500W1X34PIDM'gP6P0PCPHP@POPSPIP1M9hP6P0P1P8P9P5P11iE1P<n10110000021010500X17X34PIDM5j5eX04P1O1W0o"). Qed.
End AGB.
End CEIL_WRAP_1.

