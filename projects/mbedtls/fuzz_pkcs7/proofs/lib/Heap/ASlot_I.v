(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat MallocFacts_AS ASlot_W1.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_I () : Init.string Init.list := ["Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "Corelib.Init.Datatypes.pair"; "Stdlib.NArith.BinNat.N.lt"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "OSSVerify.KrLib.Heap.MallocBlocks.AREACH_from"; "OSSVerify.KrLib.Heap.MallocRep.agent_reserved"; "OSSVerify.KrLib.Heap.MallocFacts_AS.IST"; "ENTRY_REL"; "ALLC"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.MallocTree.auxv_ok"; "OSSVerify.KrLib.Heap.Malloc_iface.MEDTAB"; "OSSVerify.KrLib.Heap.Malloc_iface.medtab_cells"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.Heap.MallocTree.pres_except"; "OSSVerify.KrLib.Heap.Malloc_fp.malloc_fp"; "OSSVerify.KrLib.Heap.Malloc_fp.mrel"; "OSSVerify.KrLib.Heap.MallocTree.brk_link_ps"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "OSSVerify.KrLib.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.ps_so"; "as_inv2"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc_fp.slot_ok"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "stdpp.base.empty"; "stdpp.gmap.gmap_empty"; "OSSVerify.KrLib.Heap.F_malloc_enframe.rdv"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.MallocTree.pans_mem"; "OSSVerify.KrLib.Heap.Malloc.M"; "OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "as_pre2"; "OSSVerify.KrLib.Heap.Malloc.s_ceil"; "OSSVerify.KrLib.Heap.AllocSlot_iface.AS_STACK"; "OSSVerify.KrLib.Heap.Malloc_iface.AGP"; "as_post2"; "OSSVerify.KrLib.Heap.MallocTree.implT"; "OSSVerify.KrLib.Heap.Malloc.alloc_slot"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "OSSVerify.KrLib.Heap.MallocRep.alloc_slot_entry"].


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
Definition ALLC (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_I ()) "Prid,$0.Psh,$1.Po,$2.Pv,$2.Pt,$0.P,(3.(4.$1.)(5.$0.$1.(6.$0.$7.$8.$1.)(9.$0.$7.$8.$1.)R5.(:.O1.))(;.$1.R4.))P,(3.(4.(<.$2.$0.))(5.$2.(<.$2.$0.)(6.$2.$=.$>.(<.$2.$0.))(9.$2.$=.$>.(<.$2.$0.))R4.(?.R5.))(;.(<.$2.$0.)(10.$2.$0.R3.R2.)))(11.R3.(12.O1.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition ret_span (st1 : mstate) (sc idx : Z) (rid : N) (S len : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_I ()) "(13.$14.Lg,$14.(13.$14.Lb,$14.(15.(3.$16.(17.O6.O5.)(;.$14.R2.))(15.(3.$16.(18.(19.O6.R2.))(;.$14.R1.))(15.(3.$0.O3.(1:.$0.$2.R1.))(15.(3.$2.O2.(1;.(1;.(1<.$0.$2.R1.)+10.)(1=.(1>.(19.O6.R2.))O4.)))(3.$2.O1.(1?.(1>.(19.O6.R2.))+4.))))))))")
(* [comment removed for export] *).

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
        /\ (r_havp (get_shadow st1 rid)) !! (o / 4096) = None;
  (* [comment removed for export] *)
  ai_under : 0 <= idx -> forall g b, active st1 sc = Some g -> m_mem (get_meta_rec st1 g) = Some b -> under_virgin st1 g b idx
}.

Definition as_pre2 (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_I ()) "(15.(13.(20.$21.)LLB,(20.$21.)(15.(22.$23.O5.R1.)(24.O5.O4.)))(15.(25.O5.O4.)(15.(26.O4.)(15.(15.(27.=O3.)(28.O3.+30.))(15.(15.(27.=O2.)(28.O2.(29.+2.+20.)))(27.(1;.O2.+4.)(1=.+10.(2:.O3.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition as_post2
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
    (st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_I ()) "Lms',$2;.(13.(2<.&40.)Lt0,(2<.&40.)(13.(2<.&40.)Lt1,(2<.&40.)(13.(2<.&40.)Lt2,(2<.&40.)(13.(2<.&40.)La1,(2<.&40.)(13.(2<.&40.)La2,(2<.&40.)(13.(2<.&40.)La3,(2<.&40.)(13.(2<.&40.)La4,(2<.&40.)(13.(2<.&40.)La5,(2<.&40.)(13.(2<.&40.)La6,(2<.&40.)(13.(2<.&40.)La7,(2<.&40.)(13.(2<.&40.)Lt3,(2<.&40.)(13.(2<.&40.)Lt4,(2<.&40.)(13.(2<.&40.)Lt5,(2<.&40.)(13.(2<.&40.)Lt6,(2<.&40.)(13.P,(2<.&40.)(4.(2<.&8.))Lm',P,(2<.&40.)(4.(2<.&8.))(13.(2<.&40.)Lerrv',(2<.&40.)(15.(3.$2;.R11.(2=.(2>.O1=.O1<.O1;.O1:.R10.R?.R>.O19.O18.(2?.&40.O2.)R=.R<.R;.R:.R9.R8.R7.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R6.R5.R4.R3.)O=.(30.O1=.)O<.(31.(2<.&40.))R2.(32.$33.)))(15.(34.$33.R2.)(15.(35.$33.R2.O6.(36.&40.O1<.))(15.(37.$33.R2.(1;.(36.&40.O1:.)-:4.)(38.$39.(3:.R1.)(3;.$39.)))(15.(3<.R2.(36.&40.O1<.))(15.(37.$33.R2.$3=.$3>.)(15.(3?.O3.R2.)(15.(40.O3.)(15.(41.O3.O;.R2.)(15.(42.(43.O9.O3.O6.(36.&40.O1<.))O:.R2.)(15.(44.O8.O3.)(15.(45.O3.O1.)(15.(3.$46.(47.O1.)(47.O7.))(15.(3.(<.$2.$2.)(48.O1.)(48.O7.))(15.(3.$49.(4:.O1.)(4:.O7.))(15.(4;.O9.O8.O3.O5.O2.)(15.(15.(27.=(4<.(4=.O3.)))(28.(4<.(4=.O3.))(29.+2.+20.)))(4>.(3.$2.O2.-1.)(15.(27.=O2.)(13.$14.Lg,$14.(13.$14.Lb,$14.(13.$4?.Lr,$4?.(15.(3.$16.(17.O3.O5.)(;.$14.R3.))(15.(50.O3.R3.R2.R1.O2.O4.)(15.Pa,$2.P,(15.(27.(1?.(1;.(1;.(1;.(51.R2.)(1<.$0.$2.R3.))+10.)(1=.(1>.(19.O3.R4.))O2.))+4.)R1.)(28.R1.(1?.(1;.(1;.(1;.(1;.(51.R2.)(1<.$0.$2.R3.))+10.)(1=.(1>.(19.O3.R4.))O2.))(1>.(19.O3.R4.)))+4.)))(43.O9.O3.O6.(36.&40.O1<.)R2.)P,(3.(6.$0.$7.$8.$4?.)(52.O9.)(53.(6.$0.$7.$8.$4?.)(54.$0.$7.$8.$4?.)))(3.$2.(55.$56.$57.O;.O3.(10.$0.$2.(1:.$0.$2.R3.)(1;.(1;.(1<.$0.$2.R3.)(1;.+10.(1=.(1>.(19.O3.R4.))O2.)))-3.)))=))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition alloc_slot_stmt2 (fuel : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_I ()) "PR,StPk,P,$46.P,$2.(58.R3.)Pbail,(58.R2.)Po,$56.Ps,$59.PQ,P,R5.P,$59.P,$2;.SpPra,(2<.&40.)Psp,(2<.&40.)Pgp,(2<.&40.)Ptp,(2<.&40.)Pt0,(2<.&40.)Pt1,(2<.&40.)Pt2,(2<.&40.)Ps0,(2<.&40.)Ps1,(2<.&40.)Pa0,(2<.&40.)Pa1,(2<.&40.)Pa2,(2<.&40.)Pa3,(2<.&40.)Pa4,(2<.&40.)Pa5,(2<.&40.)Pa6,(2<.&40.)Pa7,(2<.&40.)Ps2,(2<.&40.)Ps3,(2<.&40.)Ps4,(2<.&40.)Ps5,(2<.&40.)Ps6,(2<.&40.)Ps7,(2<.&40.)Ps8,(2<.&40.)Ps9,(2<.&40.)Ps10,(2<.&40.)Ps11,(2<.&40.)Pt3,(2<.&40.)Pt4,(2<.&40.)Pt5,(2<.&40.)Pt6,(2<.&40.)PF,(5:.&5.(2<.&40.))Pfc,(2<.&20.)Pm,$56.Pst0,$46.Pst,$46.Plo,$2.Psc,$2.Preq,$2.Perrv,(2<.&40.)P,(5;.R6.R5.R3.R2.O1.)P,(3?.R6.R8.)P,(40.R7.)P,(41.R8.R2>.R:.)P,(45.R9.R2>.)P,(3<.R<.(36.&40.R2<.))P,(35.$33.R=.R:.(36.&40.R2=.))P,(27.(5<.R<.)R;.)P,(27.R<.(1?.(36.&40.R2?.)(5=.O1.)))P,(37.$33.R10.(1;.(36.&40.R2>.)-:4.)(38.$39.(3:.R:.)(3;.$39.)))P,(34.$33.R11.)P,(37.$33.R12.$3=.$3>.)P,(3.(2<.&40.)R32.(2?.&40.$5>.))P,(3.(2<.&40.)R32.(2?.&40.+1:620.))P,(3.(2<.&40.)R2=.(2?.&40.R11.))P,(3.(2<.&40.)R2=.(2?.&40.R11.))P,Pst1,$46.Pidx,$2.Ps',$59.Pms',$2;.P,(5?.R3<.R3;.R3:.R39.R35.R34.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1=.R1<.R3?.R1;.R1:.R19.R3>.R18.R17.R16.R4.R3.R2.R1.)(60.R43.R40.A2.R42.R5.R4.R3.R3>.R2.)(60.R3?.R3<.(61.R3?.$62.O1.R16.R14.R13.R3>.R3=.)R3;.R3:.(2=.(2>.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(2?.&40.$63.)R19.(31.(2<.&40.))R18.(32.$33.)))")
(* [comment removed for export] *).


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
        if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) needed r) then bad_answer bail else
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
        if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) needed r) then bad_answer bail else
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

#[using="Type"] Lemma ag_body_eq st m :
  ag_body st m = if PGSZ / 2 <? UNIT * size_class sc * ag_cnt1 st + UNIT then ag_mmap st m (ag_cnt1 st) else ag_nest st m (ag_cnt1 st).
Proof. reflexivity. Qed.

#[using="Type"] Lemma as_grp_eq st1 :
  as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
  unfold as_grp, alloc_group, ag_body, as_kq. f_equal.
Qed.
End AGB.
