(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS ASlot_W1.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_I () := "C35stdpp4base7is_SomeC35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:bad_answerC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7ag_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulc59OSSVerify5KrLib6Malloc7ASlot_I7ag_cnt1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3ltbc59OSSVerify5KrLib6Malloc7ASlot_I7ag_mmapC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc7ASlot_I7ag_nestC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W16as_grpC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>small_cnt_pickC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib4Spec6Malloc7med_cntC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:halve_evenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9halve_bigC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC56Stdlib6ZArith6BinInt1Z4evenC59OSSVerify5KrLib4Spec6Malloc>account_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec6Malloc2ev02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6s_atopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;live_rangesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>mmap_answer_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6is_errC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z03C59OSSVerify5KrLib4Spec6Malloc:new_regionC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>c_mmap_counterC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc3u32C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc@set_mmap_counterC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6shiftrC59OSSVerify5KrLib4Spec6Malloc<m_set_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7upd_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subK59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=size_to_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7lh_nestC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7slot_ofC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc7ASlot_I7ag_bodyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec6Malloc2IBC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7PROT_RWC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;MAP_PRIVATEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8MAP_ANONC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8full_layC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4mctx00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
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
        if negb (mmap_answer_ok (s_atop st1) (live_ranges st1) needed r) then bad_answer bail else
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
        if negb (mmap_answer_ok (s_atop st1) (live_ranges st1) needed r) then bad_answer bail else
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
ltac2:(KReplay.run1 (kr_t_ASlot_I ()) ["CANSEC1"; "AGB"] "h01mh12stp;1p;2p;3p-1R0p10000p4p710R1p8P0p1000ER2p4p710R3p8P0P2p4p7210R0p8g000YR4p4p70R5p1001Np4p710p8P5p1002Ep4p710R6p8P5p1002cR7p4p710R8p8P5P7p4p7210R7p8P5p1003<R9p4p710p8P5p1003Up4p73110p8P5P3p8p1003gp4p70R3P9p4p741110p8P3P1p8P3P0p8P3P2p4p73110p8P6P8p8P6P7p8p,1RR7p4p300R6g004\R8p4p710R2p8P6p1005Np4p710p8P6p1006Ip4p710p8P6p1007?p4p710p8P6p10089p4p710R3p8P6p10094p4p710p8P6p1009lp4p710p8P3P2p8P8j1;Tg00:gj1:Tg00;Lj12Tg00;jj21Tg00<Gj19Tg00=Bj20Tg00=_j13Tg00>Zj24Tg00?7j25Tg00?Tj36Tg00@Oj37Tg00AJj28Tg00AdR8%;7R7g00B]P7g00C=g00D2#:#2'1g00DWR7p,2sc#9'0f1R2#3R3'0/47'5f0R7=623A7273n0100000020000'8X04X18P2P7O2X04W1o"). Qed.

Lemma as_grp_eq st1 :
  as_grp full_lay f sc req k bail st1 = alloc_meta st1 (fun st mo => match mo with None => k st (-1) | Some m => ag_body st m end) bail.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_I ()) ["CANSEC1"; "AGB"] "p'0h03st1h12moi002moh21rh32sth43st2i013st2h51ch62goi022goh73idxh83st4i033cnti041gi051mi066neededi073ridi081xp;1p;2p;3p;4p;5p;6p;9p;7p;8p,1RR0p4p300g00ELR1p4p710p8g004\j1pTg00:gj19Tg00;Lj12Tg00;jj2ETg00<Gj1oTg00=Bj20Tg00FGj1=Tg00?7j21Tg00Flj2<Tg00Gbj2?Tg00Haj15Tg00I@j2STg00I^j1NTg00JVj3>Tg00KQj3CTg00LKj28Tg00Lhj2;Tg00MEj23Tg00McR2j2^Tg00NCj2\Tg00O?j1MTg00O]j1ZTg00P;j2GTg00Q:j1FTg00>Zj24Tg00R3j1HTg00Roj2YTg00SLj4BTg00Slj4XTg001Nj3WTg00Taj1VTg00UXj1UTg00VTj4RTg005Nj2OTg00WSj1PTg00XJj1QTg007?j5DTg00Xhj4TTg00Ycj1nTg00Zbj1mTg00[Vj2lTg00\Wj2hTg00]7j1JTg00^4j3@Tg00^mj2fTg00_ej26Tg00`Bj1eTg00a:j1bTg00b2j2aTg006Ij6`Tg0094l9ITg00bnj5KTg00cej1ATg00dcj2_Tg00eZj7cTg00fRj3dTg00gJj1]Tg009lj8gTg0089j4LTg00AJj2iTP1j8jTg00h?j2kTg00i:j3[Tf0R1g00DWR3'4p=7%91#9p=:g00AdR4%p0R5P0P1g003gR6g00iTR7g000YR8P5P1g00B]R9P5g00C=R:g00D2R;#9R<#2R='ER>p,2scR?#o,03R@P9g00j6RAP9PA%9<RB#=#2,1?RCf2RD/<?RE,??g00jT#5#5#5#5#5#5#5#5RF%=;RG#2RH,S?RI#NRJ=>FE;C@n0100000020000RK%2;RL'810@K#7/;>'3P=PKn0100000020000RK'0RM#7'1P2PAPAP5P91^AARN1\?D#MROP9PAP9PA%Z?%9BRP#:RQ#2,1?'31G?D#F14?L'<,4EPEn0100000020000RE%2BRB/0K'1/3OP9PA18IL%2P/0:/1MRP'3P=P9PA18I=10B:RB/1M'3PHP9PAg00k3RO,8IRI/3PPHP9PA10=:/1M,3I%=<#2PKn0100000020000n0100000020001n0100000020001n0100000020001PKn0100000020100R<%=G#2';'3P9PNp,3reqRNg00kQRI'4#7#HRM%7@'11;BM10=<,1E'3'YPAPAPLPMCBPAPAP<10@<#7#HCBR<n0100000020001P<n0100000020101g00lDR<PAP0POP1g00m9g00n1g00nm'4CXP9AW<A0RMf5RE,G?#FRB#V%UBf1R:P1CR#Mp,4bailRH,O0P9PM%P1P0f3RPPBp,1kRRP1%Q;R;O2X44RSPHDDP2P4g00ofR2PMg010DP1P:PBCTP0g011<RBg0125%n1/4L#m/l1W5%:G#2,hP#J=@E:'fP?PEP2PAP1POCBf4R2P9PAP9PA162LRG%9Q#:#:#:#2/63/E@/6LRQ'1PGPQn0100000020000RQ/1OPOPQn0100000020000P7P8P5P1P0%e?P1g012l%b1/6L/a1W2=@1DPRP1POO2X84PHE`PRP:P;O2R;n10110200021010400X66X44RQM9In2001108000121101107n0100000020001n0100000020001X2ADKn2001108000121103106P0PBp,1fRGPD10K@,43/6IRK#APKP9P5111OP0PDP:PSPHDDP7P8P5P9PAP9PAPC1<2?R2,??A>FJ2=CF@n0100000020000R2/8L10@2#7/;>'3P=P2n0100000020000/0@,43/6I#A,_:P0PB%JOPBPDP1P:P9PAP9PAPC1<E?RE,??A>FJE=CF@n0100000020000RF/8L10@F#7/;>'3P=PFn0100000020000RF/0@,43/6I#AP@PFFc5@PP?PPAdD1:PF16FLPQM9IP<PAP0g013c#]PHVADKn10110800021110400n0100000020001X7AX04PHGgn0100000020101P;n10110000021110500W1X34PHCL'iP0PBPGP?PNPRPHP1GjP0P1P7P8P5P11kD1P;n10110000021010500X16X34PHCL5[5eX04P1O1W0o"). Qed.
End AGB.


End CANSEC1.
