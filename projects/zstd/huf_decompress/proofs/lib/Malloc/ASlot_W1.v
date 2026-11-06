(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocFacts_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W1 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W14ta_mC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W14as_kC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib6Malloc@F_malloc_enframe4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib6Malloc8ASlot_W18span_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W17span_fnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205c59OSSVerify5KrLib6Malloc8ASlot_W1=span_chk_trueC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00c59OSSVerify5KrLib6Malloc8ASlot_W1:span_fn_okC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition ta_avz (st3 : mstate) (m3 : aptr) : Malloc.M R :=
  activate_group m3 st3 (fun st4 mask =>
    guard 40 (negb (mask =? 0)) (
      ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail.

(* [comment removed for export] *)
Definition ta_act (st2 : mstate) (m2 : aptr) (mask : Z) : Malloc.M R :=
  let mr2 := get_meta_rec st2 m2 in
  let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
  let '(st3, m3) :=
    if Z.land mask (mask_upto gai) =? 0 then
      if negb (optr_eqb (m_next mr2) (Some m2)) then
        match m_next mr2 with
        | Some mn => (set_active sc (Some mn) st2, mn)
        | None => (st2, m2)
        end
      else
        let cnt := gai + 2 in
        let size := size_class (m_sizeclass mr2) * UNIT in
        let span := UNIT + size * cnt in
        let cnt := span_loop 300%nat cnt span size in
        let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
        match m_mem mr2 with
        | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
        | None => (st2, m2)
        end
    else (st2, m2) in
  ta_avz st3 m3.

(* [comment removed for export] *)
Definition ta_m (st1 : mstate) (m1 : aptr) : Malloc.M R :=
  let mask := m_freed (get_meta_rec st1 m1) in
  let '(st2, m2, mask) :=
    let mr := get_meta_rec st1 m1 in
    if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
      match m_next mr with
      | Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
      | None => (st1, m1, mask)
      end
    else (st1, m1, mask) in
  ta_act st2 m2 mask.

(* [comment removed for export] *)
Lemma try_avail_eq st :
  try_avail sc st k bail =
  match active st sc with
  | None => k st 0
  | Some m =>
    if negb (m_avail (get_meta_rec st m) =? 0) then ta_fin st m (m_avail (get_meta_rec st m)) k else
    let step1 : option (mstate * aptr) :=
      if m_freed (get_meta_rec st m) =? 0 then
        let st1 := dequeue (LActive sc) m st in
        match active st1 sc with None => None | Some m1 => Some (st1, m1) end
      else
        match m_next (get_meta_rec st m) with
        | Some m1 => Some (set_active sc (Some m1) st, m1)
        | None => None
        end in
    match step1 with
    | None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
              else SVis (EUndef UBadPtr) (fun _ => bail)
    | Some (st1, m1) => ta_m st1 m1
    end
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["CANSEC1"; "TA"] "p'0h02sth13st1i003st1h25step1i015step1i021mi032m1i041pi051xp;1p;2p;5p;3p;4g0000R0p4p70g000eR1p4p710p8p,1RR2p4p300R3g001\R4p4p710p8P3p1002Np4p710p8P3p1003Dp4p710p8P3g004CR5p4p710p8P3p1005:p4p710p8P4j1DTg0064j2CTg006kj23Tg007hj16Tg008`j20Tg009=j1;TP5j5:Tg009[R5j29Tg00:;R4j18Tg00:]j12Tg00;Uj17Tg00<Mj34Tg00=Ej45Tg00=ej21Tg00>Gj1BTg00>ij1ATg00?`j3<Tg00@[j2=Tg00ATj1>TP1j5?Tg00BIj2@Tg00BcR1%D2R3P4P0P3f0R6p,2scR7'CR8g00C\R9P3f1R:/36R;#6R<g00D<R='0#;P2P:P6P<p,1kR<D:P91910R>#8R?%2;/0=%77R@?46:P1P4P0P?P8P1P0P:P6C5,1>%B>R8n10110500021010300b1P4P0P?%A;P1P01106f2R;5<7P6C5,1>P8n10110500021010300n0100000020000P?P4P>P3P6P5P1P0P3P61=:6n2001104000120100103P9P313;:#2/0=P<A4@:;P=O2g00DZg00EOR;P2g00Em#>p,4bailV;D?n0100000020000n10110100021010400b2n0100000020000P<P6P=O2n10110500021010200'@X01P6O1W0o"). Qed.
End TA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_grp (st1 : mstate) : Malloc.M R :=
  alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
    match go with
    | None => k st2 (-1)
    | Some g =>
      let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
      queue (LActive sc) g st3 (fun st4 => k st4 0) bail
    end) bail.

Definition as_k (st1 : mstate) (first : Z) : Malloc.M R :=
  if negb (first =? 0) then k st1 (ctz32 first) else as_grp st1.

Lemma alloc_slot_S st : alloc_slot lay (S f) st sc req k bail = try_avail sc st as_k bail.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["CANSEC1"; "AS"] "h02stp;1p;5p;2p,1RR0p4p300R1g001\R2p4p710p8P1p100Flp4p710p8P1g005:R3p4p710p8P1p100Gbp4p710p8P1p100H^p4p710p8P2j12TP3j51Tg00BIj20Tg00BcR3%20P0p,2scf0R0g00IYp,4bailD1'0X03P0O1W0o"). Qed.
End AS.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
  end.

(* [comment removed for export] *)
Definition span_fn (sc cnt : Z) : bool :=
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16).
Definition span_chk (sc : Z) : bool := forallb (span_fn sc) (zseq 2 32).

Lemma span_chk_true : forallb span_chk (zseq 1 47) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["CANSEC1"] "p;2p;1p;3g00BIj26Tg00JRj11Tg00K0j12Tg00KUj10Tg00L:j25Tg00M;j34Tg00MWj33Tg00C\R0g00N1R1'6g00EOg00NQg00ONR2#1%22#0#0#0#0#1'534=301do"). Qed.

Lemma span_fn_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 -> span_fn sc cnt = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with44__x1h53cnth62sch72Hch83Hsch91Xp;1p;2p;3p;4p;7p;8g00JRj15Tg00P3j22Tg00KUj14Tg00K0j10Tg00POj29Tg00Pkj26Tg00QFj1OTg00Qfj1ITg00RFj1GTg00Rdj1ETg00SBj1DTg00Smj2@Tg00TPj2STg00BIj2RTg00U2j2QTg00MWj3ATg00U^j3NTg00V=j4LTg00Voj2KTg00WMj2HTg00>Gj1FTg00X0j3=Tg00XSj2;Tg00Y0j7<Tg00NQR0j1JTg00Z9j1CTg00[5j4>Tg00[`j7MTg00\Dj7BTg00\hj8PTg00EOR1f0R2'@p=3P1f1R3g00]LP2C>p=7P3g00^3R4g00^RR5P5g00_2R6P2g00_RFMp=1P1P3g00`2P2C>p=:f2R7P4P5P5P6P3P2FBp=8f3R8P4P5P5P6P7P3P2GPp=?g00ONR4#5R9/23R:%44#0#0#0#0#5R;,93'6%04R<#5R=/23R>%0<#0#0R?#4#5R@,23'6P0P9%4<#4#4#4#5R<P8g00`Yg00a[R0#ORA%I0R0%G1RB%E1RC%D1RDg00D<RE,@1RF%39RG'7'11SD6R6P2P7g00C\RHg00N1RI'R1Q27=AHIdAN1E3CLRJb1b2b312E9P2b0PAP01K13RKPCPD1H14R4,7G,1DRL%3;,:4,1D58D%F5R5%3<9=1G,:4,1D98DLC?P6PJb1b2b3X411292192;'61;9<,93,6:[^41P2f4R:P7O2R7b0F<%J8=AHI%C:P=%0?#5R?P8P2PAP0PBPC%3=RB,7F,1DP6PJb1b2b312E=P2b0PAP0PKPCPD17B4,1DRC%3@,74,1D58DP5%3?9=1B,:4,1D98DCC?P6PJb1b2b3X4112=2122@'61;=?,93,6>[^41P7b0F<b9W7W8X51X61P3P2O2X51X61o"). Qed.

Lemma span_exit_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 ->
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["CANSEC1"] "h03cnth12sch22Hch33Hscp;1p;2p;4g00JRj11Tg00P3j22Tg00KUj13Tg00K0j10Tg00POj26Tg00Pkj24Tg00bGj45Tg00EOR0g00ONR1#1f1R2'2%31#0#0#0#0#1,62'4%01R1#1/22%01#0#0#3#1,22'4f3f2P2f0R1C5W2W3X00X10P2P1O2X00W1o"). Qed.


End CANSEC1.
