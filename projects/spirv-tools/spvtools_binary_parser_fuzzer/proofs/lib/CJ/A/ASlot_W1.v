(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocFacts_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ASlot_W1 () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec5STree5stree02C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6ta_finC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc9try_availC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2CJ4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes6option01K47Corelib4Init9Datatypes6option02C69OSSVerify5KrLib2CJ4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:set_activeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W14ta_mC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2CJ4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums1Z01I69OSSVerify5KrLib2CJ4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K69OSSVerify5KrLib2CJ4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;alloc_groupC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:alloc_slotC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W14as_kC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib2CJ1A@F_malloc_enframe4zseqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4bool01c69OSSVerify5KrLib2CJ1A8ASlot_W18span_chkC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2CJ1A@F_malloc_enframe<forallb_zseqC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W17span_fnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib2CJ1A8ASlot_W1=span_chk_trueC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00c69OSSVerify5KrLib2CJ1A8ASlot_W1:span_fn_okC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition ta_avz (st3 : mstate) (m3 : aptr) : Malloc.M R :=
  activate_group m3 st3 (fun st4 mask =>
    guard 40 (negb (mask =? 0)) (
      ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail.

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
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["AC_1"; "TA"] "p'0h02sth13st1i003st1h25step1i015step1i021mi032m1i041pi051xp;1p;2p;5p;3p;4g0000R0p4p70g000hR1p4p710p8p,1RR2p4p300R3g001bR4p4p710p8P3p1002Wp4p710p8P3p1003Pp4p710p8P3g004RR5p4p710p8P3p1005Lp4p710p8P4j1DTg006Ij2CTg007Cj23Tg008Cj16Tg009>j20Tg009[j1;TP5j5:Tg00:9R5j29Tg00:YR4j18Tg00;;j12Tg00<6j17Tg00=1j34Tg00=lj45Tg00>Lj21Tg00>nj1BTg00?Pj1ATg00@Jj3<Tg00AHj2=Tg00B?j1>TP1j5?Tg00C7j2@Tg00CQR1%D2R3P4P0P3f0R6p,2scR7'CR8g00DMR9P3f1R:/36R;#6R<g00DmR='0#;P2P:P6P<p,1kR<D:P91910R>#8R?%2;/0=%77R@?46:P1P4P0P?P8P1P0P:P6C5,1>%B>R8n10110500021010300b1P4P0P?%A;P1P01106f2R;5<7P6C5,1>P8n10110500021010300n0100000020000P?P4P>P3P6P5P1P0P3P61=:6n2001104000120100103P9P313;:#2/0=P<A4@:;P=O2g00EKg00FCR;P2g00Fa#>p,4bailV;D?n0100000020000n10110100021010400b2n0100000020000P<P6P=O2n10110500021010200'@W0o"). Qed.
End TA.

Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

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
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["AC_1"; "AS"] "h02stp;1p;5p;2p,1RR0p4p300R1g001bR2p4p710p8P1p100Gcp4p710p8P1g005LR3p4p710p8P1p100H\p4p7210p8P1p100I[p4p7210p8P2j12TP3j51Tg00C7j20Tg00CQ%20P0p,2scf0g00JYp,4bailD1'0W0o"). Qed.
End AS.

Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
  end.

Definition span_fn (sc cnt : Z) : bool :=
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16).
Definition span_chk (sc : Z) : bool := forallb (span_fn sc) (zseq 2 32).

Lemma span_chk_true : forallb span_chk (zseq 1 47) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["AC_1"] "p;2p;1p;3g00C7j26Tg00KPj11Tg00Knj12Tg00LSj10Tg00M8j25Tg00N7j34Tg00NSj33Tg00DMR0g00NmR1'6g00FCg00OMg00PHR2#1%22#0#0#0#0#1'534=301do"). Qed.

Lemma span_fn_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 -> span_fn sc cnt = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["AC_1"] "h07__arithh14__ffh28__varmaph35__with44__x1h52Hch63Hsch71Xh83cnth92scp;1p;2p;3p;4p;7p;8g00KPj15Tg00Pmj22Tg00LSj14Tg00Knj10Tg00QIj29Tg00Qej26Tg00R@j1OTg00R`j1ITg00S@j1GTg00S^j1ETg00T<j1DTg00Tgj2@Tg00UJj2STg00C7j2RTg00Ulj2QTg00NSj3ATg00VXj3NTg00W7j4LTg00Wij2KTg00XGj2HTg00>nj1FTg00Xjj3=Tg00YMj2;Tg00Yjj7<Tg00OMR0j1JTg00[1j1CTg00[kj4>Tg00\Vj7MTg00]:j7BTg00]^j8PTg00FCR1f0R2'@p=3P1f1R3g00^BP2C>p=7P3g00^iR4g00_HR5P5g00_hR6P2g00`HFMp=1P1P3g00`hP2C>p=:f2R7P4P5P5P6P3P2FBp=8f3R8P4P5P5P6P7P3P2GPp=?g00PHR4#5R9/23R:%44#0#0#0#0#5R;,93'6%04R<#5R=/23R>%0<#0#0R?#4#5R@,23'6P0P9%4<#4#4#4#5R<P8g00aOg00bOR0#ORA%I0R0%G1RB%E1RC%D1RDg00DmRE,@1RF%39RG'7'11SD6R6P2P7g00DMRHg00NmRI'R1Q27=AHIdAN1E3CLRJb1b2b312E9P2b0PAP01K13RKPCPD1H14R4,7G,1DRL%3;,:4,1D58D%F5R5%3<9=1G,:4,1D98DLC?P6PJb1b2b3X411292192;'61;9<,93,6:[^41P2f4R:P7O2R7b0F<%J8=AHI%C:P=%0?#5R?P8P2PAP0PBPC%3=RB,7F,1DP6PJb1b2b312E=P2b0PAP0PKPCPD17B4,1DRC%3@,74,1D58DP5%3?9=1B,:4,1D98DCC?P6PJb1b2b3X4112=2122@'61;=?,93,6>[^41P7b0F<b7W5W6X81X91o"). Qed.

Lemma span_exit_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 ->
  span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W1 ()) ["AC_1"] "h02Hch13Hsch23cnth32scp;1p;2p;4g00KPj11Tg00Pmj22Tg00LSj13Tg00Knj10Tg00QIj26Tg00Qej24Tg00c;j45Tg00FCR0g00PHR1#1f1R2'2%31#0#0#0#0#1,62'4%01R1#1/22%01#0#0#3#1,22'4f3f2P2f0C5W0W1X20W3o"). Qed.

End AC_1.
