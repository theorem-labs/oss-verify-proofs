(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AQWf2 AQPart ACover AFreeR AFreeR2 AFreeR3 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2 AFreeRP AFreeRQ AFreeRU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRM AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AWrapKit ACoresk ACoreF2 ANodeA7 ANodeA6 ANodd09 ANodl61 APopG2 APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2.AFreeRW OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRI1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodd09 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR.ARt4bhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2.

Module AFreeRI2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct Divembc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSnjd ARtSrgm AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeB1 AFreeH AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AQWf AQWf2 AQPart ACover AFreeR AFreeR2 AFreeR3 AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2 AFreeRP AFreeRQ AFreeRU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRW2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRM AFreeRC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRE.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AWrapKit ACoresk ACoreF2 ANodeA7 ANodeA6 ANodd09 ANodl61 APopG2 APopG5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AFreeRK2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQWf2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AQPart OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRQ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2.AFreeRW OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRI1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRE.AFreeRL OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AWrapKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoresk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ACoreF2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodd09 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.APopG5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeR.ARt4bhx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRK2.AFreeRK3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AFreeRW2.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.

(* [comment removed for export] *)
Lemma free_cached_count {Clg : Ceiling} : forall A c, WFR A -> 1 <= c <= 30 ->
  Z.of_nat (length (rg_free (a_reg A c))) + Z.of_nat (length (pk_chunks (a_cache A c))) <= carved_count A c.
Proof.
  intros A c W CR.
  (first [ pose proof ((wrR A W)) as dR_1; dand3 dR_1 as WR _ _ | destruct (wrR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c CR)) as dR_2; dand10 dR_2 as (R1 & _) _ _ _ _ _ _ FND FRG _ | destruct (WR c CR) as ((R1 & _) & _ & _ & _ & _ & _ & _ & FND & FRG & _) ]).
  destruct (wrC A W) as (WC & _). (first [ pose proof ((WC c ltac:(lia))) as dR_3; dand4 dR_3 as _ CND CRG _ | destruct (WC c ltac:(lia)) as (_ & CND & CRG & _) ]).
  pose proof (wrX A W) as PX.
  pose proof (class_size_range c CR) as CSR.
  assert (C0 : 0 <= carved_count A c) by (unfold carved_count, carved_count_; apply Z.div_pos; lia).
  apply NoDup_ListNoDup in FND. apply NoDup_ListNoDup in CND.
  assert (ND : List.NoDup (rg_free (a_reg A c) ++ pk_chunks (a_cache A c))).
  { apply NoDup_app; [exact FND| exact CND|]. intros k HF HC.
    (first [ pose proof ((PX c k CR (FRG k HF))) as dR_4; dand3 dR_4 as _ NFC _ | destruct (PX c k CR (FRG k HF)) as (_ & NFC & _) ]). apply NFC. split; [exact HF| exact HC]. }
  pose proof (NoDup_incl_length ND (l' := map Z.of_nat (seq 0 (Z.to_nat (carved_count A c))))) as X.
  rewrite length_app, !length_map, length_seq in X.
  assert (Y : (length (rg_free (a_reg A c)) + length (pk_chunks (a_cache A c)) <= Z.to_nat (carved_count A c))%nat).
  { apply X. intros x Hx. apply in_map_iff. exists (Z.to_nat x).
    assert (RG : 0 <= x < carved_count A c) by (apply in_app_or in Hx as [Hx|Hx]; [exact (FRG x Hx)| exact (CRG x Hx)]).
    split; [lia|]. apply in_seq. lia. }
  lia.
Qed.


Section RIter.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet).
  (* [comment removed for export] *)
  Variables (xs2 xs5 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation put_frame := (put_frameG rac spd s0 s1 s2 s3 s4 s5 s6 stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation rec_frame := (rec_frameG spd stkobj xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation dorec_fr := (dorec_frG s7 s8 s9 stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation head_cfg := (head_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation exit_cfg := (exit_cfgG spd gp s7 s8 s9 s10 s11 F fc stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation XCUR := (XCURG rac spd s0 s1 s2 s3 s4 s5 s6 A0 m0 md0 p n0 stkobj lo hi xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation KMORE := (KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation KDONE := (KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5).

  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_prim_drainmap : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (i : nat) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (c k n : Z),
    CUR A m md (Some (b0, i)) more scr ->
    nth_error (ba_entries b0) i = Some (QE (ChP (CP c k)) n) ->
    Z.of_nat (length (pk_chunks (a_cache A c))) = max_count c ->
    rg_mapped_fa (a_reg A c) < 4 * (Z.of_nat (length (rg_free (a_reg A c))) + max_count c / 2) ->
    KMORE A b0 i more scr -> KDONE A b0 i more scr ->
    srealizes rsegs (it_cfg A m md b0 (Z.of_nat i) dorec_callblk ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6') TS.
  Proof.
    intros A m md b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CU NTH FULL NOROOM KM KD.
    destruct CU as [RI HIST MI ST PF RF DF [LEN ILE] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0)) :: more).
    { rewrite L. unfold limbo_of. rewrite (skipn_cons_nth (ba_entries b0) i _ NTH). reflexivity. }
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_5; dand10 dR_5 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_6; dand6 dR_6 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_7; dand6 dR_7 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_SBc A v [] AR) as CSB. pose proof (rk_CRI A v [] AR) as CRI.
    pose proof (wrI A W) as CI.
    (first [ pose proof ((rk_stats A v [] AR)) as dR_8; dex3 dR_8 as statv rf rfd; dand4 dR_8 as RFR RFDR STA TRF | pose proof ((rk_stats A v [] AR)) as dR_8; dand7 dR_8 as statv rf rfd RFR RFDR STA TRF | destruct (rk_stats A v [] AR) as (statv & rf & rfd & RFR & RFDR & STA & TRF) ]).
    pose proof (ev_wf A v [] c k n _ _ _ AR W L') as WE. pose proof (ev_carved A v [] c k n _ _ _ AR W L') as CVe.
    (first [ pose proof ((rk_line A v [] AR CI c ltac:(exact (proj1 CVe)))) as dR_9; dex1 dR_9 as ks; dand7 dR_9 as LKS KSM KSF KLE KRG KND LINE | pose proof ((rk_line A v [] AR CI c ltac:(exact (proj1 CVe)))) as dR_9; dand8 dR_9 as ks LKS KSM KSF KLE KRG KND LINE | destruct (rk_line A v [] AR CI c ltac:(exact (proj1 CVe))) as (ks & LKS & KSM & KSF & KLE & KRG & KND & LINE) ]).
    pose proof (ek_geo A v [] c k n AR WE) as G.
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (RENT i _ (Nat.le_refl i) NTH) as LE.
    (first [ pose proof ((ek_cells A v [] c k n AR WE LE)) as dR_11; dex2 dR_11 as b1 ctxw; dand10 dR_11 as B1R HDR CTXW MAG SHC SHQ QL SHA R88 MP | pose proof ((ek_cells A v [] c k n AR WE LE)) as dR_11; dand12 dR_11 as b1 ctxw B1R HDR CTXW MAG SHC SHQ QL SHA R88 MP | destruct (ek_cells A v [] c k n AR WE LE) as (b1 & ctxw & B1R & HDR & CTXW & MAG & SHC & SHQ & QL & SHA & R88 & MP) ]).
    pose proof (ek_slot v (a_sb A) (batch_addr (a_sb A) b0) (ba_entries b0) i (batch_bytes b0) i _ RBAT (Nat.le_refl i) NTH LEN) as SLOT. cbn [qe_chunk qe_n] in SLOT.
    pose proof (batch_known A v [] AR (BA (ba_idx b0) (QE (ChP (CP c k)) n :: skipn (S i) (ba_entries b0))) (head_in A _ _ more W L')) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR (ba_idx b0) KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_region_facts A v [] AR c (proj1 CVe))) as dR_13; dand7 dR_13 as RGF1 RGF2 RGF3 RGF4 RGF5 RGF6 RGF7 | destruct (rk_region_facts A v [] AR c (proj1 CVe)) as (RGF1 & RGF2 & RGF3 & RGF4 & RGF5 & RGF6 & RGF7) ]).
    (first [ pose proof ((max_count_range c (proj1 CVe))) as dR_14; dand3 dR_14 as MCR0 MCE RFR0 | pose proof (max_count_range c (proj1 CVe)) as (MCR0 & MCE & RFR0) ]). set (h := refill_count c) in *.
    assert (HSH : Z.shiftr (max_count c) 1 = h) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; clear -MCE; rewrite MCE; rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
    (first [ pose proof ((rk_region A v [] AR c 0%nat (proj1 CVe) ltac:(pose proof (rk_region_facts A v [] AR c (proj1 CVe)) as (_ & _ & _ & _ & RG5' & _); clear -RG5'; cbn [Z.of_nat]; lia))) as dR_15; dex4 dR_15 as na nfs v88 junk0; dand8 dR_15 as RMX RNF RMFA RMU RNA RNFS _ _ | pose proof ((rk_region A v [] AR c 0%nat (proj1 CVe) ltac:(pose proof (rk_region_facts A v [] AR c (proj1 CVe)) as (_ & _ & _ & _ & RG5' & _); clear -RG5'; cbn [Z.of_nat]; lia))) as dR_15; dand12 dR_15 as na nfs v88 junk0 RMX RNF RMFA RMU RNA RNFS _ _ | destruct (rk_region A v [] AR c 0%nat (proj1 CVe) ltac:(pose proof (rk_region_facts A v [] AR c (proj1 CVe)) as (_ & _ & _ & _ & RG5' & _); clear -RG5'; cbn [Z.of_nat]; lia)) as (na & nfs & v88 & junk0 & RMX & RNF & RMFA & RMU & RNA & RNFS & _ & _) ]).
    pose proof (rk_CPMH A v [] AR) as CPMH. pose proof (rk_CGCF A v [] AR) as CGCF. pose proof (rk_CDMP A v [] AR) as CDMP.
    assert (NOFIT : rg_mapped_fa (a_reg A c) < 4 * (Z.of_nat (length (rg_free (a_reg A c))) + h)).
    { clear -NOROOM MCE RFR0. unfold h in *. rewrite MCE in NOROOM. replace (2 * refill_count c / 2) with (refill_count c) in NOROOM by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity). exact NOROOM. }
    pose proof (rk_CITV A v [] AR) as CITV.
    (first [ pose proof ((wtR A (proj1 AR))) as dR_17; dand3 dR_17 as WR1 _ _ | destruct (wtR A (proj1 AR)) as (WR1 & _ & _) ]). (first [ pose proof ((WR1 c (proj1 CVe))) as dR_18; dand12 dR_18 as _ _ _ _ _ _ _ _ _ _ _ CAP | destruct (WR1 c (proj1 CVe)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CAP) ]). cbv zeta in CAP. pose proof (wfr_fa_cap A W c (proj1 CVe)) as [CAPN AUB].   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (head_in A _ _ more W L') as HIN.
    assert (NEhb : ChP (CP kQuarantineBatchClass (ba_idx b0)) <> ChP (CP c k)).
    { intros E. exact (quar_not_batch A v [] AR _ _ (ev_in A c k n _ _ _ W L') HIN (eq_sym E)). }
    pose proof (carved_disjoint A v [] AR _ _ (batch_carved A v [] AR _ HIN) CVe NEhb) as Dbp. cbn [chunk_lo chunk_hi alloc_beg ba_idx] in Dbp.
    (first [ dand25 G as Gcr Gcc Gnr Gk Grz Grzm Gu1 Gu2 Gu3 Gfit Gcsr Gcm Gpe Gka Gam Gmk Gplo Gphi Gpm Gsbm Guo Gho Gab Gclo Gchi | destruct G as (Gcr & Gcc & Gnr & Gk & Grz & Grzm & Gu1 & Gu2 & Gu3 & Gfit & Gcsr & Gcm & Gpe & Gka & Gam & Gmk & Gplo & Gphi & Gpm & Gsbm & Guo & Gho & Gab & Gclo & Gchi) ]).
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    pose proof MCR0 as MCR. pose proof (class_size_mod32 c Gcr) as CS32.
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *. set (cnt := Z.of_nat (length (ba_entries b0))) in *.
    set (pp := chunk_addr sb c k) in *. set (mh := pp + rz_size n - 16) in *. set (fac_ := free_array_of sb c) in *.
    set (cntc := Z.of_nat (length (pk_chunks (a_cache A c)))) in *.
    set (kk := k * class_size c / kCompactPtrScale).
    set (nf := Z.of_nat (length (rg_free (a_reg A c)))) in *. set (mfa := rg_mapped_fa (a_reg A c)) in *. set (Ra := ri + 128 * c) in *.
    set (nm := round_up (4 * (nf + h)) kFaMap). set (fe := sb + c * 4294967296 + kFreeArrayOffset + mfa).
    set (Q := fun ms' : machine_state => exists (t0 t1 t2 a6 t3 t4 t5 t6 : word) (lscr scr2 scr3 scr4 : list byte) (m' : mem),
           ms' = MSsvc (mkR (wz mapfixed_resume) (wz (dsp + -48 + -64 + -128 + -48 + -128)) gp (cl_tp LPA) t0 t1 t2 (wz (nm - mfa)) (wz 1)
                            (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                            (wz fe) (wz efas_name) (wz PSC) (wz h) (wz (thr + 208 + 80 * c + 16 + 4 * (max_count c - h))) (wz (nf + h)) (wz 2305843009213693952)
                            (wz fac_) (wz 1152921504607895551) (wz kMutexWriter) t3 t4 t5 t6)
                       F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs) /\
           rw_cells rsegs m' dsp (dorec_fr thr scr) /\
           rw_cells rsegs m' (b + 24 + 8 * Z.of_nat i) [C8 (wz (hdr_of sb (ChP (CP c k)) n))] /\
           (rz_size n - 16 = 0 \/ rw_cells rsegs m' pp [C8 (wz 0)]) /\
           rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi (user_size n))); C4 (wz (user_size n))] /\
           bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (round_up (user_size n) 8 / 8))) /\
           rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + user_size n))] /\
           rw_cells rsegs m' (dsp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1558) (wz T) (wz dorec_retpc)) /\
           rw_cells rsegs m' (dsp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)) /\
           rw_cells rsegs m' (dsp + -48 + -64 + -128)
                 (rta_frame scr2 (Ra + 8) s11 s10 (wz (16 + Z.of_nat i)) (wz (cnt + 16)) (wz (b + 152 + 8 * Z.of_nat i)) (wz cnt) (wz (2^37)) (wz pp) (wz c) (wz 0xb1558) (wz (thr + 208)) (wz (thr + 208 + 80 * c)) (wz lcdrain_ret)) /\
           rw_cells rsegs m' (dsp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (dsp + -48 + -56)) (wz c) (wz nf) (wz Ra) (wz rta_efasret)) /\
           rw_cells rsegs m' (dsp + -48 + -64 + -128 + -48 + -128) (mapcb_frame scr4 (wz 0xb1558) (wz Ra) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) /\
           rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (wz (max_count c - h)); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s ks)] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv] /\
           rw_cells rsegs m' Ra [C8 (wz kMutexWriter)] /\ rw_cells rsegs m' (Ra + 16) [C8 (wz nf)] /\ rw_cells rsegs m' (Ra + 24) [C8 (wz mfa)] /\
           rw_cells rsegs m' (Ra + 80) [C8 nfs; C8 v88] /\
           munch [(dsp - 688, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                  (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (Ra, Ra + 8)] v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (dsp + -48 + -64 + -128 + -48 + -128)).
    unfold it_cfgG. fold sb. fold b cnt.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (iter_prim_drainmap_pre2 gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := 512 * ba_idx b0) (c := c) (idx := k) (d := rz_size n - 16) (mu := rg_mapped_user (a_reg A c)) (n := user_size n) (b1 := b1)
             (rf := rf) (rfd := rfd) (maxc := max_count c) (k := kk) (old := fd8 ((user_size n + 7) / 8)) (ks := ks) (statv := statv)
             (pw := wz (hdr_of sb (ChP (CP c k)) n)) (mh := mh) (nf := nf) (mfa := mfa) (nfs := nfs) (v88 := v88).
      all: rewrite ?HSH.
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
      all: cycle -1.
      1: { intros t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m' DF' SL' MU' MG' HD' SH' TF' LF' DRF' RTF' EFF' MFF' LN' ST' RX' RNF' RMFA' RNFS' MUN WM' MI' STK'.
           subst Q. first [ hotw_ex13 t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m' | exists t0'', t1'', t2'', a6'', t3'', t4'', t5'', t6'', lscr, scr2, scr3, scr4, m' ].
           split; [reflexivity|]. repeat (split; [assumption|]). exact STK'. }
      all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold pa_tsd; clear; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | unfold cnt; clear -LEN; unfold kQuarantineBatchCount in LEN; lia
                 | clear -SBRI RHI; lia
                 | clear -KB0 KBH; lia
                 | pose proof (nth_error_Some_lt _ _ _ NTH) as IL; unfold cnt; clear -IL; lia
                 | unfold mh, pp in *; rewrite Gho; rewrite unsigned_lit; [reflexivity| clear -Gplo Gphi Grz Gfit Gu1 CE; kung_all; pose proof (round_up_ge (user_size n) 8 ltac:(lia)); lia]
                 | unfold mh, pp in *; clear -Gpe; lia
                 | pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU; clear -RU Grz Gfit Gu1; lia
                 | clear -Grzm; lia
                 | clear -Gk; lia
                 | clear -Gka Gam; lia
                 | clear -Gmk Gam Gka Gk Gcsr; kung_all; nia
                 | unfold kk; unfold kCompactPtrScale; clear -Gcm Gk; nia
                 | clear -Gu1 Gu3 Gnr; unfold kMaxPrimaryUser in *; lia
                 | unfold mh, pp in *; clear -Gfit Gphi CE; lia
                 | unfold cntc; clear -ROOM; lia
                 | clear -MCR; lia
                 | clear -MCE RFR0; unfold h; lia
                 | rewrite LJ; clear; rewrite Z2Nat.id by lia || idtac; lia
                 | unfold nf; clear; lia
                 | clear -RGF5 CAPN RFR0; unfold nf, mfa, h in *; kung_all; lia
                 | clear -NOFIT MCE RFR0; unfold nf, mfa, h in *; lia
                 | rewrite <- FULL at 1; exact LINE
                 | clear -RGF3; unfold mfa; kung_all; lia
                 | clear -Gmk; kung_all; lia
                 | clear -NOFIT; unfold nf, h in *; lia
                 | clear -RGF4; unfold mfa; exact RGF4
                 | exact cbrec_prim_ok
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr1 md1 HQ HI1 SB1 Hcl1.
    (first [ dex13 HQ as t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m1; dand22 HQ as -> DF1 SL1 MG1 HD1 SH1 TF1 LF1 DRF1 RTF1 EFF1 MFF1 LN1 STA1 RX1 RNF1 RMFA1 RNFS1 MUN1 WM1 MI1 STK1 | dand35 HQ as t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m1 -> DF1 SL1 MG1 HD1 SH1 TF1 LF1 DRF1 RTF1 EFF1 MFF1 LN1 STA1 RX1 RNF1 RMFA1 RNFS1 MUN1 WM1 MI1 STK1 | destruct HQ as (t0'' & t1'' & t2'' & a6'' & t3'' & t4'' & t5'' & t6'' & lscr & scr2 & scr3 & scr4 & m1 & -> & DF1 & SL1 & MG1 & HD1 & SH1 & TF1 & LF1 & DRF1 & RTF1 & EFF1 & MFF1 & LN1 & STA1 & RX1 & RNF1 & RMFA1 & RNFS1 & MUN1 & WM1 & MI1 & STK1) ]).
    rewrite unrestrict_MSsvc. cbn [ms_mem MSsvc] in Hcl1.
    pose proof (same_but_materialized_frame _ _ SB1) as FRM1.
    assert (HH1 : m_halted md1 = None).
    { (first [ dand18 FRM1 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HLT. }
    assert (LED1 : aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md1) by exact (aledger_sbm _ _ _ _ md md1 SB1 LED).
    assert (COV1 : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md1)) by (rewrite (same_but_materialized_vmmaps _ _ SB1); exact COV).
    assert (TOP1 : alloc_top (m_vmmaps md1) = alloc_ceiling) by (rewrite (same_but_materialized_vmmaps _ _ SB1); exact CEI).
    (* [comment removed for export] *)
    set (len := nm - mfa) in *.
    pose proof (free_cached_count A c W Gcr) as FCC. fold nf cntc in FCC.
    (first [ pose proof ((WR1 c (proj1 CVe))) as dR_23; dand12 dR_23 as _ _ _ _ _ _ _ _ _ _ MUCAP _ | destruct (WR1 c (proj1 CVe)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MUCAP & _) ]).
    (* [comment removed for export] *)
    assert (NFH26 : nf + h <= 112993196).
    { assert (CC26 : carved_count A c <= 112993196).
      { unfold carved_count, carved_count_. apply Z.div_le_upper_bound; [clear -Gcsr; lia|]. clear -AUB Gam Gcsr. unfold kAuCap in AUB. nia. }
      clear -FCC CC26 FULL MCE RFR0. unfold h in *. lia. }
    assert (NMF : 4 * (nf + h) <= nm /\ nm < 4 * (nf + h) + kFaMap /\ nm mod kFaMap = 0 /\ nm <= 2^29 - 2^26).
    { unfold nm. pose proof (round_up_ge (4 * (nf + h)) kFaMap ltac:(unfold kFaMap; lia)) as R1. pose proof (round_up_lt (4 * (nf + h)) kFaMap ltac:(unfold kFaMap; lia)) as R2.
      pose proof (round_up_mod (4 * (nf + h)) kFaMap ltac:(unfold kFaMap; lia)) as R3.
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. clear -R2 R3 NFH26. unfold kFaMap in *. lia. }
    (first [ dand4 NMF as NM1 NM2 NM3 NM4 | destruct NMF as (NM1 & NM2 & NM3 & NM4) ]).
    assert (LENF : 0 < len /\ len mod 4096 = 0 /\ len mod kFaMap = 0).
    { unfold len. split; [clear -NM1 NOFIT; lia|]. unfold kFaMap, kFreeArrayMapSize in *. clear -NM3 RGF4. split; lia. }
    (* [comment removed for export] *)
    set (es' := skipn (S i) (ba_entries b0)) in *.
    set (hN := Z.to_nat h) in *.
    set (out := drain_out (pk_chunks (a_cache A c)) hN).
    set (cache' := recp_cache (a_cache A) c k).
    set (reg' := recp_reg (a_reg A) (a_cache A) c k nm).
    set (A' := recA' A reg' cache' (BA (ba_idx b0) es' :: more)).
    assert (RGC : reg' c = reg_return (a_reg A c) out nm).
    { unfold reg', recp_reg, reg_set, cache_push_list. fold cntc. rewrite FULL, Z.eqb_refl, Z.eqb_refl. cbn [snd].
      replace (max_count c / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (RGO : forall c', c' <> c -> reg' c' = a_reg A c').
    { intros c' NE. unfold reg', recp_reg, reg_set. fold cntc. rewrite FULL, Z.eqb_refl. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (CAE : pk_chunks (cache' c) = drain_keep (pk_chunks (a_cache A c)) hN ++ [k]).
    { unfold cache', recp_cache, cache_set, cache_push_list. rewrite Z.eqb_refl. fold cntc. rewrite FULL, Z.eqb_refl. cbn [fst pk_chunks].
      replace (max_count c / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (CAO : forall c', c' <> c -> cache' c' = a_cache A c').
    { intros c' NE. unfold cache', recp_cache, cache_set. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (RCX : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (a_reg A c) + len).
    { rewrite RGC, reg_return_mapped_user, reg_return_mapped_fa. split; [reflexivity| unfold len, mfa; clear; lia]. }
    assert (LEN0 : 0 <= len) by (clear -LENF; lia).
    pose proof (gw_hull_le A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) LEN0 RGO RCX) as HLE.
    pose proof (gw_lhull_le A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) LEN0 RGO RCX) as LHLE.   (* [comment removed for export] *)
    pose proof (gw_eager A c reg' cache' (BA (ba_idx b0) es' :: more) len Gcr RGO RCX) as EAGER.
    change (mkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with A' in HLE, LHLE, EAGER.
    assert (HLEN : (hN <= length (pk_chunks (a_cache A c)))%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    assert (OUTL : length out = hN) by (unfold out; apply drain_out_length; exact HLEN).
    assert (W' : WFR A').
    { pose proof (WFR_prim A _ c k n nm _ more W L') as X. apply X. intros _. unfold nf, mfa, h in *. clear -NM1 NM2 NM3 NM4 FCC FULL NOFIT RGF3 RGF4 CAP Gam Gka Gk Gcsr MCE RFR0.
      split; [rewrite MCE; replace (2 * refill_count c / 2) with (refill_count c) by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact NM1|].
      split; [lia|]. split; [unfold kFreeArraySize; lia|]. split; [unfold kFreeArrayMapSize, kFaMap in *; exact NM3|]. split; [clear -NM2 FCC FULL MCE RFR0; unfold carved_count, carved_count_, kFreeArrayMapSize, kFaMap in *; lia|]. intros MU0. nia. }
    (* [comment removed for export] *)
    assert (FEE : fe = fac_ + mfa) by (unfold fe, fac_, free_array_of, region_beg, sb; kung_all; lia).
    assert (RANGE : a_sb A <= fe /\ fe + len <= a_sb A + kSpaceSize + 4096 /\ fe mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len).
    { unfold fe, len. fold sb. clear -Gcr SBAL RGF3 RGF4 NM4 NM1 NOFIT LENF. unfold len in LENF. kung_all. unfold kFreeArrayMapSize in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (QB1 : q_bytes (a_qlimbo A) <= kLimboMax) by (unfold kLimboMax; exact QB).
    pose proof (wfr_budget_room A W EXTRA QB1) as ROOM0. unfold ABudget.kBudgetRoom in ROOM0.
    assert (BR : pa_eager A + len + hull_bytes (pa_lhull A) <= p_tlim (a_pl A)).   (* [comment removed for export] *)
    { unfold pa_eager. unfold len. clear -ROOM0 NM4 RGF3. lia. }
    pose proof (cr_gate A md1 fe len W TOP1 RANGE) as GATE.
    pose proof (cr_contained A md1 fe len W LED1 COV1 RANGE) as CONT.
    pose proof (cr_budget A md1 fe len W LED1 HI1 COV1 TOP1 RANGE BR) as BUD.
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A0E : ms_gpr ms1 0 = wz fe) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms1 1 = wz len) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (LENU : bv_unsigned (wz len) = len) by (apply unsigned_lit; unfold len; clear -LENF NM4 RGF3; unfold len in LENF; lia).
    assert (PRU : page_round_up_Z (bv_unsigned (ms_gpr ms1 1)) = len).
    { rewrite A1E, LENU. unfold page_round_up_Z, page_size. (first [ dand3 LENF as L0 L1 _ | destruct LENF as (L0 & L1 & _) ]). clear -L0 L1.
      replace ((len + 4096 - 1) / 4096 * 4096) with len; [reflexivity|]. pose proof (Z_div_mod_eq_full len 4096) as E. rewrite L1 in E.
      replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia. }
    (* [comment removed for export] *)
    pose proof (rk_CML A v [] AR) as CML. pose proof (rk_SEAL A v [] AR) as SEAL. pose proof (rk_DYG A v [] AR) as DYG. pose proof (rk_DYF A v [] AR) as DYF.
    pose proof (aobj_facts _ _ PT) as PTF. pose proof (aobj_facts _ _ PC) as PCF.
    assert (PPB : sb <= pp /\ pp + class_size c <= sb + c * 4294967296 + kFreeArrayOffset /\ pp <= mh /\ mh + 16 + round_up (user_size n) 8 <= pp + class_size c /\ 32 <= class_size c /\ 0 <= round_up (user_size n) 8).
    { pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU0. unfold mh, pp in *. clear -Gpe Gka Gam Gmk Gcr Gcsr Gk Grz Gfit RU0 Gu1. kung_all. nia. }
    assert (SHCH : kLowShadowMapBeg <= sh (mh + 16) /\ sh (mh + 16) + round_up (user_size n) 8 / 8 <= kHighMemBeg).
    { pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU0. unfold sh.
      assert (Q1 : kHighMemBeg / 8 <= (mh + 16) / 8) by (apply Z.div_le_mono; [clear; lia| clear -PPB SBLO; lia]).
      assert (Q2 : (mh + 16) / 8 + round_up (user_size n) 8 / 8 <= 2^44).
      { assert (E8 : round_up (user_size n) 8 = 8 * (round_up (user_size n) 8 / 8)) by (pose proof (round_up_mod (user_size n) 8 ltac:(lia)) as RM; pose proof (Z_div_mod_eq_full (round_up (user_size n) 8) 8) as X; rewrite RM in X; clear -X; lia).
        assert (Q3 : (mh + 16) / 8 <= (2^47 - round_up (user_size n) 8) / 8) by (apply Z.div_le_mono; [clear; lia| clear -PPB Gphi CE; lia]).
        rewrite E8 in Q3 at 1. replace (2^47 - 8 * (round_up (user_size n) 8 / 8)) with ((2^44 - round_up (user_size n) 8 / 8) * 8) in Q3 by (clear; lia). rewrite Z.div_mul in Q3 by (clear; lia). clear -Q3. lia. }
      assert (Q4 : 0 <= round_up (user_size n) 8 / 8) by (apply Z.div_pos; [clear -RU0 Gu1; lia| clear; lia]).
      change (kHighMemBeg / 8) with 0x2000ffff000 in Q1. clear -Q1 Q2 Q4. kung_all. lia. }
    set (W1 := [(dsp - 688, dsp); (pp, pp + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + round_up (user_size n) 8 / 8);
                (thr + 2840, thr + 2856); (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (Ra, Ra + 8)]) in *.
    assert (DJ1img : forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from W1 a l).
    { intros a l A1 A2. unfold W1. cbn [disjoint_from]. unfold Ra. clear -A1 A2 PTF PPB SBLO SHCH Gcr RLO CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (DJ1ctx : disjoint_from W1 (p_ctx (a_pl A) + 152) 8).
    { unfold W1. cbn [disjoint_from]. unfold Ra, apart in *. fold sb in SP6. clear -PCF PCC PPB SHCH SP3 SP5 SP6 Gcr CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    pose proof (thread_cells_munch W1 v m1 _ _ _ _ TC MUN1 eq_refl ltac:(unfold pa_tsd; clear; lia) DJ1img DJ1ctx) as TC1.
    pose proof (poison_consts_munch W1 v m1 PCo MUN1 DJ1img) as PCo1.
    assert (CGCF1 : ro_cells rsegs m1 0xa8b60 [C8 (wz CF)]) by (eapply ro_cells_transport; [exact CGCF| exact MUN1| apply DJ1img; cbn; lia]).
    assert (CML1 : ro_cells rsegs m1 (CF + 144) [C8 (wz 0)]) by (eapply ro_cells_transport; [exact CML| exact MUN1| apply DJ1img; unfold CF; cbn; lia]).
    assert (SEAL1 : ro_cells rsegs m1 0xa8bb0 [C8 (wz 1)]) by (eapply ro_cells_transport; [exact SEAL| exact MUN1| apply DJ1img; cbn; lia]).
    assert (DYG1 : ro_cells rsegs m1 0xa8bb8 [C8 (wz 0x1466dc)]) by (eapply ro_cells_transport; [exact DYG| exact MUN1| apply DJ1img; cbn; lia]).
    assert (DYF1 : ro_cells rsegs m1 0x1466dc [C4 (wz 0)]) by (eapply ro_cells_transport; [exact DYF| exact MUN1| apply DJ1img; cbn; lia]).
    assert (CSB1 : ro_cells rsegs m1 0xb1578 [C8 (wz sb)]) by (eapply ro_cells_transport; [exact CSB| exact MUN1| apply DJ1img; cbn; lia]).
    assert (CRI1 : ro_cells rsegs m1 RI_PTR [C8 (wz ri)]) by (eapply ro_cells_transport; [exact CRI| exact MUN1| apply DJ1img; unfold RI_PTR; cbn; lia]).
    assert (CITV1 : ro_cells rsegs m1 0xb1580 [C4 (wz 4294967295)]) by (eapply ro_cells_transport; [exact CITV| exact MUN1| apply DJ1img; cbn; lia]).
    assert (RMU1 : ro_cells rsegs m1 (Ra + 48) [C8 (wz (rg_mapped_user (a_reg A c)))]).
    { eapply ro_cells_transport; [exact RMU| exact MUN1|]. unfold W1. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold Ra, apart in *. fold sb in SP2, SP4.
      clear -PTF PPB SHCH SP1 SP2 Gcr RLO RHI RI0 CEIL LOW CE SPR. fold sb in RI0. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    eapply (srz_mmap_fixed_rw_contained_nf rsegs ms1 md1 (wz 222) (wz 50) TS HH1 eq_refl eq_refl).
    - unfold mmap_fixed_args. subst ms1. rewrite !ms_gpr_MSsvc. simp_regs. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      intros E. apply (f_equal bv_unsigned) in E. rewrite LENU, unsigned_lit in E by lia. clear -E LENF. lia.
    - exact fixed_rw_shape_plain.
    - rewrite PRU, A0E. exact GATE.
    - unfold fixed_contained. rewrite PRU, A0E. exact CONT.
    - rewrite PRU, A0E. exact BUD.
    - (* [comment removed for export] *)
      rewrite !PRU, !A0E. subst ms1.
      rewrite advance_apply_MSsvc, mkR_set_a0, lit_add_lit. change (mmap_ecall_pc + 4) with mmap_after_pc.
      cbn [apply_writes apply_unmaps].
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with m end.
      set (M1 := munrestrict (hidc (pa_hull A)) m m1).
      set (M2 := apply_zeros M1 [(wz fe, wz len)]).
      set (md2 := commit_model (wz 50) (wz fe) (wz len) false md1).
      set (m2 := mrestrict (hidc (pa_hull A')) M2).
      (first [ pose proof ((rk_region_facts A v [] AR c (proj1 CVe))) as dR_27; dand4 dR_27 as _ _ RG3' _ | pose proof (rk_region_facts A v [] AR c (proj1 CVe)) as (_ & _ & RG3' & _) ]).
      assert (FEB : kHighMemBeg <= fe /\ fe + len <= alloc_ceiling /\ fe + len <= 2^47 /\ fe + len <= sb + kSpaceSize).
      { (first [ dand3 RANGE as R1 R2 _ | destruct RANGE as (R1 & R2 & _) ]). pose proof (region_piece_boundsT A c (proj1 AR) Gcr) as RB. cbv zeta in RB. (first [ dand9 RB as _ _ _ _ _ _ R7 R8 _ | destruct RB as (_ & _ & _ & _ & _ & _ & R7 & R8 & _) ]).
        fold sb in R1, R2, R7, R8. unfold fe, len, region_beg in *. clear -R1 R2 R7 R8 SBLO CE NM4 Gcr. kung_all. lia. }
      assert (ZSPEC : forall x : word, M2 x = if in_range fe len x then Some (Z_to_bv 8 0) else M1 x).
      { intros x. subst M2. change (Z_to_bv 64 fe) with (wa fe). apply apply_zeros_spec; [clear -FEB LENF; kung_all; lia| clear -LENF FEB; kung_all; lia| clear -FEB LENF; lia]. }
      (* [comment removed for export] *)
      assert (FE8 : fe mod 8 = 0 /\ len mod 8 = 0) by ((first [ dand5 RANGE as _ _ R3 R4 _ | destruct RANGE as (_ & _ & R3 & R4 & _) ]); clear -R3 R4; lia).
      set (sfe := sh fe) in *.
      assert (SFE : sfe = fe / 8 + kShadowOffset) by (unfold sfe, sh; reflexivity).
      (* [comment removed for export] *)
      assert (DMF : len mod kFreeArrayMapSize = 0) by (unfold kFreeArrayMapSize, kFaMap in *; exact (proj2 (proj2 LENF))).
      assert (FAE2 : region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) = fe) by (unfold fe, region_beg, sb, mfa; kung_all; lia).
      assert (NEWH : forall x, in_hullb (pa_hull A') x = true -> in_hullb (pa_hull A) x = false -> (fe <= x < fe + len) \/ (sfe <= x < sfe + len / 8)).
      { intros x H1 H0. destruct (gw_hull_cases A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) Gcr LEN0 DMF RGO RCX x H1) as [O|[N|N]].
        - rewrite O in H0. discriminate.
        - left. rewrite FAE2 in N. exact N.
        - right. rewrite FAE2 in N. exact N. }
      set (Wg := [(fe, fe + len); (sfe, sfe + len / 8)]).
      assert (MU12 : munch Wg m1 m2).
      { apply (restrict_grow_munch_le (pa_hull A) (pa_hull A') Wg HLE) with (full := m).
        - intros x H1 H0 OUT. cbn [outside Wg] in OUT. (first [ dand3 OUT as O1 O2 _ | destruct OUT as (O1 & O2 & _) ]). destruct (NEWH x H1 H0) as [N|N]; [exact (O1 N)| exact (O2 N)].
        - exact Hcl1.
        - intros a OUT. rewrite ZSPEC. cbn [outside Wg] in OUT. destruct OUT as (O1 & _). unfold in_range.
          replace ((fe <=? bv_unsigned a) && (bv_unsigned a <? fe + len)) with false; [reflexivity|].
          symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (bv_unsigned a) fe) as [l|g]; [left; apply Z.leb_gt; exact l| right; apply Z.ltb_ge; clear -O1 g; lia]. }
      assert (WM12 : wmono rsegs m1 m2).
      { apply (restrict_grow_wmono_le (pa_hull A) (pa_hull A') HLE m1 M2 Hcl1).
        intros a V0 NZ. rewrite ZSPEC. destruct (in_range fe len a); [discriminate|]. unfold M1, munrestrict. rewrite V0. exact NZ. }
      assert (Hcl2 : forall a, hidc (pa_hull A') a = true -> m2 a = None) by (intros a Ha; unfold m2, mrestrict; rewrite Ha; reflexivity).
      assert (MI2 : mem_inv rsegs m2).
      { intros a bb Hab. unfold m2, mrestrict in Hab. destruct (hidc (pa_hull A') a) eqn:V1; [discriminate|]. rewrite ZSPEC in Hab.
        destruct (ro_addr rsegs a) eqn:RO; [| reflexivity]. exfalso. pose proof (proj1 (pa_ro_addr_iff _) RO) as ROr.
        destruct (in_range fe len a) eqn:IR.
        - unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. clear -ROr I1 FEB. kung_all. lia.
        - unfold M1, munrestrict in Hab. destruct (hidc (pa_hull A) a) eqn:V0; [| rewrite (MI1 a bb Hab) in RO; discriminate].
          unfold hidc in V0, V1. apply negb_true_iff in V0. apply negb_false_iff in V1.
          destruct (NEWH _ V1 V0) as [N|N]; [clear -N ROr FEB; kung_all; lia|].
          pose proof (Z.div_pos fe 8 ltac:(clear -FEB; kung_all; lia) ltac:(lia)) as P. clear -N ROr SFE P. unfold kShadowOffset in *. lia. }
      (* [comment removed for export] *)
      assert (HH2 : m_halted md2 = None) by (unfold md2; rewrite commit_model_halted; exact HH1).
      assert (QB' : q_bytes (a_qlimbo A') <= kLimboMax).
      { unfold A', recA', kLimboMax. cbn [a_qlimbo]. rewrite L' in QB. rewrite !q_bytes_cons, !batch_bytes_ebytes in QB |- *. cbn [ba_entries] in QB |- *. rewrite ebytes_cons in QB.
        pose proof (user_size_pos n ltac:(clear -Gnr; lia)) as (U1 & _). unfold qe_bytes in QB at 1. cbn [qe_n] in QB. clear -QB U1. lia. }
      assert (EXTRA' : wf_extra LPA pa_site_pcs (a_pl A')) by exact EXTRA.
      pose proof (wfr_budget_room A' W' EXTRA' QB') as ROOM'. unfold ABudget.kBudgetRoom in ROOM'. change (p_tlim (a_pl A')) with (p_tlim (a_pl A)) in ROOM'.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (LZ2 : lazy_free (m_vm_lazy md2) (region_beg (a_sb A) c + kFreeArrayOffset + mfa) (region_beg (a_sb A) c + kFreeArrayOffset + mfa + len)).
      { pose proof (cr_lzfree_new A md1 fe len W HI1 RANGE) as X. fold md2 in X.
        replace (region_beg (a_sb A) c + kFreeArrayOffset + mfa) with fe by (unfold fe, region_beg, sb, a_sb; kung_all; clear; lia). exact X. }
      assert (LED2' : aledger_ AL_pboth (a_pl A) reg' (a_sec A) md2).
      { pose proof (cr_ledger A md1 fe len W LED1 HI1 COV1 RANGE) as L2. fold md2 in L2. exact (gw_aledger A c reg' len Gcr RGO RCX md2 L2 LZ2). }
      assert (HI2 : MInv (pa_hull A') (pa_lhull A') (pa_eager A') md2).
      { pose proof (cr_minv A md1 fe len W LED1 HI1 COV1 TOP1 RANGE BR) as X0. fold md2 in X0.
        pose proof (cr_limit A md1 fe len LED1) as LIM2. fold md2 in LIM2.
        apply (MInv_hull_mono (pa_hull A) (pa_lhull A) (pa_hull A') (pa_lhull A') (pa_eager A + len) (pa_eager A') md2 X0 LHLE).
        - intros l0 h0 Hin. right. exact (ahull_coverT A' md2 (WFT_of_WFR A' W') LED2' l0 h0 Hin).
        - rewrite EAGER. clear. lia.
        - rewrite LIM2. unfold pa_eager at 1. clear -ROOM'. lia. }
      (* [comment removed for export] *)
      assert (SHB : kLowShadowMapBeg <= sfe /\ sfe + len / 8 <= kHighMemBeg /\ sfe + len / 8 = (fe + len) / 8 + kShadowOffset).
      { destruct FE8 as [F8 L8]. (first [ dand3 FEB as B1 B2 B3 | destruct FEB as (B1 & B2 & B3) ]). rewrite SFE.
        assert (E : (fe + len) / 8 = fe / 8 + len / 8).
        { pose proof (Z_div_mod_eq_full fe 8) as X1. rewrite F8 in X1.
          replace (fe + len) with (fe / 8 * 8 + len) by (clear -X1; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
        rewrite E. assert (Q1 : fe / 8 + len / 8 <= 2^44) by (rewrite <- E; apply Z.div_le_upper_bound; [clear; lia| clear -B3; lia]).
        assert (Q2 : kHighMemBeg / 8 <= fe / 8) by (apply Z.div_le_mono; [clear; lia| exact B1]).
        assert (Q3 : 0 <= len / 8) by (apply Z.div_pos; [clear -LENF; lia| clear; lia]).
        change (kHighMemBeg / 8) with 0x2000ffff000 in Q2. clear -Q1 Q2 Q3. kung_all. lia. }
      assert (DJ12 : forall a l, (a + l <= fe \/ fe + len <= a) -> (a + l <= sfe \/ sfe + len / 8 <= a) -> disjoint_from Wg a l).
      { intros a l D1 D2. unfold Wg. cbn [disjoint_from]. split; [exact D1|]. split; [exact D2| exact I]. }
      assert (DJstk : forall a l, alloc_ceiling <= a -> disjoint_from Wg a l).
      { intros a l Ha. apply DJ12; right; [clear -Ha FEB; lia| clear -Ha SHB CE; kung_all; lia]. }
      assert (DJthr : forall a l, thr <= a -> a + l <= thr + 4096 -> disjoint_from Wg a l).
      { intros a l H1 H2. (first [ dand3 RANGE as R1 R2 _ | destruct RANGE as (R1 & R2 & _) ]). fold sb in R1, R2. unfold apart in SP4. apply DJ12.
        - clear -H1 H2 R1 FEB SP4. kung_all. lia.
        - clear -H1 H2 PTF SHB. lia. }
      assert (DJri : forall a l, ri <= a -> a + l <= ri + 4096 -> disjoint_from Wg a l).
      { intros a l H1 H2. (first [ dand3 RANGE as R1 R2 _ | destruct RANGE as (R1 & R2 & _) ]). fold sb in R1, R2. apply DJ12; right.
        - clear -H1 FEB RI0. fold sb in RI0. kung_all. lia.
        - clear -H1 SHB RLO. lia. }
      assert (DJimg : forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from Wg a l).
      { intros a l H1 H2. apply DJ12; left; [clear -H2 FEB; kung_all; lia| clear -H2 SHB; kung_all; lia]. }
      (* [comment removed for export] *)
      assert (DJ2ctx : disjoint_from Wg (p_ctx (a_pl A) + 152) 8).
      { destruct RANGE as (R1 & _). fold sb in R1. unfold apart in SP6. fold sb in SP6. apply DJ12.
        - clear -SP6 R1 FEB. kung_all. lia.
        - clear -PCF SHB. lia. }
      pose proof (thread_cells_munch Wg m1 m2 _ _ _ _ TC1 MU12 eq_refl ltac:(unfold pa_tsd; clear; lia) DJimg DJ2ctx) as TC2.
      pose proof (poison_consts_munch Wg m1 m2 PCo1 MU12 DJimg) as PCo2.
      assert (CGCF2 : ro_cells rsegs m2 0xa8b60 [C8 (wz CF)]) by (eapply ro_cells_transport; [exact CGCF1| exact MU12| apply DJimg; cbn; lia]).
      assert (CML2 : ro_cells rsegs m2 (CF + 144) [C8 (wz 0)]) by (eapply ro_cells_transport; [exact CML1| exact MU12| apply DJimg; unfold CF; cbn; lia]).
      assert (CSB2 : ro_cells rsegs m2 0xb1578 [C8 (wz sb)]) by (eapply ro_cells_transport; [exact CSB1| exact MU12| apply DJimg; cbn; lia]).
      assert (CRI2 : ro_cells rsegs m2 RI_PTR [C8 (wz ri)]) by (eapply ro_cells_transport; [exact CRI1| exact MU12| apply DJimg; unfold RI_PTR; cbn; lia]).
      assert (CITV2 : ro_cells rsegs m2 0xb1580 [C4 (wz 4294967295)]) by (eapply ro_cells_transport; [exact CITV1| exact MU12| apply DJimg; cbn; lia]).
      assert (RMU2 : ro_cells rsegs m2 (Ra + 48) [C8 (wz (rg_mapped_user (a_reg A c)))]).
      { eapply ro_cells_transport; [exact RMU1| exact MU12| apply DJri; unfold Ra; cbn; clear -Gcr; lia]. }
      assert (STK2 : stk rsegs m2 lo (dsp + -48 + -64 + -128 + -48 + -128)) by (eapply (stk_transport_disjoint rsegs); [exact STK1| exact MU12| exact WM12| apply DJstk; exact CEIL]).
      assert (DF2 : rw_cells rsegs m2 dsp (dorec_fr thr scr)) by (eapply rw_cells_transport; [exact DF1| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia]).
      assert (LF2 : rw_cells rsegs m2 (dsp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1558) (wz T) (wz dorec_retpc)))
        by (eapply rw_cells_transport; [exact LF1| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia]).
      assert (DRF2 : rw_cells rsegs m2 (dsp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)))
        by (eapply rw_cells_transport; [exact DRF1| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia]).
      pose proof RTF1 as RTF2. eapply rw_cells_transport in RTF2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      pose proof EFF1 as EFF2. eapply rw_cells_transport in EFF2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      pose proof MFF1 as MFF2. eapply rw_cells_transport in MFF2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      (* [comment removed for export] *)
      assert (FEL : sb + c * 4294967296 + kFreeArrayOffset <= fe /\ fe + len <= sb + c * 4294967296 + 4294967296) by (unfold fe, len; clear -RGF3 NM4; kung_all; lia).
      assert (DJb : forall a l, b <= a -> a + l <= b + 8192 -> disjoint_from Wg a l).
      { intros a l H1 H2. apply DJ12.
        - assert (BE : b = sb + 24 * 2^32 + 16 * (512 * ba_idx b0)) by exact BFORM. clear -H1 H2 BE KB0 KBH FEL FEB Gcr. kung_all. lia.
        - right. assert (BL : kHighMemBeg <= b) by exact BLO. clear -H1 SHB BL. lia. }
      assert (DJp : forall a l, pp <= a -> a + l <= pp + class_size c -> disjoint_from Wg a l).
      { intros a l H1 H2. apply DJ12.
        - left. clear -H2 PPB FEL. lia.
        - right. clear -H1 SHB PPB SBLO. lia. }
      pose proof SL1 as SL2. eapply rw_cells_transport in SL2; [| exact MU12| exact WM12| apply DJb; cbn; pose proof (nth_error_Some_lt _ _ _ NTH) as IL; clear -IL LEN; unfold kQuarantineBatchCount in LEN; lia].
      assert (MG2 : rz_size n - 16 = 0 \/ rw_cells rsegs m2 pp [C8 (wz 0)]).
      { destruct MG1 as [E|C]; [left; exact E| right]. eapply rw_cells_transport; [exact C| exact MU12| exact WM12| apply DJp; cbn; clear -PPB; lia]. }
      pose proof HD1 as HD2. eapply rw_cells_transport in HD2; [| exact MU12| exact WM12| apply DJp; cbn; clear -PPB; lia].
      assert (SHD : sh (mh + 16) + round_up (user_size n) 8 / 8 <= sfe).
      { rewrite SFE. unfold sh. assert (E8 : round_up (user_size n) 8 = 8 * (round_up (user_size n) 8 / 8)) by (pose proof (round_up_mod (user_size n) 8 ltac:(lia)) as RM; pose proof (Z_div_mod_eq_full (round_up (user_size n) 8) 8) as X0; rewrite RM in X0; clear -X0; lia).
        assert (Qd : (mh + 16 + round_up (user_size n) 8) / 8 <= fe / 8) by (apply Z.div_le_mono; [clear; lia| clear -PPB FEL; lia]).
        rewrite E8 in Qd at 1. replace (mh + 16 + 8 * (round_up (user_size n) 8 / 8)) with (round_up (user_size n) 8 / 8 * 8 + (mh + 16)) in Qd by (clear; lia).
        rewrite Z.div_add_l in Qd by (clear; lia). clear -Qd. lia. }
      assert (R8P : 0 <= round_up (user_size n) 8 / 8) by (apply Z.div_pos; [clear -PPB; lia| clear; lia]).
      pose proof SH1 as SH2. eapply bytes_at_transport in SH2; [| exact MU12| rewrite repeat_length, Z2Nat.id by exact R8P; apply DJ12; left; [clear -SHCH FEB; lia| exact SHD]].
      (* [comment removed for export] *)
      pose proof TF1 as TF2. eapply rw_cells_transport in TF2; [| exact MU12| exact WM12| apply DJthr; cbn; clear; lia].
      pose proof LN1 as LN2. eapply rw_cells_transport in LN2; [| exact MU12| exact WM12| apply DJthr; cbn; clear -Gcr; lia].
      pose proof STA1 as STA2. eapply rw_cells_transport in STA2; [| exact MU12| exact WM12| apply DJthr; cbn; clear; lia].
      pose proof RX1 as RX2. eapply rw_cells_transport in RX2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      pose proof RNF1 as RNF2. eapply rw_cells_transport in RNF2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      pose proof RMFA1 as RMFA2. eapply rw_cells_transport in RMFA2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      pose proof RNFS1 as RNFS2. eapply rw_cells_transport in RNFS2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (first [ pose proof ((rk_thr_words A v [] AR (thr + 2872) 2 ltac:(unfold off_th_stats; fold thr; clear; lia) ltac:(unfold off_th_stats; fold thr; cbn; clear; lia))) as dR_35; dex1 dR_35 as mmw; destruct dR_35 as [LMM MMv] | pose proof ((rk_thr_words A v [] AR (thr + 2872) 2 ltac:(unfold off_th_stats; fold thr; clear; lia) ltac:(unfold off_th_stats; fold thr; cbn; clear; lia))) as dR_35; dand3 dR_35 as mmw LMM MMv | destruct (rk_thr_words A v [] AR (thr + 2872) 2 ltac:(unfold off_th_stats; fold thr; clear; lia) ltac:(unfold off_th_stats; fold thr; cbn; clear; lia)) as (mmw & LMM & MMv) ]).
      destruct mmw as [|mm72 [|mm80 [|]]]; try (cbn in LMM; clear -LMM; lia). cbn [map] in MMv.
      assert (NN1 : forall a, 0 <= a < 2^64 -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> v (wz a) <> None -> m1 (wz a) <> None).
      { intros a H0 H1. apply (wmono_NNR _ _ a WM1); [exact H1| exact H0]. }
      assert (MM1 : rw_cells rsegs m1 (thr + 2872) [C8 mm72; C8 mm80]).
      { eapply rw_cells_transport; [exact MMv| exact MUN1| exact WM1|]. unfold W1. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        unfold Ra, apart in *. fold sb in SP4. clear -PTF PTC PPB SHCH SP1 SP4 Gcr CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      pose proof MM1 as MM2. eapply rw_cells_transport in MM2; [| exact MU12| exact WM12| apply DJthr; cbn; clear; lia].
      (* [comment removed for export] *)
      assert (FAB : fac_ = region_beg (a_sb A) c + kFreeArrayOffset) by (unfold fac_, free_array_of, region_beg, sb; kung_all; lia).
      pose proof (ar_regions _ _ _ _ _ (proj2 AR) c Gcr) as RR. unfold region_repr_ in RR. cbv zeta in RR. change (a_sb A) with sb in RR. rewrite FAE in RR.
      (first [ dand13 RR as _ _ _ _ _ _ _ _ _ _ _ MFAv _ | destruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MFAv & _) ]). fold fac_ mfa in MFAv.
      assert (VISFA : forall x, fe <= x < fe + len -> hidc (pa_hull A') (wz x) = false).
      { intros x Hx. unfold hidc. apply negb_false_iff. rewrite unsigned_lit by (clear -Hx FEB LENF; kung_all; lia).
        apply (gw_vis_fa A c reg' cache' (BA (ba_idx b0) es' :: more) len Gcr LEN0 RCX ltac:(fold mfa; clear -RGF3 LENF; lia)). fold mfa. rewrite <- FAB. clear -Hx FEE RGF3. lia. }
      assert (ZFE : forall x, fe <= x < fe + len -> m2 (wz x) = Some (Z_to_bv 8 0)).
      { intros x Hx. unfold m2, mrestrict. rewrite (VISFA x Hx), ZSPEC. unfold in_range. rewrite unsigned_lit by (clear -Hx FEB LENF; kung_all; lia).
        replace ((fe <=? x) && (x <? fe + len)) with true; [reflexivity|]. symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Hx; lia. }
      assert (FACB : kHighMemBeg <= fac_) by (rewrite FAB; unfold region_beg; fold sb; clear -SBLO Gcr; kung_all; lia).
      assert (MJ2 : mapped m2 (fac_ + 4 * nf) (Z.of_nat (4 * hN))).
      { intros i0 Hi0. assert (HNE : Z.of_nat (4 * hN) = 4 * h) by (unfold hN; clear -RFR0; lia). rewrite HNE in Hi0.
        destruct (Z_lt_le_dec (fac_ + 4 * nf + i0) fe) as [Lo|Hi].
        - assert (X0 : 0 <= fac_ + 4 * nf + i0 < 2^64 /\ 0x60a000 <= fac_ + 4 * nf + i0 /\ kHighMemBeg <= fac_ + 4 * nf + i0) by (rewrite FEE in Lo; clear -Lo Hi0 FEB FEE FACB RGF3 RGF5 LENF; unfold nf in *; kung_all; lia).
          rewrite (MU12 (wz (fac_ + 4 * nf + i0))).
          + apply NN1; [exact (proj1 X0)| right; exact (proj1 (proj2 X0))|]. replace (fac_ + 4 * nf + i0) with (fac_ + (4 * nf + i0)) by (clear; lia). apply MFAv. rewrite FEE in Lo. clear -Lo Hi0 RGF5. unfold nf in *. lia.
          + rewrite unsigned_lit by exact (proj1 X0). unfold Wg. cbn [outside]. split; [clear -Lo; lia|]. split; [| exact I]. clear -X0 SHB FEB Lo. kung_all. lia.
        - rewrite (ZFE (fac_ + 4 * nf + i0)); [discriminate|]. split; [exact Hi|]. rewrite FEE. unfold len. clear -Hi0 NM1. lia. }
      (first [ pose proof ((mapped_u32arr m2 (fac_ + 4 * nf) hN MJ2 ltac:(clear -FEB FEE RGF3; unfold nf; kung_all; lia) ltac:(unfold hN; rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -RFR0; lia); clear -FEB FEE NM1 LENF RFR0; unfold len in *; kung_all; lia))) as dR_37; dex1 dR_37 as junk2; destruct dR_37 as [LJ2 JUNK2] | pose proof ((mapped_u32arr m2 (fac_ + 4 * nf) hN MJ2 ltac:(clear -FEB FEE RGF3; unfold nf; kung_all; lia) ltac:(unfold hN; rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -RFR0; lia); clear -FEB FEE NM1 LENF RFR0; unfold len in *; kung_all; lia))) as dR_37; dand3 dR_37 as junk2 LJ2 JUNK2 | destruct (mapped_u32arr m2 (fac_ + 4 * nf) hN MJ2 ltac:(clear -FEB FEE RGF3; unfold nf; kung_all; lia) ltac:(unfold hN; rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -RFR0; lia); clear -FEB FEE NM1 LENF RFR0; unfold len in *; kung_all; lia)) as (junk2 & LJ2 & JUNK2) ]).
      (* [comment removed for export] *)
      assert (SHFA : sfe = sh (region_beg (a_sb A) c + kFreeArrayOffset) + mfa / 8).
      { unfold sfe. rewrite FEE, FAB. apply sh_add; [| clear -RGF4; unfold kFreeArrayMapSize in *; lia].
        (first [ pose proof ((gw_align A c len (proj1 AR) Gcr LEN0 DMF)) as dR_38; dand3 dR_38 as _ FA64 _ | pose proof (gw_align A c len (proj1 AR) Gcr LEN0 DMF) as (_ & FA64 & _) ]). apply (mod0_down _ 64 8); [exists 8; reflexivity| exact FA64]. }
      assert (MS2 : mapped m2 sfe (len / 8)).
      { intros i0 Hi0.
        assert (ZR : 0 <= sfe + i0 < 2^64 /\ 0x60a000 <= sfe + i0 /\ sfe + i0 < fe) by (clear -Hi0 SHB FEB; kung_all; lia).
        assert (GH : ghost_hs_ (a_pl A) (sfe + i0)).
        { apply (gw_prim_shadow_ghost A (proj1 AR)). fold sb. destruct RANGE as (R1 & _). fold sb in R1.
          assert (Q1 : sb / 8 <= fe / 8) by (apply Z.div_le_mono; [clear; lia| exact R1]).
          assert (Q2 : (fe + len) / 8 <= (sb + kSpaceSize) / 8) by (apply Z.div_le_mono; [clear; lia| clear -FEB; lia]).
          assert (Q3 : (sb + kSpaceSize) / 8 = sb / 8 + kSpaceSize / 8).
          { pose proof (Z_div_mod_eq_full sb 8) as X0. rewrite (mod0_down sb 4096 8 ltac:(exists 512; reflexivity) SBAL) in X0.
            replace (sb + kSpaceSize) with (sb / 8 * 8 + kSpaceSize) by (clear -X0; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
          (first [ dand3 SHB as _ _ S3 | destruct SHB as (_ & _ & S3) ]). unfold sh. rewrite SFE in *. clear -Hi0 Q1 Q2 Q3 S3. lia. }
        assert (VIS : hidc (pa_hull A') (wz (sfe + i0)) = false).
        { unfold hidc. apply negb_false_iff. rewrite unsigned_lit by exact (proj1 ZR).
          apply (gw_vis_fsh A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) Gcr LEN0 DMF RCX ltac:(fold mfa; clear -RGF3 LENF; lia)). fold mfa. rewrite SHFA.
          assert (D2 : (mfa + len) / 8 = mfa / 8 + len / 8).
          { pose proof (Z_div_mod_eq_full mfa 8) as X0. assert (M8 : mfa mod 8 = 0) by (clear -RGF4; unfold kFreeArrayMapSize in *; lia). rewrite M8 in X0.
            replace (mfa + len) with (mfa / 8 * 8 + len) by (clear -X0; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
          rewrite D2. assert (0 <= mfa / 8) by (apply Z.div_pos; [clear -RGF3; lia| clear; lia]). clear -Hi0 H. lia. }
        destruct HID as [HG _]. destruct (HG _ GH) as [PRES _].
        unfold m2, mrestrict. rewrite VIS, ZSPEC. unfold in_range. rewrite unsigned_lit by exact (proj1 ZR).
        replace ((fe <=? sfe + i0) && (sfe + i0 <? fe + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; exact (proj2 (proj2 ZR))).
        unfold M1, munrestrict. destruct (hidc (pa_hull A) (wz (sfe + i0))) eqn:V0; [exact PRES|].
        apply NN1; [exact (proj1 ZR)| right; exact (proj1 (proj2 ZR))|]. unfold v, aview_of, mrestrict. rewrite V0. exact PRES. }
      pose proof (mapped_rw_cells m2 sfe (len / 8) MS2 ltac:(clear -SHB; kung_all; lia) ltac:(apply Z.div_pos; [clear -LENF; lia| clear; lia]) ltac:(clear -SHB; kung_all; lia)) as SHN2.
      (* [comment removed for export] *)
      set (Q2 := fun ms' : machine_state => exists (a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 statv' : word) (m' : mem) (pc : Z),
           ms' = MS (it_regs (wz dsp) gp (cl_tp LPA) T b cnt s10 s11 (wz dorec_retpc) a0 a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (Z.of_nat i + 1)) F (wz pc) fc None m' (seg_rom rsegs) /\
           ((Z.of_nat i + 1 < cnt /\ pc = dorec_callblk) \/ (Z.of_nat i + 1 = cnt /\ pc = dorec_batchblk)) /\
           rw_cells rsegs m' dsp (dorec_fr thr scr) /\
           (rz_size n - 16 = 0 \/ rw_cells rsegs m' pp [C8 (wz 0)]) /\
           rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi (user_size n))); C4 (wz (user_size n))] /\
           bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (round_up (user_size n) 8 / 8))) /\
           rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + user_size n))] /\
           rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (wz (max_count c - h + 1)); C4 (wz (max_count c)); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat (max_count c - h)) (wz kk)))] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv'] /\
           rw_cells rsegs m' Ra [C8 (wz 0)] /\ rw_cells rsegs m' (Ra + 16) [C8 (wz (nf + h))] /\ rw_cells rsegs m' (Ra + 24) [C8 (wz nm)] /\
           rw_cells rsegs m' (Ra + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] /\
           u32arr rsegs m' (fac_ + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (max_count c - h)) ks)) /\
           bytes_at rsegs m' sfe (repeat (Z_to_bv 8 250) (Z.to_nat (len / 8))) /\
           rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + len))] /\
           munch [(dsp - 688, dsp); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                  (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 24, Ra + 32); (Ra + 80, Ra + 88);
                  (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h); (sfe, sfe + len / 8); (thr + 2872, thr + 2888)] m2 m' /\
           wmono rsegs m2 m' /\ mem_inv rsegs m' /\ stk rsegs m' lo dsp).
      eapply (srz_evt_restrict rsegs (pa_hull A') (hull_segsR A') pa_wxR _ (pa_eager A') Q2 _ md2 TS HI2 HH2).
      { rewrite restrict_MS. fold m2.
        assert (USP : bv_unsigned (wz dsp) = dsp) by (apply unsigned_lit; clear -CE LOW SPHI HI47 SPR CEIL; lia).
        replace (dsp + -48 + -64 + -128 + -48 + -128) with (bv_unsigned (wz dsp) + -48 + -64 + -128 + -48 + -128) by (rewrite USP; reflexivity).
        unfold len, nm. rewrite <- HSH.
        eapply (iter_prim_drainmap_post gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b cnt (Z.of_nat i) scr
                  (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                  pa_tsd (p_ctx (a_pl A)) thr sb ri)
          with (kb := 512 * ba_idx b0) (m7 := m2) (c := c) (idx := k) (d := rz_size n - 16) (mu := rg_mapped_user (a_reg A c)) (n := user_size n) (b1 := b1)
               (rf := rf) (rfd := rfd) (maxc := max_count c) (k := kk) (ks := ks) (statv := statv) (junk := junk2)
               (pw := wz (hdr_of sb (ChP (CP c k)) n)) (mh := mh) (nf := nf) (mfa := mfa) (nfs := nfs) (v88 := v88) (mm72 := mm72) (mm80 := mm80)
               (lscr := lscr) (scr2 := scr2) (scr3 := scr3) (scr4 := scr4) (a0r := wz fe).
        all: rewrite ?HSH.
        all: try assumption.
        all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
        all: try assumption.
        all: cycle -2.
        1: { intros LT a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' DF' SL' MU' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' STK'.
             apply evt_done. subst Q2. first [ hotw_ex18 a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' dorec_callblk | exists a0y, a1y, a2y, a3y, a4y, a5y, a6y, a7y, t0y, t1y, t2y, t3y, t4y, t5y, t6y, statv', m', dorec_callblk ].
             split; [reflexivity|]. split; [left; split; [exact LT| reflexivity]|].
             repeat (split; [assumption|]). exact STK'. }
        1: { intros EQ a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' DF' SL' MU' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' STK'.
             apply evt_done. subst Q2. first [ hotw_ex18 a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' dorec_batchblk | exists a0y, a1y, a2y, a3y, a4y, a5y, a6y, a7y, t0y, t1y, t2y, t3y, t4y, t5y, t6y, statv', m', dorec_batchblk ].
             split; [reflexivity|]. split; [right; split; [exact EQ| reflexivity]|].
             repeat (split; [assumption|]). exact STK'. }
        all: first [ assumption | reflexivity | exact SHN2
                   | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                   | unfold pa_tsd; clear; lia
                   | unfold cnt; clear -LEN; unfold kQuarantineBatchCount in LEN; lia
                   | clear -SBRI RHI; lia
                   | clear -KB0 KBH; lia
                   | pose proof (nth_error_Some_lt _ _ _ NTH) as IL; unfold cnt; clear -IL; lia
                   | unfold mh, pp in *; clear -Gpe; lia
                   | pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU; clear -RU Grz Gfit Gu1; lia
                   | clear -Grzm; lia
                   | clear -Gk; lia
                   | clear -Gka Gam; lia
                   | clear -Gmk Gam Gka Gk Gcsr; kung_all; nia
                   | unfold kk; unfold kCompactPtrScale; clear -Gcm Gk; nia
                   | clear -Gu1 Gu3 Gnr; unfold kMaxPrimaryUser in *; lia
                   | unfold mh, pp in *; clear -Gfit Gphi CE; lia
                   | clear -MCR; lia
                   | clear -MCE RFR0; unfold h; lia
                   | unfold nf; clear; lia
                   | clear -RGF5 CAPN RFR0; unfold nf, mfa, h in *; kung_all; lia
                   | clear -RGF3; unfold mfa; kung_all; lia
                   | clear -Gmk; kung_all; lia
                   | apply unsigned_lit; clear -FEB LENF; kung_all; lia
                   | match goal with |- ?g => idtac "UNSOLVED2:" g end ]. }
      intros msr2 md3 HQ2 HI3 SB3 Hcl3.
      (first [ dex18 HQ2 as a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m3 pc; dand20 HQ2 as -> CASE DF' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' STK' | dand36 HQ2 as a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m3 pc -> CASE DF' MG' HD' SH' TF' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 dR_HQ2_t0; dand3 dR_HQ2_t0 as WM2 MI' STK' | destruct HQ2 as (a0y & a1y & a2y & a3y & a4y & a5y & a6y & a7y & t0y & t1y & t2y & t3y & t4y & t5y & t6y & statv' & m3 & pc & -> & CASE & DF' & MG' & HD' & SH' & TF' & LN' & ST' & RX' & RNF' & RMFA' & RNFS' & ARR' & SHF' & MM' & MUN2 & WM2 & MI' & STK') ]).
      rewrite unrestrict_MS. cbn [ms_mem] in Hcl3.
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with M2 end.
      set (Mf := munrestrict (hidc (pa_hull A')) M2 m3).
      pose proof (same_but_materialized_frame _ _ SB3) as FRM3.
      assert (VIEW : aview_of (pa_hull A') Mf = m3).
      { unfold aview_of, Mf. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl3. }
      set (W2 := [(dsp - 688, dsp); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                  (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 24, Ra + 32); (Ra + 80, Ra + 88);
                  (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h); (sfe, sfe + len / 8); (thr + 2872, thr + 2888)]) in *.
      assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m3 (wz a) <> None).
      { intros a H0 H1 H2 Hv. apply (wmono_NNR _ _ a WM2); [exact H1| clear -H0 H2; lia|]. apply (wmono_NNR _ _ a WM12); [exact H1| clear -H0 H2; lia|].
        apply NN1; [clear -H0 H2; lia| exact H1| exact Hv]. }
      assert (AG3 : forall a, 0 <= a < 2^64 -> outside W1 a -> outside Wg a -> outside W2 a -> m3 (wz a) = v (wz a)).
      { intros a Ha O1 Og O2. rewrite (MUN2 (wz a)) by (rewrite unsigned_lit by exact Ha; exact O2).
        rewrite (MU12 (wz a)) by (rewrite unsigned_lit by exact Ha; exact Og). apply (MUN1 (wz a)). rewrite unsigned_lit by exact Ha. exact O1. }
      (* [comment removed for export] *)
      set (Wn := fun a => dsp - 688 <= a < dsp).
      set (SHP := fun a => sh (pp + rz_size n) <= a < sh (pp + rz_size n) + (user_size n + 7) / 8).
      pose proof (round_up_ge (user_size n) 8 ltac:(lia)) as RU.
      assert (MU : forall a, 0 <= a < 2^64 -> ~ rp_foot A c k reg' Wn SHP a -> m3 (wz a) = v (wz a)).
      { intros a Ha NF. unfold rp_foot in NF. rewrite RGC, reg_return_mapped_fa in NF. subst Wn SHP. cbv beta in NF.
        fold pp thr sb ri in NF. fold Ra fac_ nf mfa in NF.
        apply (AG3 a Ha); unfold W1, Wg, W2; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros Xa; apply NF.
        - left. exact Xa.
        - right; left. clear -Xa Gcsr. lia.
        - right; left. clear -Xa PPB. unfold mh in *. lia.
        - right; right; left. replace (mh + 16) with (pp + rz_size n) in Xa by (unfold mh; clear; lia). rewrite ?R88 in Xa. exact Xa.
        - do 4 right; left. clear -Xa. lia.
        - do 3 right; left. clear -Xa. lia.
        - do 5 right; left. exact Xa.
        - do 7 right; left. rewrite FEE in Xa. unfold len in Xa. clear -Xa RGF5. unfold nf in *. lia.
        - do 8 right. rewrite <- FEE. fold sfe. unfold len in Xa. exact Xa.
        - left. exact Xa.
        - do 3 right; left. exact Xa.
        - do 4 right; left. clear -Xa. lia.
        - do 5 right; left. exact Xa.
        - do 6 right; left. clear -Xa. lia.
        - do 6 right; left. clear -Xa. lia.
        - do 6 right; left. clear -Xa. lia.
        - do 7 right; left. clear -Xa NM1. lia.
        - do 8 right. rewrite <- FEE. fold sfe. unfold len in Xa. exact Xa.
        - do 4 right; left. clear -Xa. lia. }
      (* [comment removed for export] *)
      set (Wall := W1 ++ Wg ++ W2).
      assert (MUNall : munch Wall v m3).
      { assert (S1 : sub_fp W1 Wall) by (unfold sub_fp, Wall; intros y Hy; rewrite !AFreeH0.outside_app in Hy; exact (proj1 Hy)).
        assert (S2 : sub_fp Wg Wall) by (unfold sub_fp, Wall; intros y Hy; rewrite !AFreeH0.outside_app in Hy; exact (proj1 (proj2 Hy))).
        assert (S3 : sub_fp W2 Wall) by (unfold sub_fp, Wall; intros y Hy; rewrite !AFreeH0.outside_app in Hy; exact (proj2 (proj2 Hy))).
        exact (munch_trans _ _ _ _ (munch_weaken _ _ _ _ S1 MUN1) (munch_trans _ _ _ _ (munch_weaken _ _ _ _ S2 MU12) (munch_weaken _ _ _ _ S3 MUN2))). }
      assert (WMall : wmono rsegs v m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 WM2)).
      assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
      pose proof (round_up_mod (user_size n) 8 ltac:(lia)) as RUM.
      assert (SHPW : forall a, SHP a -> sh pp <= a < sh pp + class_size c / 8).
      { subst SHP; cbv beta; intros a Ha. rewrite SHA in Ha. clear -Ha Gfit Grz Grzm CS32 RUM RU Gu1 R88. lia. }
      (* [comment removed for export] *)
      assert (DISJ : forall a l, 0 < l ->
               (Ra + 32 <= a /\ a + l <= Ra + 80) \/ (Ra + 96 <= a /\ a + l <= Ra + 128) \/ (fac_ <= a /\ a + l <= fac_ + 4 * nf) \/ (T <= a /\ a + l <= uspd) ->
               disjoint_from Wall a l).
      { intros a l Hl Ha. unfold Wall, W1, Wg, W2. cbn [app disjoint_from].
        assert (K0 : dsp <= T /\ uspd <= 2^47 /\ alloc_ceiling <= dsp - 688) by (clear -CEIL LOW SPHI HI47; lia).
        assert (K1 : kHighMemBeg <= fac_ /\ fac_ + 4 * nf <= fe /\ fe + len <= sb + kSpaceSize /\ sb + kSpaceSize <= ri /\ fac_ + 4 * nf + 4 * h <= fe + len /\
                     pp + class_size c <= fac_ /\ sb <= fac_ /\ ri + 4096 <= alloc_ceiling /\ kHighMemBeg <= sb /\ 0 <= len /\ 0 <= nf /\ 0 <= h).
        { fold sb in RI0. (first [ dand3 PPB as PB1 PB2 _ | destruct PPB as (PB1 & PB2 & _) ]). clear -FACB FEE RGF5 FEB RI0 NM1 PB1 PB2 FAB RHI SBLO Gcr LEN0 RFR0. unfold len, nf, h, fac_, free_array_of, region_beg in *. kung_all. lia. }
        assert (K2 : sfe + len / 8 <= kHighMemBeg /\ kLowShadowMapBeg <= sfe /\ sh (mh + 16) + round_up (user_size n) 8 / 8 <= kHighMemBeg /\ kLowShadowMapBeg <= sh (mh + 16)) by (clear -SHB SHCH; lia).
        assert (THRD : (ri <= a /\ a + l <= ri + 4096) \/ (sb <= a /\ a + l <= sb + kSpaceSize) \/ alloc_ceiling <= a -> a + l <= thr \/ thr + 4096 <= a).
        { unfold apart in SP1, SP4. fold sb in SP4. clear -SP1 SP4 PTC Hl. kung_all. lia. }
        assert (ZONE : (ri <= a /\ a + l <= ri + 4096) \/ (sb <= a /\ a + l <= sb + kSpaceSize) \/ alloc_ceiling <= a).
        { destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left| left| right; left| right; right]; clear -Ha Hl K0 K1 Gcr; try unfold Ra in *; lia. }
        specialize (THRD ZONE). clear ZONE.
        (first [ dand6 PPB as PB1 PB2 PB3 PB4 PB5 PB6 | destruct PPB as (PB1 & PB2 & PB3 & PB4 & PB5 & PB6) ]).
        destruct Ha as [Ha|[Ha|[Ha|Ha]]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit;
          first [ clear -Ha Hl K0 K1 K2 PB3 PB4 PB5 PB6 Gcr; try unfold Ra in *; kung_all; lia
                | clear -Ha Hl THRD Gcr; lia ]. }
      assert (OUT : forall a, (Ra + 32 <= a < Ra + 80 \/ Ra + 96 <= a < Ra + 128 \/ fac_ <= a < fac_ + 4 * nf \/ T <= a < uspd) -> outside Wall a).
      { intros a Ha. apply (disjoint_outside _ a 1); [| clear; lia]. apply DISJ; [clear; lia|]. clear -Ha. lia. }
    assert (P_mx : u64_at rsegs m3 (ri + 128 * c) 0) by (apply u64_of_rw; [clear; lia| exact RX']).
    (* [comment removed for export] *)
    assert (KSE : firstn (length (pk_chunks (a_cache A c))) ks = map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) (pk_chunks (a_cache A c))) by exact KSF.
    assert (OUTW : firstn (Z.to_nat h) (skipn (Z.to_nat (max_count c - h)) ks) = map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) out).
    { unfold out, drain_out. fold hN. replace (Z.to_nat (max_count c - h)) with (length (pk_chunks (a_cache A c)) - hN)%nat by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      rewrite firstn_skipn_comm. replace (length (pk_chunks (a_cache A c)) - hN + hN)%nat with (length (pk_chunks (a_cache A c))) by (clear -HLEN; lia).
      rewrite KSE, skipn_map. reflexivity. }
    assert (MFA3 : mapped m3 (free_array_beg sb c) nm).
    { rewrite FAE. fold fac_. intros i0 Hi0. destruct (Z_lt_le_dec (fac_ + i0) fe) as [Lo|Hi].
      - apply NN; [clear -Hi0 FACB; kung_all; lia| right; clear -Hi0 FACB; kung_all; lia| clear -Lo FEB LENF; lia|]. apply MFAv. rewrite FEE in Lo. clear -Lo Hi0. lia.
      - apply (wmono_NNR _ _ (fac_ + i0) WM2); [right; clear -Hi0 FACB; kung_all; lia| clear -Hi0 Hi FEB FEE NM1 LENF; unfold len in *; kung_all; lia|].
        rewrite (ZFE (fac_ + i0)); [discriminate|]. split; [exact Hi|]. rewrite FEE. unfold len. clear -Hi0. lia. }
    assert (P_regc : region_repr_ LPA sb (reg' c) m3 c).
    { rewrite RGC. pose proof (ar_regions _ _ _ _ _ (proj2 AR) c Gcr) as RR0. change (a_sb A) with sb in RR0.
      (first [ pose proof ((rk_region_facts A v [] AR c Gcr)) as dR_43; dand6 dR_43 as _ _ RG3 _ RG5 _ | pose proof (rk_region_facts A v [] AR c Gcr) as (_ & _ & RG3 & _ & RG5 & _) ]).
      apply (region_return_of_cells_grow v m3 sb (a_reg A c) c out (wz (bv_unsigned nfs + h)) v88 nm Gcr RR0).
      - rewrite OUTL. unfold hN, nf in *. clear -RG3 RG5 CAPN RFR0. kung_all. lia.
      - clear -NM1 NM4 RFR0. unfold nf, h in *. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUNall (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE; kung_all; lia). apply OUT. left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUNall (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE; kung_all; lia). apply OUT. right; left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite FAE in Ha. apply (MUNall (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RG3 RG5 SBLO SBRI RHI CE; unfold free_array_of in *; kung_all; lia). apply OUT. right; right; left. unfold fac_, nf. clear -Ha. lia.
      - exact MFA3.
      - intros a Ha Hv. rewrite RBE in Ha. apply NN; [| right| | exact Hv]; clear -Ha Gcr Gmk SBLO SBRI RHI CE; kung_all; lia.
      - rewrite RIA, OUTL. unfold hN. rewrite Z2Nat.id by (clear -RFR0; unfold h; lia). fold nf. unfold Ra, ri in RNF'. exact RNF'.
      - rewrite RIA. unfold Ra, ri in RMFA'. exact RMFA'.
      - rewrite RIA. unfold Ra, ri in RNFS'. exact RNFS'.
      - rewrite FAE, <- OUTW. fold nf. unfold fac_, sb in ARR'. exact ARR'. }
    (* [comment removed for export] *)
    assert (ENC : forall k', In k' (pk_chunks (a_cache A c)) \/ k' = k -> 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { intros k' Hk'. assert (KR' : 0 <= k' < carved_count A c) by (destruct Hk' as [Hk'| ->]; [exact (KRG k' Hk')| exact Gk]).
      unfold kCompactPtrScale. clear -KR' RGF6 Gam Gmk Gcsr. split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. kung_all. nia. }
    assert (ENT : forall i0 k', nth_error (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]) i0 = Some k' ->
              nth_error (upd ks (Z.to_nat (max_count c - h)) (wz kk)) i0 = Some (wz (k' * class_size c / kCompactPtrScale)) /\ 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { assert (KL : length (drain_keep (pk_chunks (a_cache A c)) hN) = (length (pk_chunks (a_cache A c)) - hN)%nat) by (apply drain_keep_length; exact HLEN).
      assert (MH : Z.to_nat (max_count c - h) = (length (pk_chunks (a_cache A c)) - hN)%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      intros i0 k' Hk'. destruct (Nat.lt_ge_cases i0 (length (pk_chunks (a_cache A c)) - hN)) as [LT|GE].
      - rewrite nth_error_app1 in Hk' by (rewrite KL; exact LT). unfold drain_keep in Hk'. rewrite nth_error_firstn in Hk'.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)) - hN)); [| exfalso; clear -LT H; lia].
        split; [| apply ENC; left; eapply nth_error_In; exact Hk'].
        rewrite nth_error_upd_other by (rewrite MH; clear -LT; lia).
        pose proof (f_equal (fun l => nth_error l i0) KSF) as E. cbv beta in E. rewrite nth_error_firstn in E.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)))); [| exfalso; clear -LT H0; lia]. rewrite E, nth_error_map, Hk'. reflexivity.
      - rewrite nth_error_app2 in Hk' by (rewrite KL; exact GE). rewrite KL in Hk'. destruct (i0 - (length (pk_chunks (a_cache A c)) - hN))%nat as [|x] eqn:EQ; cbn in Hk'; [injection Hk' as <-| destruct x; discriminate].
        assert (i0 = (length (pk_chunks (a_cache A c)) - hN)%nat) by (clear -GE EQ; lia). subst i0. split; [| apply ENC; right; reflexivity].
        rewrite MH. rewrite nth_error_upd_same by (rewrite LKS; unfold hN, cntc in *; clear -FULL MCR RFR0; lia). reflexivity. }
    pose proof LN' as LNx.
    replace (max_count c - h + 1) with (Z.of_nat (length (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]))) in LNx
      by (rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    pose proof (line_of_cells m3 (thr + 208 + 80 * c) c (upd ks (Z.to_nat (max_count c - h)) (wz kk)) (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]) (a_cache_inited A) Gcr CI
                  ltac:(rewrite upd_length; exact LKS) ltac:(rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0 MCR; lia) ENT
                  LNx) as P_linec.
    rewrite <- CAE in P_linec.
    replace (thr + 208 + 80 * c) with (thr + off_th_per_class c) in P_linec by (unfold off_th_per_class, off_th_alloc_cache, kPerClassSize; clear; lia).
    assert (MFA8 : rg_mapped_fa (a_reg A c) mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists (2^15); reflexivity| exact RGF4]).
    assert (R'E : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_allocated_user (reg' c) = rg_allocated_user (a_reg A c) /\
                  rg_mapped_fa (a_reg A c) <= rg_mapped_fa (reg' c) /\ rg_mapped_fa (reg' c) <= kFreeArraySize /\ rg_mapped_fa (reg' c) mod 8 = 0).
    { rewrite RGC, reg_return_mapped_user, reg_return_allocated, reg_return_mapped_fa. fold mfa. clear -NM1 NM3 NM4 NOFIT. unfold kFreeArraySize, kFaMap in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; lia. }
    assert (VSH : bytes_at rsegs m3 (sh pp) (pshadow_free c)).
    { apply (vsh_entry A v m3 [] c k reg' AR Wn WNH SHP CVe R'E MU n WE LE).
      - intros a. subst SHP. cbv beta. unfold pp, sb. split; intros X; exact X.
      - replace (chunk_addr (a_sb A) c k + rz_size n) with (mh + 16) by (unfold mh, pp, sb; clear; lia). exact SH'. }
    assert (P_fash : bytes_at rsegs m3 (sh (fac_ + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (reg' c) - mfa) / 8)))).
    { rewrite RGC, reg_return_mapped_fa. rewrite <- FEE. exact SHF'. }
    pose proof (recp_arepr A v m3 [] c k more reg' cache' AR W Wn WNH SHP SHPW CVe
                  (ev_ne_live A v [] c k n _ _ _ AR W L') (ev_ne_batch A v [] c k n _ _ _ AR W L') (ev_ne_rest A c k n _ _ _ W L')
                  CAO ltac:(intros k' Hk'; rewrite CAE in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|[<-|[]]]; [left; exact (proj2 (drain_in_iff _ hN k') (or_introl Hk'))| right; reflexivity])
                  RGO R'E ltac:(intros k' Hk'; rewrite RGC, reg_return_free in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|Hk']; [left; exact Hk'| right; exact (proj2 (drain_in_iff _ hN k') (or_intror Hk'))])
                  MU NN P_mx P_regc P_linec VSH P_fash (BA (ba_idx b0) es' :: more)) as AR'.
    change (recA' _ _ _ _) with A' in AR'.
    (* [comment removed for export] *)
    pose proof (ev_ne_batch A v [] c k n _ _ _ AR W L') as NEB. pose proof (ev_ne_limbo A c k n _ _ _ W L') as NEL.
    assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' (es' ++ q_entries more)).
    { intros b' e' Hb' He'. apply in_or_app. right. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
    assert (INhead : forall j e', (S i <= j)%nat -> nth_error (ba_entries b0) j = Some e' -> In e' (es' ++ q_entries more)).
    { intros j e' Hj He'. apply in_or_app. left. subst es'. apply (nth_error_In _ (j - S i)). rewrite nth_error_skipn. replace (S i + (j - S i))%nat with j by (clear -Hj; lia). exact He'. }
    assert (RC' : rcells A' m3 T (Some (b0, S i)) more).
    { constructor.
      - exact AR'.
      - unfold tmp_hdr. eapply rw_cells_transport; [exact RTMP| exact MUNall| exact WMall|]. apply DISJ; [cbn; clear; lia|]. right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia.
      - apply (tmp_chain_xfer A v m3 [] c k (ba_idx b0) _ more reg' cache' AR W L' Wn WNH SHP SHPW CVe NEB R'E MU more); [intros b' Hb'; exact Hb'| exact RCH].
      - intros b' e' Hb' He'. apply (lentry_xfer A v m3 [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU NN e').
        + apply (limbo_in A (ba_idx b0) _ more W L'). cbn [app]. right. exact (INmore b' e' Hb' He').
        + apply NEL. exact (INmore b' e' Hb' He').
        + exact (RME b' e' Hb' He').
      - intros b' Hb'. destruct (RMO b' Hb') as [LB SHBx]. pose proof (more_in A (ba_idx b0) _ more W L' b' Hb') as Hb2.
        destruct (lbatch_xfer A v m3 [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                    (batch_carved A v [] AR b' Hb2) (NEB b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
        split; [exact LB'| exact (SHB' SHBx)].
      - split; [|split].
        + intros j e' Hj He'. apply (lentry_xfer A v m3 [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU NN e').
          * apply (limbo_in A (ba_idx b0) _ more W L'). cbn [app]. right. exact (INhead j e' Hj He').
          * apply NEL. exact (INhead j e' Hj He').
          * exact (RENT j e' ltac:(clear -Hj; lia) He').
        + assert (LBi : lbatch_cells sb v (chunk_addr sb kQuarantineBatchClass (ba_idx b0)) (ba_entries b0) (S i) (batch_bytes b0)).
          { (first [ dand3 RBAT as X1 X2 X3 | destruct RBAT as (X1 & X2 & X3) ]). split; [| exact (conj X2 X3)]. intros i0 e' Hi0 He'. apply (X1 i0 e'); [clear -Hi0; lia| exact He']. }
          exact (proj1 (lbatch_xfer A v m3 [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b0) (ba_entries b0) (S i) (batch_bytes b0)
                           (batch_carved A v [] AR _ HIN) NEhb LEN LBi)).
        + exact (proj2 (lbatch_xfer A v m3 [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b0) (ba_entries b0) i (batch_bytes b0)
                           (batch_carved A v [] AR _ HIN) NEhb LEN RBAT) RBSH). }
      (* [comment removed for export] *)
      assert (AMD1 : amd_frame md md1) by exact (wamd_sbm md md1 SB1 HLT).
      (first [ pose proof ((cr_model A md md1 fe len W LED1 HH1 HI1 COV1 TOP1 RANGE AMD1 md3 SB3)) as dR_45; dand5 dR_45 as LED3 COV3 TOP3 AMD3 HH3 | destruct (cr_model A md md1 fe len W LED1 HH1 HI1 COV1 TOP1 RANGE AMD1 md3 SB3) as (LED3 & COV3 & TOP3 & AMD3 & HH3) ]).
      assert (MFH : forall z, 0 <= z < 2^64 -> hidc (pa_hull A') (wz z) = true -> Mf (wz z) = m (wz z)).
      { intros z Hz V1. unfold Mf, munrestrict. rewrite V1, ZSPEC. unfold in_range. rewrite unsigned_lit by exact Hz.
        destruct (Z_lt_le_dec z fe) as [Lo|Hi0]; [| destruct (Z_lt_le_dec z (fe + len)) as [Lo2|Hi2]].
        - replace ((fe <=? z) && (z <? fe + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; exact Lo).
          unfold M1, munrestrict. rewrite (APopG5.hidc_grow_le (pa_hull A) (pa_hull A') HLE (wz z) V1). reflexivity.
        - exfalso. rewrite (VISFA z (conj Hi0 Lo2)) in V1. discriminate.
        - replace ((fe <=? z) && (z <? fe + len)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; exact Hi2).
          unfold M1, munrestrict. rewrite (APopG5.hidc_grow_le (pa_hull A) (pa_hull A') HLE (wz z) V1). reflexivity. }
      assert (MFV : forall z, hidc (pa_hull A') (wz z) = false -> Mf (wz z) = m3 (wz z)) by (intros z V1; unfold Mf, munrestrict; rewrite V1; reflexivity).
      assert (D2 : (mfa + len) / 8 = mfa / 8 + len / 8).
      { pose proof (Z_div_mod_eq_full mfa 8) as X0. assert (M8 : mfa mod 8 = 0) by (clear -RGF4; unfold kFreeArrayMapSize in *; lia). rewrite M8 in X0.
        replace (mfa + len) with (mfa / 8 * 8 + len) by (clear -X0; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
      assert (NEWHS : forall z, sfe <= z < sfe + len / 8 -> heap_shadow A' z).
      { intros z Hz. unfold heap_shadow, heap_shadow_, A', recA'. cbn [a_pl a_reg a_sec]. right; left. exists c. split; [exact Gcr|]. cbv zeta.
        rewrite (proj2 RCX). fold mfa. unfold a_sb. cbn [a_pl]. fold (a_sb A). rewrite D2. rewrite SHFA in Hz.
        assert (0 <= mfa / 8) by (apply Z.div_pos; [clear -RGF3; lia| clear; lia]). clear -Hz H. lia. }
      assert (GHV : forall z, ghost_hs_ (a_pl A) z -> 0 <= z < 2^64 /\ 0x60a000 <= z /\ ~ (fe <= z < fe + len)).
      { intros z [SMz _]. unfold in_shadow_maps in SMz. clear -SMz FEB. kung_all. lia. }
      assert (VOLD : forall z, 0 <= z < 2^64 -> hidc (pa_hull A') (wz z) = false -> ~ (fe <= z < fe + len) -> ~ (sfe <= z < sfe + len / 8) -> hidc (pa_hull A) (wz z) = false).
      { intros z Hz V1 N1 N2. destruct (hidc (pa_hull A) (wz z)) eqn:V0; [| reflexivity]. exfalso. unfold hidc in V0, V1. apply negb_true_iff in V0. apply negb_false_iff in V1.
        rewrite unsigned_lit in V0, V1 by exact Hz. destruct (NEWH z V1 V0) as [X0|X0]; [exact (N1 X0)| exact (N2 X0)]. }
      assert (HID' : hidden_repr (a_pl A') (a_reg A') (a_sec A') Mf).
      { apply (gw_hidden A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) LEN0 RGO RCX m Mf HID).
        - intros z Gz Pz. (first [ pose proof ((GHV z Gz)) as dR_46; dand3 dR_46 as Z64 ZI NFE | destruct (GHV z Gz) as (Z64 & ZI & NFE) ]). destruct (hidc (pa_hull A') (wz z)) eqn:V1; [rewrite (MFH z Z64 V1); exact Pz|].
          rewrite (MFV z V1). destruct (classic (sfe <= z < sfe + len / 8)) as [INS|NS].
          + apply (wmono_NNR _ _ z WM2); [right; exact ZI| exact Z64|]. replace z with (sfe + (z - sfe)) by (clear; lia). apply MS2. clear -INS. lia.
          + apply NN; [clear -Z64; lia| right; exact ZI| clear -Z64; lia|]. unfold v, aview_of, mrestrict. rewrite (VOLD z Z64 V1 NFE NS). exact Pz.
        - intros z Gz NHS. (first [ pose proof ((GHV z Gz)) as dR_47; dand3 dR_47 as Z64 ZI NFE | destruct (GHV z Gz) as (Z64 & ZI & NFE) ]). destruct (hidc (pa_hull A') (wz z)) eqn:V1; [exact (MFH z Z64 V1)|].
          rewrite (MFV z V1). assert (NS : ~ (sfe <= z < sfe + len / 8)) by (intros INS; exact (NHS (NEWHS z INS))).
          destruct Gz as [SMz NVz].
          rewrite (AG_shadow_maps A v m3 [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU z SMz).
          + unfold v, aview_of, mrestrict. rewrite (VOLD z Z64 V1 NFE NS). reflexivity.
          + intros SP. apply NHS. apply (gw_heap_shadow_mono A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) LEN0 RGO RCX).
            (first [ pose proof ((chunk_shadow A v [] AR c k Gcr Gk)) as dR_48; dand3 dR_48 as _ S2 _ | pose proof (chunk_shadow A v [] AR c k Gcr Gk) as (_ & S2 & _) ]). apply S2. exact (SHPW z SP).
          + rewrite RGC, reg_return_mapped_fa. change (free_array_of (a_sb A) c) with fac_. change (rg_mapped_fa (a_reg A c)) with mfa. rewrite <- FEE. change (sh fe) with sfe. change (nm - mfa) with len. exact NS.
        - intros z Hz NVz Pz. assert (Z64 : 0 <= z < 2^64 /\ 0x60a000 <= z /\ ~ (fe <= z < fe + len) /\ ~ (sfe <= z < sfe + len / 8)) by (clear -Hz FEB SHB; kung_all; lia).
          (first [ dand4 Z64 as Z64 ZI NFE NS | destruct Z64 as (Z64 & ZI & NFE & NS) ]). destruct (hidc (pa_hull A') (wz z)) eqn:V1; [rewrite (MFH z Z64 V1); exact Pz|].
          rewrite (MFV z V1). apply NN; [clear -Z64; lia| right; exact ZI| clear -Z64; lia|]. unfold v, aview_of, mrestrict. rewrite (VOLD z Z64 V1 NFE NS). exact Pz. }
      assert (RI' : RINV A' Mf md3 T (Some (b0, S i)) more).
      { constructor.
        - exact W'.
        - reflexivity.
        - rewrite VIEW. exact RC'.
        - exact HID'.
        - exact EXTRA.
        - exact (gw_aledger A c reg' len Gcr RGO RCX md3 LED3 (lazy_free_sbm _ _ _ _ SB3 LZ2)).   (* [comment removed for export] *)
        - exact HI3.
        - exact HH3.
        - exact COV3.
        - exact TOP3. }
      (* [comment removed for export] *)
      assert (PF' : put_frame (p_thr (a_pl A)) m3).
      { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUNall| exact WMall|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
      assert (RF' : rec_frame (p_thr (a_pl A)) m3).
      { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUNall| exact WMall|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
      assert (SM' : mapped m3 lo (uspd - lo)).
      { intros q Hq. pose proof (rc_tmp _ _ _ _ _ RC') as TM'. unfold tmp_hdr in TM'.
        destruct (Z.lt_ge_cases (lo + q) dsp) as [C1|C1].
        { exact (stk_mapped_pa m3 lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
        destruct (Z.lt_ge_cases (lo + q) T) as [C2|C2].
        { pose proof (rw_mapped_hi m3 _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
          specialize (M (lo + q - dsp) ltac:(clear -C1 C2; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M. }
        destruct (Z.lt_ge_cases (lo + q) (T + 32)) as [C3|C3].
        { pose proof (rw_mapped_hi m3 _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
          specialize (M (lo + q - T) ltac:(clear -C2 C3; lia)). replace (T + (lo + q - T)) with (lo + q) in M by (clear; lia). exact M. }
        destruct (Z.lt_ge_cases (lo + q) (T + 80)) as [C4|C4].
        { pose proof (rw_mapped_hi m3 _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
          specialize (M (lo + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (lo + q - (T + 32))) with (lo + q) in M by (clear; lia). exact M. }
        pose proof (rw_mapped_hi m3 _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (lo + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (lo + q - (uspd + -80))) with (lo + q) in M by (clear; lia). exact M. }
      (* [comment removed for export] *)
      assert (DEADB : forall dlo dhi, In (dlo, dhi) (a_deadsh A) -> dhi <= kHighMemBeg).
      { intros dlo dhi Hd. (first [ pose proof ((wrE A W)) as dR_50; dand3 dR_50 as _ DF0 _ | destruct (wrE A W) as (_ & DF0 & _) ]). pose proof (proj1 (Forall_forall _ _) DF0 _ Hd) as (D1 & _). cbn [fst snd] in D1. clear -D1. kung_all. unfold kShadowGapBeg in *. lia. }
      assert (NLF : forall a, fac_ <= a < fac_ + kFreeArraySize -> ~ in_live_user A a /\ ~ in_live_frame A a).
      { intros a Ha. split.
        - intros LU. exact (proj2 (live_user_not_foot A v [] c k reg' AR CVe R'E a LU) Ha).
        - intros LF. pose proof (live_frame_zoneT A a (proj1 AR) LF) as Z1. (first [ pose proof ((bm_nth_fixed A)) as dR_51; dand8 dR_51 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
          pose proof (bm_sepT A 6 0 _ _ _ _ (proj1 AR) E6 E0 ltac:(lia)) as D.
          assert (INSP : a_sb A <= a < a_sb A + kSpaceSize + 4096) by (rewrite FAB in Ha; unfold region_beg in Ha; clear -Ha Gcr; kung_all; lia).
          pose proof (primary_in_b6T A a (proj1 AR) INSP) as XB6.
          unfold a_fs, a_b6 in *. clear -Z1 D XB6. unfold kFakeStackBytes, kFakeFramesOffset in *. lia. }
      assert (RS : rstep (pa_owned A) (pa_owned A') lo uspd v m3).
      { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
        - intros a Ha NO NO' NW. apply MU; [exact Ha|]. intros Fa.
          destruct (foot_owned A v [] c k reg' AR Wn SHP SHPW CVe (ev_ne_live A v [] c k n _ _ _ AR W L') R'E a Fa) as [X|[X|[X|X]]].
          + apply NW. subst Wn. cbv beta in X. clear -X LOW CEIL. lia.
          + exact (NO X).
          + apply NO'. rewrite RGC, reg_return_mapped_fa in X. change (free_array_of (a_sb A) c) with fac_ in X. change (rg_mapped_fa (a_reg A c)) with mfa in X.
            destruct (NLF a ltac:(clear -X RGF3 NM4; unfold kFreeArraySize; lia)) as [NU NF].
            apply (gw_fa_owned A c reg' cache' (BA (ba_idx b0) es' :: more) len Gcr RCX a); [| exact NU| exact NF]. rewrite <- FAB. fold mfa. unfold len. clear -X RGF3. lia.
          + apply NO'. rewrite RGC, reg_return_mapped_fa in X. change (free_array_of (a_sb A) c) with fac_ in X. change (rg_mapped_fa (a_reg A c)) with mfa in X.
            apply (gw_fsh_owned A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) Gcr LEN0 DMF RCX a). rewrite <- FAB. fold mfa. exact X.
        - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
        - exact SM'.
        - intros a Ha O'. destruct (gw_owned_new A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) Gcr RGO RCX ltac:(fold mfa; unfold len, kFreeArraySize; clear -NM4 RGF3; lia) a O') as [O|NEWa]; [left; exact O| right].
          rewrite FAE2 in NEWa. split.
          + unfold v, aview_of, mrestrict. replace (hidc (pa_hull A) (wz a)) with true; [reflexivity|]. symmetry. unfold hidc. apply negb_true_iff. rewrite unsigned_lit by exact Ha.
            apply (prim_unmapped_hidden A (proj1 AR) EXTRA DEADB c a Gcr). right. rewrite FAE2. unfold region_beg, kRegionSize. change (a_sb A) with sb. clear -NEWa FEL. unfold kFreeArrayOffset in *. lia.
          + unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear -NEWa FEB CE. kung_all. lia.
        - intros a Ha O NO'. exfalso. apply NO'. exact (gw_owned_mono A c reg' cache' (BA (ba_idx b0) es' :: more) len (proj1 AR) LEN0 RGO RCX a O). }
      assert (NZ : a_reg A c <> region_zero).
      { intros E. pose proof Gk as X. unfold carved_count, carved_count_ in X. rewrite E in X. cbn in X. clear -X.
        pose proof (Z.div_0_l (class_size c)). rewrite Zdiv_0_l in X. lia. }
      pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A' m3 md3 HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                    (fun c0 NE V0 => gw_virgin A c reg' cache' (BA (ba_idx b0) es' :: more) RGO c0 NZ CAO V0)
                    AMD3 RS) as HIST'.
      (* [comment removed for export] *)
      assert (CU' : CUR A' Mf md3 (Some (b0, S i)) more scr).
      { constructor; rewrite ?VIEW.
        - exact RI'.
        - exact HIST'.
        - exact MI'.
        - exact STK'.
        - exact PF'.
        - exact RF'.
        - exact DF'.
        - split; [exact LEN| pose proof (nth_error_Some_lt _ _ _ NTH) as IL; clear -IL; lia].
        - exact QB'. }
      destruct CASE as [[LT ->]|[EQ ->]].
      + specialize (KM A' Mf md3 a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y
                       ltac:(unfold cnt in LT; clear -LT; lia) CU' eq_refl).
        unfold it_cfgG in KM. rewrite Nat2Z.inj_succ in KM. exact KM.
      + specialize (KD A' Mf md3 a0y a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y
                       ltac:(unfold cnt in EQ; clear -EQ; lia) CU' eq_refl).
        unfold it_cfgG in KD. rewrite Nat2Z.inj_succ in KD. exact KD.
  Qed.
End RIter.

(* [comment removed for export] *)
Theorem step_pdm_ok {Clg : Ceiling} : step_pdm_stmt.
Proof.
  unfold step_pdm_stmt. intros rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 m1 md1 b0 i more scr
         ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CEIL LOW SPHI HI47 SPA VB CU NTH FULL NOROOM KM KD.
  exact (step_prim_drainmap rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
           A1 m1 md1 b0 i more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' c k n CU NTH FULL NOROOM KM KD).
Qed.
End AFreeRI2.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRW2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AFreeRI3.AFreeRI2.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kFreeArraySize, kLowShadowMapBeg, kPtrArrayReserve,
                        kQuarantineBatchBytes, kQuarantineBatchCount in *.

Section RIter.
Context {Clg : Ceiling}.
  (* [comment removed for export] *)
  Variables (rac spd gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (A0 : AState) (m0 : mem) (md0 : Model) (p n0 stkobj lo hi : Z) (TS : TSet).
  (* [comment removed for export] *)
  Variables (xs2 xs5 : word).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LOW : lo <= bv_unsigned spd - 4096.
  Hypothesis SPHI : bv_unsigned spd <= hi.
  Hypothesis HI47 : hi <= 2^47.
  Hypothesis SPA : bv_unsigned spd mod 16 = 0.
  Hypothesis VB : forall a, newblk p n0 a -> a < alloc_ceiling.
  #[warnings="-notation-for-abbreviation"] Local Notation uspd := (bv_unsigned spd).
  #[warnings="-notation-for-abbreviation"] Local Notation T := (bv_unsigned spd - 160).
  #[warnings="-notation-for-abbreviation"] Local Notation dsp := (bv_unsigned spd - 160 - 112).
  #[warnings="-notation-for-abbreviation"] Local Notation v0 := (aview_of (pa_hull A0) m0).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation put_frame := (put_frameG rac spd s0 s1 s2 s3 s4 s5 s6 stkobj).
  #[warnings="-notation-for-abbreviation"] Local Notation rec_frame := (rec_frameG spd stkobj xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation dorec_fr := (dorec_frG s7 s8 s9 stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation CUR := (CURG rac spd s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 A0 m0 md0 p n0 stkobj lo hi xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation it_cfg := (it_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation head_cfg := (head_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation blk_cfg := (blk_cfgG spd gp s10 s11 F fc).
  #[warnings="-notation-for-abbreviation"] Local Notation exit_cfg := (exit_cfgG spd gp s7 s8 s9 s10 s11 F fc stkobj xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation XCUR := (XCURG rac spd s0 s1 s2 s3 s4 s5 s6 A0 m0 md0 p n0 stkobj lo hi xs2).
  #[warnings="-notation-for-abbreviation"] Local Notation KMORE := (KMORE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5).
  #[warnings="-notation-for-abbreviation"] Local Notation KDONE := (KDONE rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5).

  (* [comment removed for export] *)
  #[using="VB SPA HI47 SPHI LOW CEIL"] Lemma step_batch_drainmap : forall (A : AState) (m : mem) (md : Model) (b0 : batch) (more : list batch) (scr : list byte)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' : word),
    CUR A m md (Some (b0, length (ba_entries b0))) more scr ->
    Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass))) = max_count kQuarantineBatchClass ->
    rg_mapped_fa (a_reg A kQuarantineBatchClass) < 4 * (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) + max_count kQuarantineBatchClass / 2) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        more <> [] -> CUR A' m' md' None more scr -> a_pl A' = a_pl A ->
        srealizes rsegs (head_cfg A' m' md' more (wz dorec_nextpc) a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (wz (batch_addr (a_sb A) b0)) s6' s7' s8' s9') TS) ->
    (forall (A' : AState) (m' : mem) (md' : Model) (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' : word),
        more = [] -> XCUR A' m' md' -> a_pl A' = a_pl A ->
        srealizes rsegs (exit_cfg A' m' md' t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'') TS) ->
    srealizes rsegs (blk_cfg A m md b0 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9') TS.
  Proof.
    intros A m md b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU FULL NOROOM KM K0.
    destruct CU as [RI HIST MI ST PF RF DF [LEN _] QB]. destruct RI as [W L RC HID EXTRA LED HMI HLT COV CEI].
    set (v := aview_of (pa_hull A) m) in *.
    pose proof (conj (WFT_of_WFR A W) (rc_arepr _ _ _ _ _ RC) : WFT A /\ @arepr _ DepotRepL LPA AL_pboth [] A v) as AR.
    assert (L' : a_qlimbo A = BA (ba_idx b0) [] :: more).
    { rewrite L. unfold limbo_of. rewrite skipn_all. reflexivity. }
    pose proof alloc_ceiling_val as CE. pose proof (zr_word spd) as SPR; unfold inr64 in SPR.
    (* [comment removed for export] *)
    (first [ pose proof ((rk_ri A v [] AR)) as dR_1; dand10 dR_1 as RI0 RLO RHI RAL SBAL SBLO SBRI RIA FAE RBE | pose proof (rk_ri A v [] AR) as (RI0 & RLO & RHI & RAL & SBAL & SBLO & SBRI & RIA & FAE & RBE) ]).
    (first [ pose proof ((rk_sep A v [] AR)) as dR_2; dand6 dR_2 as SP1 SP2 SP3 SP4 SP5 SP6 | pose proof (rk_sep A v [] AR) as (SP1 & SP2 & SP3 & SP4 & SP5 & SP6) ]).
    (first [ pose proof ((rk_place A v [] AR)) as dR_3; dand6 dR_3 as PT PTC PTM PC PCC _ | pose proof (rk_place A v [] AR) as (PT & PTC & PTM & PC & PCC & _) ]).
    pose proof (rk_TC A v [] AR) as TC. pose proof (rk_PCo A v [] AR) as PCo. pose proof (rk_SBc A v [] AR) as CSB. pose proof (rk_CRI A v [] AR) as CRI.
    pose proof (wrI A W) as CI.
    (first [ pose proof ((rk_stats A v [] AR)) as dR_4; dex3 dR_4 as statv rf rfd; dand4 dR_4 as RFR RFDR STA TRF | pose proof ((rk_stats A v [] AR)) as dR_4; dand7 dR_4 as statv rf rfd RFR RFDR STA TRF | destruct (rk_stats A v [] AR) as (statv & rf & rfd & RFR & RFDR & STA & TRF) ]).
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; clear; lia).
    (first [ pose proof ((rk_line A v [] AR CI kQuarantineBatchClass C24)) as dR_5; dex1 dR_5 as ks; dand7 dR_5 as LKS KSM KSF KLE KRG KND LINE | pose proof ((rk_line A v [] AR CI kQuarantineBatchClass C24)) as dR_5; dand8 dR_5 as ks LKS KSM KSF KLE KRG KND LINE | destruct (rk_line A v [] AR CI kQuarantineBatchClass C24) as (ks & LKS & KSM & KSF & KLE & KRG & KND & LINE) ]).
    destruct RC as [RAR RTMP RCH RME RMO RCUR]. cbn [rc_cur] in RCUR. (first [ dand3 RCUR as RENT RBAT RBSH | destruct RCUR as (RENT & RBAT & RBSH) ]).
    pose proof (head_in A _ _ more W L') as HIN.
    pose proof (batch_known A v [] AR (BA (ba_idx b0) []) HIN) as [KBR _]. cbn [ba_idx] in KBR.
    pose proof (rk_batch A v [] AR (ba_idx b0) KBR) as BG. cbv zeta in BG. (first [ dand9 BG as BFORM BLO BHI BAL KB0 KBH SEP_bt SEP_bc SEP_br | destruct BG as (BFORM & BLO & BHI & BAL & KB0 & KBH & SEP_bt & SEP_bc & SEP_br) ]).
    (first [ pose proof ((rk_region_facts A v [] AR kQuarantineBatchClass C24)) as dR_8; dand7 dR_8 as RGF1 RGF2 RGF3 RGF4 RGF5 RGF6 RGF7 | destruct (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (RGF1 & RGF2 & RGF3 & RGF4 & RGF5 & RGF6 & RGF7) ]).
    (first [ pose proof ((max_count_range kQuarantineBatchClass C24)) as dR_9; dand3 dR_9 as MCR0 MCE RFR0 | pose proof (max_count_range kQuarantineBatchClass C24) as (MCR0 & MCE & RFR0) ]). set (h := refill_count kQuarantineBatchClass) in *.
    assert (HSH : Z.shiftr (max_count kQuarantineBatchClass) 1 = h) by (rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; clear -MCE; rewrite MCE; rewrite Z.mul_comm, Z_div_mult by lia; reflexivity).
    (first [ pose proof ((rk_region A v [] AR kQuarantineBatchClass 0%nat C24 ltac:(pose proof (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (_ & _ & _ & _ & RG5' & _); clear -RG5'; cbn [Z.of_nat]; lia))) as dR_10; dex4 dR_10 as na nfs v88 junk0; dand8 dR_10 as RMX RNF RMFA RMU RNA RNFS _ _ | pose proof ((rk_region A v [] AR kQuarantineBatchClass 0%nat C24 ltac:(pose proof (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (_ & _ & _ & _ & RG5' & _); clear -RG5'; cbn [Z.of_nat]; lia))) as dR_10; dand12 dR_10 as na nfs v88 junk0 RMX RNF RMFA RMU RNA RNFS _ _ | destruct (rk_region A v [] AR kQuarantineBatchClass 0%nat C24 ltac:(pose proof (rk_region_facts A v [] AR kQuarantineBatchClass C24) as (_ & _ & _ & _ & RG5' & _); clear -RG5'; cbn [Z.of_nat]; lia)) as (na & nfs & v88 & junk0 & RMX & RNF & RMFA & RMU & RNA & RNFS & _ & _) ]).
    pose proof (rk_CPMH A v [] AR) as CPMH. pose proof (rk_CGCF A v [] AR) as CGCF. pose proof (rk_CDMP A v [] AR) as CDMP.
    assert (NOFIT : rg_mapped_fa (a_reg A kQuarantineBatchClass) < 4 * (Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass))) + h)).
    { clear -NOROOM MCE RFR0. unfold h in *. rewrite MCE in NOROOM. replace (2 * refill_count kQuarantineBatchClass / 2) with (refill_count kQuarantineBatchClass) in NOROOM by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity). exact NOROOM. }
    pose proof (rk_CITV A v [] AR) as CITV.
    (first [ pose proof ((wtR A (proj1 AR))) as dR_12; dand3 dR_12 as WR1 _ _ | destruct (wtR A (proj1 AR)) as (WR1 & _ & _) ]). (first [ pose proof ((WR1 kQuarantineBatchClass C24)) as dR_13; dand12 dR_13 as _ _ _ _ _ _ _ _ _ _ _ CAP | destruct (WR1 kQuarantineBatchClass C24) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CAP) ]). cbv zeta in CAP. pose proof (wfr_fa_cap A W kQuarantineBatchClass C24) as [CAPN AUB].   (* [comment removed for export] *)
    pose proof (bv_carved A v [] (ba_idx b0) more AR W L') as CVe.
    pose proof TC as TC'. (first [ dand13 TC' as _ _ _ _ _ Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct TC' as (_ & _ & _ & _ & _ & Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]).
    pose proof MCR0 as MCR.
    set (thr := p_thr (a_pl A)) in *. set (sb := a_sb A) in *. set (ri := a_ri A) in *.
    set (b := batch_addr sb b0) in *.
    set (fac_ := free_array_of sb kQuarantineBatchClass) in *.
    set (cntc := Z.of_nat (length (pk_chunks (a_cache A kQuarantineBatchClass)))) in *.
    set (kk := 512 * ba_idx b0).
    set (tn := Z.of_nat (length more)).
    set (nf := Z.of_nat (length (rg_free (a_reg A kQuarantineBatchClass)))) in *. set (mfa := rg_mapped_fa (a_reg A kQuarantineBatchClass)) in *.
    set (Ra := ri + 128 * kQuarantineBatchClass) in *.
    assert (TNR : 0 <= tn < 2^64).
    { pose proof (limbo_count_bound A W) as X. rewrite L' in X. cbn [length] in X.
      change (class_size kQuarantineBatchClass) with 8192 in RGF6. unfold tn. clear -X RGF1 RGF2 RGF6. kung_all. lia. }
    pose proof RTMP as TH. unfold tmp_hdr in TH. fold tn in TH.
    assert (RRE : bv_unsigned (wz recycle_ret : word) mod 2 = 0) by (rewrite unsigned_lit; [reflexivity| unfold recycle_ret; clear; lia]).
    set (nm := round_up (4 * (nf + h)) kFaMap). set (fe := sb + kQuarantineBatchClass * 4294967296 + kFreeArrayOffset + mfa).
    set (tf := match more with [] => 0 | b' :: _ => batch_addr sb b' end) in *.
    set (tl := match more with [] => 0 | _ :: _ => batch_addr sb (last more (BA 0 [])) end) in *.
    set (Q := fun ms' : machine_state => exists (t0 t1 t2 a6 t3 t4 t5 t6 : word) (lscr scr2 scr3 scr4 : list byte) (m' : mem),
           ms' = MSsvc (mkR (wz mapfixed_resume) (wz (dsp + -48 + -64 + -128 + -48 + -128)) gp (cl_tp LPA) t0 t1 t2 (wz (nm - mfa)) (wz 1)
                            (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6 (wz 222)
                            (wz fe) (wz efas_name) (wz PSC) (wz h) (wz (thr + 208 + 80 * kQuarantineBatchClass + 16 + 4 * (max_count kQuarantineBatchClass - h))) (wz (nf + h)) (wz 2305843009213693952)
                            (wz fac_) (wz 1152921504607895551) (wz kMutexWriter) t3 t4 t5 t6)
                       F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs) /\
           rw_cells rsegs m' dsp (dorec_fr thr scr) /\
           rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz (q_bytes more))] /\
           rw_cells rsegs m' (dsp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1558) (wz T) (wz dorec_nextpc)) /\
           rw_cells rsegs m' (dsp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)) /\
           rw_cells rsegs m' (dsp + -48 + -64 + -128)
                 (rta_frame scr2 (Ra + 8) s11 s10 s9' s8' s7' s6' (wz (2^37)) (wz b) (wz 24) (wz 0xb1558) (wz (thr + 208)) (wz (thr + 208 + 80 * kQuarantineBatchClass)) (wz lcdrain_ret)) /\
           rw_cells rsegs m' (dsp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (dsp + -48 + -56)) (wz 24) (wz nf) (wz Ra) (wz rta_efasret)) /\
           rw_cells rsegs m' (dsp + -48 + -64 + -128 + -48 + -128) (mapcb_frame scr4 (wz 0xb1558) (wz Ra) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) /\
           rw_cells rsegs m' (thr + 208 + 80 * kQuarantineBatchClass) [C4 (wz (max_count kQuarantineBatchClass - h)); C4 (wz (max_count kQuarantineBatchClass)); C8 (wz 8192); CB 64 (u32s ks)] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv] /\
           rw_cells rsegs m' Ra [C8 (wz kMutexWriter)] /\ rw_cells rsegs m' (Ra + 16) [C8 (wz nf)] /\ rw_cells rsegs m' (Ra + 24) [C8 (wz mfa)] /\
           rw_cells rsegs m' (Ra + 80) [C8 nfs; C8 v88] /\
           munch [(dsp - 688, dsp); (thr + 208 + 80 * kQuarantineBatchClass, thr + 208 + 80 * kQuarantineBatchClass + 4); (Ra, Ra + 8)] v m' /\
           wmono rsegs v m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (dsp + -48 + -64 + -128 + -48 + -128)).
    unfold blk_cfgG. fold sb. fold b.
    eapply (srz_evt_restrict rsegs (pa_hull A) (hull_segsR A) pa_wxR _ (pa_eager A) Q _ md TS HMI HLT).
    { rewrite restrict_MS. change (mrestrict (hidc (pa_hull A)) m) with v.
      eapply (batch_free_drainmap_pre2 gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b scr
                (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                pa_tsd (p_ctx (a_pl A)) thr sb ri)
        with (kb := kk) (tn := tn) (maxc := max_count kQuarantineBatchClass) (ks := ks) (statv := statv)
             (tf := tf) (tl := tl) (ts := q_bytes more) (nf := nf) (mfa := mfa) (nfs := nfs) (v88 := v88).
      all: rewrite ?HSH.
      all: try assumption.
      all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
      all: try assumption.
      all: cycle -1.
      1: { intros t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m' DF' TCL' LF' DRF' RTF' EFF' MFF' LN' ST' RX' RNF' RMFA' RNFS' MUN WM' MI' STK'.
           subst Q. first [ hotw_ex13 t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m' | exists t0'', t1'', t2'', a6'', t3'', t4'', t5'', t6'', lscr, scr2, scr3, scr4, m' ].
           split; [reflexivity|]. repeat (split; [assumption|]). exact STK'. }
      all: first [ assumption | reflexivity
                 | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                 | unfold pa_tsd; clear; lia
                 | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                 | clear -SBRI RHI; lia
                 | unfold kk; clear -KB0 KBH; lia
                 | clear -MCR; lia
                 | clear -MCE RFR0; unfold h; lia
                 | unfold nf; clear; lia
                 | clear -RGF5 CAPN RFR0; unfold nf, mfa, h in *; kung_all; lia
                 | clear -NOFIT MCE RFR0; unfold nf, mfa, h in *; lia
                 | rewrite <- FULL at 1; exact LINE
                 | clear -RGF3; unfold mfa; kung_all; lia
                 | clear -RGF4; unfold mfa; exact RGF4
                 | exact TH
                 | match goal with |- ?g => idtac "UNSOLVED:" g end ]. }
    intros msr1 md1 HQ HI1 SB1 Hcl1.
    (first [ dex13 HQ as t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m1; dand18 HQ as -> DF1 TCL1 LF1 DRF1 RTF1 EFF1 MFF1 LN1 STA1 RX1 RNF1 RMFA1 RNFS1 MUN1 WM1 MI1 STK1 | dand31 HQ as t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' lscr scr2 scr3 scr4 m1 -> DF1 TCL1 LF1 DRF1 RTF1 EFF1 MFF1 LN1 STA1 RX1 RNF1 RMFA1 RNFS1 MUN1 WM1 MI1 STK1 | destruct HQ as (t0'' & t1'' & t2'' & a6'' & t3'' & t4'' & t5'' & t6'' & lscr & scr2 & scr3 & scr4 & m1 & -> & DF1 & TCL1 & LF1 & DRF1 & RTF1 & EFF1 & MFF1 & LN1 & STA1 & RX1 & RNF1 & RMFA1 & RNFS1 & MUN1 & WM1 & MI1 & STK1) ]).
    rewrite unrestrict_MSsvc. cbn [ms_mem MSsvc] in Hcl1.
    pose proof (same_but_materialized_frame _ _ SB1) as FRM1.
    assert (HH1 : m_halted md1 = None).
    { (first [ dand18 FRM1 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X17 _ | destruct FRM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X17 & _) ]). rewrite X17. exact HLT. }
    assert (LED1 : aledger_ AL_pboth (a_pl A) (a_reg A) (a_sec A) md1) by exact (aledger_sbm _ _ _ _ md md1 SB1 LED).
    assert (COV1 : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md1)) by (rewrite (same_but_materialized_vmmaps _ _ SB1); exact COV).
    assert (TOP1 : alloc_top (m_vmmaps md1) = alloc_ceiling) by (rewrite (same_but_materialized_vmmaps _ _ SB1); exact CEI).
    (* [comment removed for export] *)
    set (c := kQuarantineBatchClass) in *. set (k := ba_idx b0) in *.
    pose proof C24 as Gcr. pose proof KBR as Gk. pose proof (class_size_range c Gcr) as Gcsr.
    pose proof (proj2 RGF1) as Gam. pose proof RGF2 as Gmk.
    (* [comment removed for export] *)
    set (len := nm - mfa) in *.
    pose proof (free_cached_count A c W Gcr) as FCC. fold nf cntc in FCC.
    (first [ pose proof ((WR1 c Gcr)) as dR_17; dand12 dR_17 as _ _ _ _ _ _ _ _ _ _ MUCAP _ | destruct (WR1 c Gcr) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MUCAP & _) ]).
    assert (NFH26 : nf + h <= 112993196).
    { assert (CC26 : carved_count A c <= 112993196).
      { unfold carved_count, carved_count_. apply Z.div_le_upper_bound; [clear -Gcsr; lia|]. clear -AUB Gam Gcsr. unfold kAuCap in AUB. change kQuarantineBatchClass with c in AUB. nia. }
      clear -FCC CC26 FULL MCE RFR0. unfold h in *. lia. }
    assert (NMF : 4 * (nf + h) <= nm /\ nm < 4 * (nf + h) + kFaMap /\ nm mod kFaMap = 0 /\ nm <= 2^29 - 2^26).
    { unfold nm. pose proof (round_up_ge (4 * (nf + h)) kFaMap ltac:(unfold kFaMap; lia)) as R1. pose proof (round_up_lt (4 * (nf + h)) kFaMap ltac:(unfold kFaMap; lia)) as R2.
      pose proof (round_up_mod (4 * (nf + h)) kFaMap ltac:(unfold kFaMap; lia)) as R3.
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. clear -R2 R3 NFH26. unfold kFaMap in *. lia. }
    (first [ dand4 NMF as NM1 NM2 NM3 NM4 | destruct NMF as (NM1 & NM2 & NM3 & NM4) ]).
    assert (LENF : 0 < len /\ len mod 4096 = 0 /\ len mod kFaMap = 0).
    { unfold len. split; [clear -NM1 NOFIT; lia|]. unfold kFaMap, kFreeArrayMapSize in *. clear -NM3 RGF4. split; lia. }
    (* [comment removed for export] *)
    set (hN := Z.to_nat h) in *.
    set (out := drain_out (pk_chunks (a_cache A c)) hN).
    set (cache' := recp_cache (a_cache A) c k).
    set (reg' := recp_reg (a_reg A) (a_cache A) c k nm).
    set (A' := recA' A reg' cache' more).
    assert (RGC : reg' c = reg_return (a_reg A c) out nm).
    { unfold reg', recp_reg, reg_set, cache_push_list. fold cntc. rewrite FULL, Z.eqb_refl, Z.eqb_refl. cbn [snd].
      replace (max_count c / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (RGO : forall c', c' <> c -> reg' c' = a_reg A c').
    { intros c' NE. unfold reg', recp_reg, reg_set. fold cntc. rewrite FULL, Z.eqb_refl. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (CAE : pk_chunks (cache' c) = drain_keep (pk_chunks (a_cache A c)) hN ++ [k]).
    { unfold cache', recp_cache, cache_set, cache_push_list. rewrite Z.eqb_refl. fold cntc. rewrite FULL, Z.eqb_refl. cbn [fst pk_chunks].
      replace (max_count c / 2) with h by (clear -MCE RFR0; unfold h in *; lia). reflexivity. }
    assert (CAO : forall c', c' <> c -> cache' c' = a_cache A c').
    { intros c' NE. unfold cache', recp_cache, cache_set. destruct (Z.eqb_spec c' c); [exfalso; exact (NE e)| reflexivity]. }
    assert (RCX : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_mapped_fa (reg' c) = rg_mapped_fa (a_reg A c) + len).
    { rewrite RGC, reg_return_mapped_user, reg_return_mapped_fa. split; [reflexivity| unfold len, mfa; clear; lia]. }
    assert (LEN0 : 0 <= len) by (clear -LENF; lia).
    pose proof (gw_hull_le A c reg' cache' more len (proj1 AR) LEN0 RGO RCX) as HLE.
    pose proof (gw_lhull_le A c reg' cache' more len (proj1 AR) LEN0 RGO RCX) as LHLE.   (* [comment removed for export] *)
    pose proof (gw_eager A c reg' cache' more len Gcr RGO RCX) as EAGER.
    change (mkA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) with A' in HLE, LHLE, EAGER.
    assert (HLEN : (hN <= length (pk_chunks (a_cache A c)))%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    assert (OUTL : length out = hN) by (unfold out; apply drain_out_length; exact HLEN).
    assert (W' : WFR A').
    { pose proof (WFR_batch A k nm more W L') as X. apply X. intros _. change kQuarantineBatchClass with c. unfold nf, mfa, h in *. clear -NM1 NM2 NM3 NM4 FCC FULL NOFIT RGF3 RGF4 CAP Gk RGF6 RGF1 MCE RFR0.
      split; [rewrite MCE; replace (2 * refill_count c / 2) with (refill_count c) by (rewrite Z.mul_comm, Z_div_mult by lia; reflexivity); exact NM1|].
      split; [lia|]. split; [unfold kFreeArraySize; lia|]. split; [unfold kFreeArrayMapSize, kFaMap in *; exact NM3|]. split; [clear -NM2 FCC FULL MCE RFR0; unfold carved_count, carved_count_, kFreeArrayMapSize, kFaMap in *; subst c; lia|]. intros MU0. change (class_size c) with 8192 in RGF6. nia. }
    (* [comment removed for export] *)
    assert (FEE : fe = fac_ + mfa) by (unfold fe, fac_, free_array_of, region_beg, sb; kung_all; lia).
    assert (RANGE : a_sb A <= fe /\ fe + len <= a_sb A + kSpaceSize + 4096 /\ fe mod 4096 = 0 /\ len mod 4096 = 0 /\ 0 < len).
    { unfold fe, len. fold sb. clear -Gcr SBAL RGF3 RGF4 NM4 NM1 NOFIT LENF. unfold len in LENF. kung_all. unfold kFreeArrayMapSize in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (QB1 : q_bytes (a_qlimbo A) <= kLimboMax) by (unfold kLimboMax; exact QB).
    pose proof (wfr_budget_room A W EXTRA QB1) as ROOM0. unfold ABudget.kBudgetRoom in ROOM0.
    assert (BR : pa_eager A + len + hull_bytes (pa_lhull A) <= p_tlim (a_pl A)).   (* [comment removed for export] *)
    { unfold pa_eager. unfold len. clear -ROOM0 NM4 RGF3. lia. }
    pose proof (cr_gate A md1 fe len W TOP1 RANGE) as GATE.
    pose proof (cr_contained A md1 fe len W LED1 COV1 RANGE) as CONT.
    pose proof (cr_budget A md1 fe len W LED1 HI1 COV1 TOP1 RANGE BR) as BUD.
    match goal with |- srealizes _ (mkCfg ?ms _) _ => set (ms1 := ms) end.
    assert (A0E : ms_gpr ms1 0 = wz fe) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (A1E : ms_gpr ms1 1 = wz len) by (subst ms1; rewrite ms_gpr_MSsvc; simp_regs; reflexivity).
    assert (LENU : bv_unsigned (wz len) = len) by (apply unsigned_lit; unfold len; clear -LENF NM4 RGF3; unfold len in LENF; lia).
    assert (PRU : page_round_up_Z (bv_unsigned (ms_gpr ms1 1)) = len).
    { rewrite A1E, LENU. unfold page_round_up_Z, page_size. (first [ dand3 LENF as L0 L1 _ | destruct LENF as (L0 & L1 & _) ]). clear -L0 L1.
      replace ((len + 4096 - 1) / 4096 * 4096) with len; [reflexivity|]. pose proof (Z_div_mod_eq_full len 4096) as E. rewrite L1 in E.
      replace (len + 4096 - 1) with ((len / 4096) * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. replace (4095 / 4096) with 0 by reflexivity. lia. }
    (* [comment removed for export] *)
    pose proof (rk_CML A v [] AR) as CML. pose proof (rk_SEAL A v [] AR) as SEAL. pose proof (rk_DYG A v [] AR) as DYG. pose proof (rk_DYF A v [] AR) as DYF.
    pose proof (aobj_facts _ _ PT) as PTF. pose proof (aobj_facts _ _ PC) as PCF.
    set (W1 := [(dsp - 688, dsp); (thr + 208 + 80 * c, thr + 208 + 80 * c + 4); (Ra, Ra + 8)]) in *.
    assert (DJ1img : forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from W1 a l).
    { intros a l A1 A2. unfold W1. cbn [disjoint_from]. unfold Ra. clear -A1 A2 PTF Gcr RLO CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    assert (DJ1ctx : disjoint_from W1 (p_ctx (a_pl A) + 152) 8).
    { unfold W1. cbn [disjoint_from]. unfold Ra, apart in *. clear -PCF PCC SP3 SP5 Gcr CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    pose proof (thread_cells_munch W1 v m1 _ _ _ _ TC MUN1 eq_refl ltac:(unfold pa_tsd; clear; lia) DJ1img DJ1ctx) as TC1.
    pose proof (poison_consts_munch W1 v m1 PCo MUN1 DJ1img) as PCo1.
    assert (CGCF1 : ro_cells rsegs m1 0xa8b60 [C8 (wz CF)]) by (eapply ro_cells_transport; [exact CGCF| exact MUN1| apply DJ1img; cbn; lia]).
    assert (CML1 : ro_cells rsegs m1 (CF + 144) [C8 (wz 0)]) by (eapply ro_cells_transport; [exact CML| exact MUN1| apply DJ1img; unfold CF; cbn; lia]).
    assert (SEAL1 : ro_cells rsegs m1 0xa8bb0 [C8 (wz 1)]) by (eapply ro_cells_transport; [exact SEAL| exact MUN1| apply DJ1img; cbn; lia]).
    assert (DYG1 : ro_cells rsegs m1 0xa8bb8 [C8 (wz 0x1466dc)]) by (eapply ro_cells_transport; [exact DYG| exact MUN1| apply DJ1img; cbn; lia]).
    assert (DYF1 : ro_cells rsegs m1 0x1466dc [C4 (wz 0)]) by (eapply ro_cells_transport; [exact DYF| exact MUN1| apply DJ1img; cbn; lia]).
    assert (CSB1 : ro_cells rsegs m1 0xb1578 [C8 (wz sb)]) by (eapply ro_cells_transport; [exact CSB| exact MUN1| apply DJ1img; cbn; lia]).
    assert (CRI1 : ro_cells rsegs m1 RI_PTR [C8 (wz ri)]) by (eapply ro_cells_transport; [exact CRI| exact MUN1| apply DJ1img; unfold RI_PTR; cbn; lia]).
    assert (CITV1 : ro_cells rsegs m1 0xb1580 [C4 (wz 4294967295)]) by (eapply ro_cells_transport; [exact CITV| exact MUN1| apply DJ1img; cbn; lia]).
    assert (RMU1 : ro_cells rsegs m1 (Ra + 48) [C8 (wz (rg_mapped_user (a_reg A c)))]).
    { eapply ro_cells_transport; [exact RMU| exact MUN1|]. unfold W1. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. unfold Ra, apart in *. fold sb in SP2, SP4.
      clear -PTF SP1 Gcr RLO RHI CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
    eapply (srz_mmap_fixed_rw_contained_nf rsegs ms1 md1 (wz 222) (wz 50) TS HH1 eq_refl eq_refl).
    - unfold mmap_fixed_args. subst ms1. rewrite !ms_gpr_MSsvc. simp_regs. split; [| OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity].
      intros E. apply (f_equal bv_unsigned) in E. rewrite LENU, unsigned_lit in E by lia. clear -E LENF. lia.
    - exact fixed_rw_shape_plain.
    - rewrite PRU, A0E. exact GATE.
    - unfold fixed_contained. rewrite PRU, A0E. exact CONT.
    - rewrite PRU, A0E. exact BUD.
    - (* [comment removed for export] *)
      rewrite !PRU, !A0E. subst ms1.
      rewrite advance_apply_MSsvc, mkR_set_a0, lit_add_lit. change (mmap_ecall_pc + 4) with mmap_after_pc.
      cbn [apply_writes apply_unmaps].
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with m end.
      set (M1 := munrestrict (hidc (pa_hull A)) m m1).
      set (M2 := apply_zeros M1 [(wz fe, wz len)]).
      set (md2 := commit_model (wz 50) (wz fe) (wz len) false md1).
      set (m2 := mrestrict (hidc (pa_hull A')) M2).
      (first [ pose proof ((rk_region_facts A v [] AR c Gcr)) as dR_21; dand4 dR_21 as _ _ RG3' _ | pose proof (rk_region_facts A v [] AR c Gcr) as (_ & _ & RG3' & _) ]).
      assert (FEB : kHighMemBeg <= fe /\ fe + len <= alloc_ceiling /\ fe + len <= 2^47 /\ fe + len <= sb + kSpaceSize).
      { (first [ dand3 RANGE as R1 R2 _ | destruct RANGE as (R1 & R2 & _) ]). pose proof (region_piece_boundsT A c (proj1 AR) Gcr) as RB. cbv zeta in RB. (first [ dand9 RB as _ _ _ _ _ _ R7 R8 _ | destruct RB as (_ & _ & _ & _ & _ & _ & R7 & R8 & _) ]).
        fold sb in R1, R2, R7, R8. unfold fe, len, region_beg in *. clear -R1 R2 R7 R8 SBLO CE NM4 Gcr. kung_all. lia. }
      assert (ZSPEC : forall x : word, M2 x = if in_range fe len x then Some (Z_to_bv 8 0) else M1 x).
      { intros x. subst M2. change (Z_to_bv 64 fe) with (wa fe). apply apply_zeros_spec; [clear -FEB LENF; kung_all; lia| clear -LENF FEB; kung_all; lia| clear -FEB LENF; lia]. }
      (* [comment removed for export] *)
      assert (FE8 : fe mod 8 = 0 /\ len mod 8 = 0) by ((first [ dand5 RANGE as _ _ R3 R4 _ | destruct RANGE as (_ & _ & R3 & R4 & _) ]); clear -R3 R4; lia).
      set (sfe := sh fe) in *.
      assert (SFE : sfe = fe / 8 + kShadowOffset) by (unfold sfe, sh; reflexivity).
      (* [comment removed for export] *)
      assert (DMF : len mod kFreeArrayMapSize = 0) by (unfold kFreeArrayMapSize, kFaMap in *; exact (proj2 (proj2 LENF))).
      assert (FAE2 : region_beg (a_sb A) c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) = fe) by (unfold fe, region_beg, sb, mfa; kung_all; lia).
      assert (NEWH : forall x, in_hullb (pa_hull A') x = true -> in_hullb (pa_hull A) x = false -> (fe <= x < fe + len) \/ (sfe <= x < sfe + len / 8)).
      { intros x H1 H0. destruct (gw_hull_cases A c reg' cache' more len (proj1 AR) Gcr LEN0 DMF RGO RCX x H1) as [O|[N|N]].
        - rewrite O in H0. discriminate.
        - left. rewrite FAE2 in N. exact N.
        - right. rewrite FAE2 in N. exact N. }
      set (Wg := [(fe, fe + len); (sfe, sfe + len / 8)]).
      assert (MU12 : munch Wg m1 m2).
      { apply (restrict_grow_munch_le (pa_hull A) (pa_hull A') Wg HLE) with (full := m).
        - intros x H1 H0 OUT. cbn [outside Wg] in OUT. (first [ dand3 OUT as O1 O2 _ | destruct OUT as (O1 & O2 & _) ]). destruct (NEWH x H1 H0) as [N|N]; [exact (O1 N)| exact (O2 N)].
        - exact Hcl1.
        - intros a OUT. rewrite ZSPEC. cbn [outside Wg] in OUT. destruct OUT as (O1 & _). unfold in_range.
          replace ((fe <=? bv_unsigned a) && (bv_unsigned a <? fe + len)) with false; [reflexivity|].
          symmetry. apply andb_false_iff. destruct (Z_lt_le_dec (bv_unsigned a) fe) as [l|g]; [left; apply Z.leb_gt; exact l| right; apply Z.ltb_ge; clear -O1 g; lia]. }
      assert (WM12 : wmono rsegs m1 m2).
      { apply (restrict_grow_wmono_le (pa_hull A) (pa_hull A') HLE m1 M2 Hcl1).
        intros a V0 NZ. rewrite ZSPEC. destruct (in_range fe len a); [discriminate|]. unfold M1, munrestrict. rewrite V0. exact NZ. }
      assert (Hcl2 : forall a, hidc (pa_hull A') a = true -> m2 a = None) by (intros a Ha; unfold m2, mrestrict; rewrite Ha; reflexivity).
      assert (MI2 : mem_inv rsegs m2).
      { intros a bb Hab. unfold m2, mrestrict in Hab. destruct (hidc (pa_hull A') a) eqn:V1; [discriminate|]. rewrite ZSPEC in Hab.
        destruct (ro_addr rsegs a) eqn:RO; [| reflexivity]. exfalso. pose proof (proj1 (pa_ro_addr_iff _) RO) as ROr.
        destruct (in_range fe len a) eqn:IR.
        - unfold in_range in IR. apply andb_true_iff in IR as [I1 I2]. apply Z.leb_le in I1. clear -ROr I1 FEB. kung_all. lia.
        - unfold M1, munrestrict in Hab. destruct (hidc (pa_hull A) a) eqn:V0; [| rewrite (MI1 a bb Hab) in RO; discriminate].
          unfold hidc in V0, V1. apply negb_true_iff in V0. apply negb_false_iff in V1.
          destruct (NEWH _ V1 V0) as [N|N]; [clear -N ROr FEB; kung_all; lia|].
          pose proof (Z.div_pos fe 8 ltac:(clear -FEB; kung_all; lia) ltac:(lia)) as P. clear -N ROr SFE P. unfold kShadowOffset in *. lia. }
      (* [comment removed for export] *)
      assert (HH2 : m_halted md2 = None) by (unfold md2; rewrite commit_model_halted; exact HH1).
      assert (QB' : q_bytes (a_qlimbo A') <= kLimboMax).
      { unfold A', recA', kLimboMax. cbn [a_qlimbo]. rewrite L' in QB. rewrite q_bytes_cons, batch_bytes_ebytes in QB. cbn [ba_entries] in QB. change (ebytes []) with 0 in QB.
        unfold kQuarantineBatchBytes in QB. clear -QB. lia. }
      assert (EXTRA' : wf_extra LPA pa_site_pcs (a_pl A')) by exact EXTRA.
      pose proof (wfr_budget_room A' W' EXTRA' QB') as ROOM'. unfold ABudget.kBudgetRoom in ROOM'. change (p_tlim (a_pl A')) with (p_tlim (a_pl A)) in ROOM'.   (* [comment removed for export] *)
      (* [comment removed for export] *)
      assert (LZ2 : lazy_free (m_vm_lazy md2) (region_beg (a_sb A) c + kFreeArrayOffset + mfa) (region_beg (a_sb A) c + kFreeArrayOffset + mfa + len)).
      { pose proof (cr_lzfree_new A md1 fe len W HI1 RANGE) as X. fold md2 in X.
        replace (region_beg (a_sb A) c + kFreeArrayOffset + mfa) with fe by (unfold fe, region_beg, sb, a_sb; kung_all; clear; lia). exact X. }
      assert (LED2' : aledger_ AL_pboth (a_pl A) reg' (a_sec A) md2).
      { pose proof (cr_ledger A md1 fe len W LED1 HI1 COV1 RANGE) as L2. fold md2 in L2. exact (gw_aledger A c reg' len Gcr RGO RCX md2 L2 LZ2). }
      assert (HI2 : MInv (pa_hull A') (pa_lhull A') (pa_eager A') md2).
      { pose proof (cr_minv A md1 fe len W LED1 HI1 COV1 TOP1 RANGE BR) as X0. fold md2 in X0.
        pose proof (cr_limit A md1 fe len LED1) as LIM2. fold md2 in LIM2.
        apply (MInv_hull_mono (pa_hull A) (pa_lhull A) (pa_hull A') (pa_lhull A') (pa_eager A + len) (pa_eager A') md2 X0 LHLE).
        - intros l0 h0 Hin. right. exact (ahull_coverT A' md2 (WFT_of_WFR A' W') LED2' l0 h0 Hin).
        - rewrite EAGER. clear. lia.
        - rewrite LIM2. unfold pa_eager at 1. clear -ROOM'. lia. }
      (* [comment removed for export] *)
      assert (SHB : kLowShadowMapBeg <= sfe /\ sfe + len / 8 <= kHighMemBeg /\ sfe + len / 8 = (fe + len) / 8 + kShadowOffset).
      { destruct FE8 as [F8 L8]. (first [ dand3 FEB as B1 B2 B3 | destruct FEB as (B1 & B2 & B3) ]). rewrite SFE.
        assert (E : (fe + len) / 8 = fe / 8 + len / 8).
        { pose proof (Z_div_mod_eq_full fe 8) as X1. rewrite F8 in X1.
          replace (fe + len) with (fe / 8 * 8 + len) by (clear -X1; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
        rewrite E. assert (Q1 : fe / 8 + len / 8 <= 2^44) by (rewrite <- E; apply Z.div_le_upper_bound; [clear; lia| clear -B3; lia]).
        assert (Q2 : kHighMemBeg / 8 <= fe / 8) by (apply Z.div_le_mono; [clear; lia| exact B1]).
        assert (Q3 : 0 <= len / 8) by (apply Z.div_pos; [clear -LENF; lia| clear; lia]).
        change (kHighMemBeg / 8) with 0x2000ffff000 in Q2. clear -Q1 Q2 Q3. kung_all. lia. }
      assert (DJ12 : forall a l, (a + l <= fe \/ fe + len <= a) -> (a + l <= sfe \/ sfe + len / 8 <= a) -> disjoint_from Wg a l).
      { intros a l D1 D2. unfold Wg. cbn [disjoint_from]. split; [exact D1|]. split; [exact D2| exact I]. }
      assert (DJstk : forall a l, alloc_ceiling <= a -> disjoint_from Wg a l).
      { intros a l Ha. apply DJ12; right; [clear -Ha FEB; lia| clear -Ha SHB CE; kung_all; lia]. }
      assert (DJthr : forall a l, thr <= a -> a + l <= thr + 4096 -> disjoint_from Wg a l).
      { intros a l H1 H2. (first [ dand3 RANGE as R1 R2 _ | destruct RANGE as (R1 & R2 & _) ]). fold sb in R1, R2. unfold apart in SP4. apply DJ12.
        - clear -H1 H2 R1 FEB SP4. kung_all. lia.
        - clear -H1 H2 PTF SHB. lia. }
      assert (DJri : forall a l, ri <= a -> a + l <= ri + 4096 -> disjoint_from Wg a l).
      { intros a l H1 H2. (first [ dand3 RANGE as R1 R2 _ | destruct RANGE as (R1 & R2 & _) ]). fold sb in R1, R2. apply DJ12; right.
        - clear -H1 FEB RI0. fold sb in RI0. kung_all. lia.
        - clear -H1 SHB RLO. lia. }
      assert (DJimg : forall a l, 0x10000 <= a -> a + l <= 0x60a000 -> disjoint_from Wg a l).
      { intros a l H1 H2. apply DJ12; left; [clear -H2 FEB; kung_all; lia| clear -H2 SHB; kung_all; lia]. }
      (* [comment removed for export] *)
      assert (DJ2ctx : disjoint_from Wg (p_ctx (a_pl A) + 152) 8).
      { destruct RANGE as (R1 & _). fold sb in R1. unfold apart in SP6. fold sb in SP6. apply DJ12.
        - clear -SP6 R1 FEB. kung_all. lia.
        - clear -PCF SHB. lia. }
      pose proof (thread_cells_munch Wg m1 m2 _ _ _ _ TC1 MU12 eq_refl ltac:(unfold pa_tsd; clear; lia) DJimg DJ2ctx) as TC2.
      pose proof (poison_consts_munch Wg m1 m2 PCo1 MU12 DJimg) as PCo2.
      assert (CGCF2 : ro_cells rsegs m2 0xa8b60 [C8 (wz CF)]) by (eapply ro_cells_transport; [exact CGCF1| exact MU12| apply DJimg; cbn; lia]).
      assert (CML2 : ro_cells rsegs m2 (CF + 144) [C8 (wz 0)]) by (eapply ro_cells_transport; [exact CML1| exact MU12| apply DJimg; unfold CF; cbn; lia]).
      assert (CSB2 : ro_cells rsegs m2 0xb1578 [C8 (wz sb)]) by (eapply ro_cells_transport; [exact CSB1| exact MU12| apply DJimg; cbn; lia]).
      assert (CRI2 : ro_cells rsegs m2 RI_PTR [C8 (wz ri)]) by (eapply ro_cells_transport; [exact CRI1| exact MU12| apply DJimg; unfold RI_PTR; cbn; lia]).
      assert (CITV2 : ro_cells rsegs m2 0xb1580 [C4 (wz 4294967295)]) by (eapply ro_cells_transport; [exact CITV1| exact MU12| apply DJimg; cbn; lia]).
      assert (RMU2 : ro_cells rsegs m2 (Ra + 48) [C8 (wz (rg_mapped_user (a_reg A c)))]).
      { eapply ro_cells_transport; [exact RMU1| exact MU12| apply DJri; unfold Ra; cbn; clear -Gcr; lia]. }
      assert (STK2 : stk rsegs m2 lo (dsp + -48 + -64 + -128 + -48 + -128)) by (eapply (stk_transport_disjoint rsegs); [exact STK1| exact MU12| exact WM12| apply DJstk; exact CEIL]).
      assert (DF2 : rw_cells rsegs m2 dsp (dorec_fr thr scr)) by (eapply rw_cells_transport; [exact DF1| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia]).
      assert (LF2 : rw_cells rsegs m2 (dsp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1558) (wz T) (wz dorec_nextpc)))
        by (eapply rw_cells_transport; [exact LF1| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia]).
      assert (DRF2 : rw_cells rsegs m2 (dsp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)))
        by (eapply rw_cells_transport; [exact DRF1| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia]).
      pose proof RTF1 as RTF2. eapply rw_cells_transport in RTF2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      pose proof EFF1 as EFF2. eapply rw_cells_transport in EFF2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      pose proof MFF1 as MFF2. eapply rw_cells_transport in MFF2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      assert (FEL : sb + c * 4294967296 + kFreeArrayOffset <= fe /\ fe + len <= sb + c * 4294967296 + 4294967296) by (unfold fe, len; clear -RGF3 NM4; kung_all; lia).
      pose proof TCL1 as TCL2. eapply rw_cells_transport in TCL2; [| exact MU12| exact WM12| apply DJstk; clear -CEIL LOW; lia].
      (* [comment removed for export] *)
      pose proof LN1 as LN2. eapply rw_cells_transport in LN2; [| exact MU12| exact WM12| apply DJthr; cbn; clear -Gcr; lia].
      pose proof STA1 as STA2. eapply rw_cells_transport in STA2; [| exact MU12| exact WM12| apply DJthr; cbn; clear; lia].
      pose proof RX1 as RX2. eapply rw_cells_transport in RX2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      pose proof RNF1 as RNF2. eapply rw_cells_transport in RNF2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      pose proof RMFA1 as RMFA2. eapply rw_cells_transport in RMFA2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      pose proof RNFS1 as RNFS2. eapply rw_cells_transport in RNFS2; [| exact MU12| exact WM12| apply DJri; unfold Ra; cbn; clear -Gcr; lia].
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      (first [ pose proof ((rk_thr_words A v [] AR (thr + 2872) 2 ltac:(unfold off_th_stats; fold thr; clear; lia) ltac:(unfold off_th_stats; fold thr; cbn; clear; lia))) as dR_29; dex1 dR_29 as mmw; destruct dR_29 as [LMM MMv] | pose proof ((rk_thr_words A v [] AR (thr + 2872) 2 ltac:(unfold off_th_stats; fold thr; clear; lia) ltac:(unfold off_th_stats; fold thr; cbn; clear; lia))) as dR_29; dand3 dR_29 as mmw LMM MMv | destruct (rk_thr_words A v [] AR (thr + 2872) 2 ltac:(unfold off_th_stats; fold thr; clear; lia) ltac:(unfold off_th_stats; fold thr; cbn; clear; lia)) as (mmw & LMM & MMv) ]).
      destruct mmw as [|mm72 [|mm80 [|]]]; try (cbn in LMM; clear -LMM; lia). cbn [map] in MMv.
      assert (NN1 : forall a, 0 <= a < 2^64 -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> v (wz a) <> None -> m1 (wz a) <> None).
      { intros a H0 H1. apply (wmono_NNR _ _ a WM1); [exact H1| exact H0]. }
      assert (MM1 : rw_cells rsegs m1 (thr + 2872) [C8 mm72; C8 mm80]).
      { eapply rw_cells_transport; [exact MMv| exact MUN1| exact WM1|]. unfold W1. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        unfold Ra, apart in *. clear -PTF PTC SP1 Gcr CEIL LOW CE SPR. kung_all. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      pose proof MM1 as MM2. eapply rw_cells_transport in MM2; [| exact MU12| exact WM12| apply DJthr; cbn; clear; lia].
      (* [comment removed for export] *)
      assert (FAB : fac_ = region_beg (a_sb A) c + kFreeArrayOffset) by (unfold fac_, free_array_of, region_beg, sb; kung_all; lia).
      pose proof (ar_regions _ _ _ _ _ (proj2 AR) c Gcr) as RR. unfold region_repr_ in RR. cbv zeta in RR. change (a_sb A) with sb in RR. rewrite FAE in RR.
      (first [ dand13 RR as _ _ _ _ _ _ _ _ _ _ _ MFAv _ | destruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MFAv & _) ]). fold fac_ mfa in MFAv.
      assert (VISFA : forall x, fe <= x < fe + len -> hidc (pa_hull A') (wz x) = false).
      { intros x Hx. unfold hidc. apply negb_false_iff. rewrite unsigned_lit by (clear -Hx FEB LENF; kung_all; lia).
        apply (gw_vis_fa A c reg' cache' more len Gcr LEN0 RCX ltac:(fold mfa; clear -RGF3 LENF; lia)). fold mfa. rewrite <- FAB. clear -Hx FEE RGF3. lia. }
      assert (ZFE : forall x, fe <= x < fe + len -> m2 (wz x) = Some (Z_to_bv 8 0)).
      { intros x Hx. unfold m2, mrestrict. rewrite (VISFA x Hx), ZSPEC. unfold in_range. rewrite unsigned_lit by (clear -Hx FEB LENF; kung_all; lia).
        replace ((fe <=? x) && (x <? fe + len)) with true; [reflexivity|]. symmetry. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; clear -Hx; lia. }
      assert (FACB : kHighMemBeg <= fac_) by (rewrite FAB; unfold region_beg; fold sb; clear -SBLO Gcr; kung_all; lia).
      assert (MJ2 : mapped m2 (fac_ + 4 * nf) (Z.of_nat (4 * hN))).
      { intros i0 Hi0. assert (HNE : Z.of_nat (4 * hN) = 4 * h) by (unfold hN; clear -RFR0; lia). rewrite HNE in Hi0.
        destruct (Z_lt_le_dec (fac_ + 4 * nf + i0) fe) as [Lo|Hi].
        - assert (X0 : 0 <= fac_ + 4 * nf + i0 < 2^64 /\ 0x60a000 <= fac_ + 4 * nf + i0 /\ kHighMemBeg <= fac_ + 4 * nf + i0) by (rewrite FEE in Lo; clear -Lo Hi0 FEB FEE FACB RGF3 RGF5 LENF; unfold nf in *; kung_all; lia).
          rewrite (MU12 (wz (fac_ + 4 * nf + i0))).
          + apply NN1; [exact (proj1 X0)| right; exact (proj1 (proj2 X0))|]. replace (fac_ + 4 * nf + i0) with (fac_ + (4 * nf + i0)) by (clear; lia). apply MFAv. rewrite FEE in Lo. clear -Lo Hi0 RGF5. unfold nf in *. lia.
          + rewrite unsigned_lit by exact (proj1 X0). unfold Wg. cbn [outside]. split; [clear -Lo; lia|]. split; [| exact I]. clear -X0 SHB FEB Lo. kung_all. lia.
        - rewrite (ZFE (fac_ + 4 * nf + i0)); [discriminate|]. split; [exact Hi|]. rewrite FEE. unfold len. clear -Hi0 NM1. lia. }
      (first [ pose proof ((mapped_u32arr m2 (fac_ + 4 * nf) hN MJ2 ltac:(clear -FEB FEE RGF3; unfold nf; kung_all; lia) ltac:(unfold hN; rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -RFR0; lia); clear -FEB FEE NM1 LENF RFR0; unfold len in *; kung_all; lia))) as dR_31; dex1 dR_31 as junk2; destruct dR_31 as [LJ2 JUNK2] | pose proof ((mapped_u32arr m2 (fac_ + 4 * nf) hN MJ2 ltac:(clear -FEB FEE RGF3; unfold nf; kung_all; lia) ltac:(unfold hN; rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -RFR0; lia); clear -FEB FEE NM1 LENF RFR0; unfold len in *; kung_all; lia))) as dR_31; dand3 dR_31 as junk2 LJ2 JUNK2 | destruct (mapped_u32arr m2 (fac_ + 4 * nf) hN MJ2 ltac:(clear -FEB FEE RGF3; unfold nf; kung_all; lia) ltac:(unfold hN; rewrite Nat2Z.inj_mul, Z2Nat.id by (clear -RFR0; lia); clear -FEB FEE NM1 LENF RFR0; unfold len in *; kung_all; lia)) as (junk2 & LJ2 & JUNK2) ]).
      (* [comment removed for export] *)
      assert (SHFA : sfe = sh (region_beg (a_sb A) c + kFreeArrayOffset) + mfa / 8).
      { unfold sfe. rewrite FEE, FAB. apply sh_add; [| clear -RGF4; unfold kFreeArrayMapSize in *; lia].
        (first [ pose proof ((gw_align A c len (proj1 AR) Gcr LEN0 DMF)) as dR_32; dand3 dR_32 as _ FA64 _ | pose proof (gw_align A c len (proj1 AR) Gcr LEN0 DMF) as (_ & FA64 & _) ]). apply (mod0_down _ 64 8); [exists 8; reflexivity| exact FA64]. }
      assert (MS2 : mapped m2 sfe (len / 8)).
      { intros i0 Hi0.
        assert (ZR : 0 <= sfe + i0 < 2^64 /\ 0x60a000 <= sfe + i0 /\ sfe + i0 < fe) by (clear -Hi0 SHB FEB; kung_all; lia).
        assert (GH : ghost_hs_ (a_pl A) (sfe + i0)).
        { apply (gw_prim_shadow_ghost A (proj1 AR)). fold sb. destruct RANGE as (R1 & _). fold sb in R1.
          assert (Q1 : sb / 8 <= fe / 8) by (apply Z.div_le_mono; [clear; lia| exact R1]).
          assert (Q2 : (fe + len) / 8 <= (sb + kSpaceSize) / 8) by (apply Z.div_le_mono; [clear; lia| clear -FEB; lia]).
          assert (Q3 : (sb + kSpaceSize) / 8 = sb / 8 + kSpaceSize / 8).
          { pose proof (Z_div_mod_eq_full sb 8) as X0. rewrite (mod0_down sb 4096 8 ltac:(exists 512; reflexivity) SBAL) in X0.
            replace (sb + kSpaceSize) with (sb / 8 * 8 + kSpaceSize) by (clear -X0; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
          (first [ dand3 SHB as _ _ S3 | destruct SHB as (_ & _ & S3) ]). unfold sh. rewrite SFE in *. clear -Hi0 Q1 Q2 Q3 S3. lia. }
        assert (VIS : hidc (pa_hull A') (wz (sfe + i0)) = false).
        { unfold hidc. apply negb_false_iff. rewrite unsigned_lit by exact (proj1 ZR).
          apply (gw_vis_fsh A c reg' cache' more len (proj1 AR) Gcr LEN0 DMF RCX ltac:(fold mfa; clear -RGF3 LENF; lia)). fold mfa. rewrite SHFA.
          assert (D2 : (mfa + len) / 8 = mfa / 8 + len / 8).
          { pose proof (Z_div_mod_eq_full mfa 8) as X0. assert (M8 : mfa mod 8 = 0) by (clear -RGF4; unfold kFreeArrayMapSize in *; lia). rewrite M8 in X0.
            replace (mfa + len) with (mfa / 8 * 8 + len) by (clear -X0; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
          rewrite D2. assert (0 <= mfa / 8) by (apply Z.div_pos; [clear -RGF3; lia| clear; lia]). clear -Hi0 H. lia. }
        destruct HID as [HG _]. destruct (HG _ GH) as [PRES _].
        unfold m2, mrestrict. rewrite VIS, ZSPEC. unfold in_range. rewrite unsigned_lit by exact (proj1 ZR).
        replace ((fe <=? sfe + i0) && (sfe + i0 <? fe + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; exact (proj2 (proj2 ZR))).
        unfold M1, munrestrict. destruct (hidc (pa_hull A) (wz (sfe + i0))) eqn:V0; [exact PRES|].
        apply NN1; [exact (proj1 ZR)| right; exact (proj1 (proj2 ZR))|]. unfold v, aview_of, mrestrict. rewrite V0. exact PRES. }
      pose proof (mapped_rw_cells m2 sfe (len / 8) MS2 ltac:(clear -SHB; kung_all; lia) ltac:(apply Z.div_pos; [clear -LENF; lia| clear; lia]) ltac:(clear -SHB; kung_all; lia)) as SHN2.
      (* [comment removed for export] *)
      set (Q2 := fun ms' : machine_state => exists (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 statv' : word) (m' : mem),
           ((more <> [] /\ ms' = MS (head_regs (wz dsp) gp (cl_tp LPA) T s10 s11 (wz dorec_nextpc) tn a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 t4 t5 t6 (wz b) s6' s7' s8' s9') F (wz dorec_head) fc None m' (seg_rom rsegs)
             /\ rw_cells rsegs m' dsp (dorec_fr thr scr) /\ stk rsegs m' lo dsp)
            \/ (more = [] /\ ms' = MS (mkR (wz recycle_ret) (wz (dsp + 112)) gp (cl_tp LPA) t0 t1 t2 (wz QINST) (wz (thr + 80)) (wz 0) a1 a2 a3 a4 a5 a6 a7
                                        xs2 (wz stkobj) (wz (thr + 208)) xs5 (wz (2^20)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc (wz recycle_ret)) fc None m' (seg_rom rsegs)
             /\ stk rsegs m' lo (dsp + 112))) /\
           tmp_hdr sb m' T more /\
           rw_cells rsegs m' (thr + 208 + 80 * c) [C4 (wz (max_count c - h + 1)); C4 (wz (max_count c)); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat (max_count c - h)) (wz kk)))] /\
           rw_cells rsegs m' (thr + 208 + 2576) [C8 statv'] /\
           rw_cells rsegs m' Ra [C8 (wz 0)] /\ rw_cells rsegs m' (Ra + 16) [C8 (wz (nf + h))] /\ rw_cells rsegs m' (Ra + 24) [C8 (wz nm)] /\
           rw_cells rsegs m' (Ra + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] /\
           u32arr rsegs m' (fac_ + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (max_count c - h)) ks)) /\
           bytes_at rsegs m' sfe (repeat (Z_to_bv 8 250) (Z.to_nat (len / 8))) /\
           rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + len))] /\
           munch [(dsp - 688, dsp); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                  (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 24, Ra + 32); (Ra + 80, Ra + 88);
                  (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h); (sfe, sfe + len / 8); (thr + 2872, thr + 2888)] m2 m' /\
           wmono rsegs m2 m' /\ mem_inv rsegs m').
      eapply (srz_evt_restrict rsegs (pa_hull A') (hull_segsR A') pa_wxR _ (pa_eager A') Q2 _ md2 TS HI2 HH2).
      { rewrite restrict_MS. fold m2.
        assert (USP : bv_unsigned (wz dsp) = dsp) by (apply unsigned_lit; clear -CE LOW SPHI HI47 SPR CEIL; lia).
        replace (dsp + -48 + -64 + -128 + -48 + -128) with (bv_unsigned (wz dsp) + -48 + -64 + -128 + -48 + -128) by (rewrite USP; reflexivity).
        unfold len, nm. rewrite <- HSH.
        eapply (batch_free_drainmap_post gp (cl_tp LPA) s10 s11 (wz dsp) F fc v lo T b scr
                  (wz stkobj) s9 s8 s7 (wz (2^20)) xs5 (wz (thr + 208)) (wz stkobj) xs2 (wz (thr + 80)) (wz QINST) (wz recycle_ret)
                  pa_tsd (p_ctx (a_pl A)) thr sb ri)
          with (kb := kk) (m7 := m2) (tn := tn) (tf := tf) (tl := tl) (ts := q_bytes more) (maxc := max_count c) (ks := ks) (statv := statv) (junk := junk2)
               (nf := nf) (mfa := mfa) (nfs := nfs) (v88 := v88) (mm72 := mm72) (mm80 := mm80)
               (lscr := lscr) (scr2 := scr2) (scr3 := scr3) (scr4 := scr4) (a0r := wz fe).
        all: rewrite ?HSH.
        all: try assumption.
        all: try (rewrite ?unsigned_lit by (clear -CE LOW SPHI HI47 SPR CEIL; lia)).
        all: try assumption.
        all: cycle -2.
        1: { intros NE a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' DF' TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' STK'.
             apply evt_done. subst Q2. first [ hotw_ex16 a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' | exists a1y, a2y, a3y, a4y, a5y, a6y, a7y, t0y, t1y, t2y, t3y, t4y, t5y, t6y, statv', m' ].
             split; [left; split; [unfold tn in NE; clear -NE; intros E; apply NE; rewrite E; reflexivity| split; [reflexivity| exact (conj DF' STK')]]|].
             exact (conj TC' (conj LN' (conj ST' (conj RX' (conj RNF' (conj RMFA' (conj RNFS' (conj ARR' (conj SHF' (conj MM' (conj MUN2 (conj WM2 MI')))))))))))). }
        1: { intros EQ a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' DF' TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' STK'.
             apply evt_done. subst Q2. first [ hotw_ex16 a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m' | exists a1y, a2y, a3y, a4y, a5y, a6y, a7y, t0y, t1y, t2y, t3y, t4y, t5y, t6y, statv', m' ].
             split; [right; split; [unfold tn in EQ; clear -EQ; destruct more; [reflexivity| cbn in EQ; lia]| split; [reflexivity| exact STK']]|].
             exact (conj TC' (conj LN' (conj ST' (conj RX' (conj RNF' (conj RMFA' (conj RNFS' (conj ARR' (conj SHF' (conj MM' (conj MUN2 (conj WM2 MI')))))))))))). }
        all: first [ assumption | exact SHN2 | exact TCL2
                   | clear -SPA SPR CE LOW SPHI HI47 CEIL; lia
                   | unfold pa_tsd; clear; lia
                   | apply (mod0_down _ 16 8); [exists 2; reflexivity| exact BAL]
                   | clear -SBRI RHI; lia
                   | unfold kk; clear -KB0 KBH; lia
                   | clear -MCR; lia
                   | clear -MCE RFR0; unfold h; lia
                   | unfold nf; clear; lia
                   | clear -RGF5 CAPN RFR0; unfold nf, mfa, h in *; kung_all; lia
                   | clear -NOFIT MCE RFR0; unfold nf, mfa, h in *; lia
                   | clear -RGF3; unfold mfa; kung_all; lia
                   | clear -RGF4; unfold mfa; exact RGF4
                   | change (sb + 24 * 4294967296 + kFreeArrayOffset + mfa) with fe; apply unsigned_lit; clear -FEB LENF; kung_all; lia
                   | reflexivity
                   | match goal with |- ?g => idtac "UNSOLVED2:" g end ]. }
      intros msr2 md3 HQ2 HI3 SB3 Hcl3.
      (first [ dex16 HQ2 as a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m3; dand14 HQ2 as CASE TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' | dand30 HQ2 as a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y statv' m3 CASE TC' LN' ST' RX' RNF' RMFA' RNFS' ARR' SHF' MM' MUN2 WM2 MI' | destruct HQ2 as (a1y & a2y & a3y & a4y & a5y & a6y & a7y & t0y & t1y & t2y & t3y & t4y & t5y & t6y & statv' & m3 & CASE & TC' & LN' & ST' & RX' & RNF' & RMFA' & RNFS' & ARR' & SHF' & MM' & MUN2 & WM2 & MI') ]).
      assert (MSE : exists regs pcw, msr2 = MS regs F pcw fc None m3 (seg_rom rsegs)) by (destruct CASE as [(_ & -> & _)|(_ & -> & _)]; eexists _, _; reflexivity).
      (first [ dex2 MSE as regs pcw | dand3 MSE as regs pcw MSE | destruct MSE as (regs & pcw & MSE) ]). rewrite MSE in Hcl3 |- *. rewrite unrestrict_MS. cbn [ms_mem] in Hcl3.
      match goal with |- context [munrestrict _ (ms_mem ?X) _] => change (ms_mem X) with M2 end.
      set (Mf := munrestrict (hidc (pa_hull A')) M2 m3).
      pose proof (same_but_materialized_frame _ _ SB3) as FRM3.
      assert (VIEW : aview_of (pa_hull A') Mf = m3).
      { unfold aview_of, Mf. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact Hcl3. }
      set (W2 := [(dsp - 688, dsp); (thr + 208 + 80 * c, thr + 208 + 80 * c + 80); (thr + 208 + 2576, thr + 208 + 2584);
                  (Ra, Ra + 8); (Ra + 16, Ra + 24); (Ra + 24, Ra + 32); (Ra + 80, Ra + 88);
                  (fac_ + 4 * nf, fac_ + 4 * nf + 4 * h); (sfe, sfe + len / 8); (thr + 2872, thr + 2888)]) in *.
      assert (NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (wz a) <> None -> m3 (wz a) <> None).
      { intros a H0 H1 H2 Hv. apply (wmono_NNR _ _ a WM2); [exact H1| clear -H0 H2; lia|]. apply (wmono_NNR _ _ a WM12); [exact H1| clear -H0 H2; lia|].
        apply NN1; [clear -H0 H2; lia| exact H1| exact Hv]. }
      assert (AG3 : forall a, 0 <= a < 2^64 -> outside W1 a -> outside Wg a -> outside W2 a -> m3 (wz a) = v (wz a)).
      { intros a Ha O1 Og O2. rewrite (MUN2 (wz a)) by (rewrite unsigned_lit by exact Ha; exact O2).
        rewrite (MU12 (wz a)) by (rewrite unsigned_lit by exact Ha; exact Og). apply (MUN1 (wz a)). rewrite unsigned_lit by exact Ha. exact O1. }
      (* [comment removed for export] *)
      set (Wn := fun a => dsp - 688 <= a < dsp).
      set (SHP := fun a : Z => False).
      assert (MU : forall a, 0 <= a < 2^64 -> ~ rp_foot A c k reg' Wn SHP a -> m3 (wz a) = v (wz a)).
      { intros a Ha NF. unfold rp_foot in NF. rewrite RGC, reg_return_mapped_fa in NF. subst Wn SHP. cbv beta in NF.
        fold thr sb ri in NF. fold Ra fac_ nf mfa in NF.
        apply (AG3 a Ha); unfold W1, Wg, W2; cbn [outside]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; intros Xa; apply NF.
        - left. exact Xa.
        - do 3 right; left. clear -Xa. lia.
        - do 5 right; left. exact Xa.
        - do 7 right; left. rewrite FEE in Xa. unfold len in Xa. clear -Xa RGF5. unfold nf in *. lia.
        - do 8 right. rewrite <- FEE. fold sfe. unfold len in Xa. exact Xa.
        - left. exact Xa.
        - do 3 right; left. exact Xa.
        - do 4 right; left. clear -Xa. lia.
        - do 5 right; left. exact Xa.
        - do 6 right; left. clear -Xa. lia.
        - do 6 right; left. clear -Xa. lia.
        - do 6 right; left. clear -Xa. lia.
        - do 7 right; left. clear -Xa NM1. lia.
        - do 8 right. rewrite <- FEE. fold sfe. unfold len in Xa. exact Xa.
        - do 4 right; left. clear -Xa. lia. }
      (* [comment removed for export] *)
      set (Wall := W1 ++ Wg ++ W2).
      assert (MUNall : munch Wall v m3).
      { assert (S1 : sub_fp W1 Wall) by (unfold sub_fp, Wall; intros y Hy; rewrite !AFreeH0.outside_app in Hy; exact (proj1 Hy)).
        assert (S2 : sub_fp Wg Wall) by (unfold sub_fp, Wall; intros y Hy; rewrite !AFreeH0.outside_app in Hy; exact (proj1 (proj2 Hy))).
        assert (S3 : sub_fp W2 Wall) by (unfold sub_fp, Wall; intros y Hy; rewrite !AFreeH0.outside_app in Hy; exact (proj2 (proj2 Hy))).
        exact (munch_trans _ _ _ _ (munch_weaken _ _ _ _ S1 MUN1) (munch_trans _ _ _ _ (munch_weaken _ _ _ _ S2 MU12) (munch_weaken _ _ _ _ S3 MUN2))). }
      assert (WMall : wmono rsegs v m3) by exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM12 WM2)).
      assert (WNH : forall a, Wn a -> alloc_ceiling <= a) by (subst Wn; cbv beta; intros a Ha; clear -Ha CEIL LOW; lia).
      assert (SHPW : forall a, SHP a -> sh b <= a < sh b + class_size c / 8) by (subst SHP; cbv beta; intros a []).
      pose proof (bv_ne_live A v [] k more AR W L') as NE_live.
      pose proof (bv_ne_batch A k more W L') as NEB.
      pose proof (bv_ne_rest A v [] k more AR W L') as NE_rest.
      pose proof (bv_ne_limbo A v [] k more AR W L') as NEL.
      (* [comment removed for export] *)
      assert (DISJ : forall a l, 0 < l ->
               (Ra + 32 <= a /\ a + l <= Ra + 80) \/ (Ra + 96 <= a /\ a + l <= Ra + 128) \/ (fac_ <= a /\ a + l <= fac_ + 4 * nf) \/ (T <= a /\ a + l <= uspd) ->
               disjoint_from Wall a l).
      { intros a l Hl Ha. unfold Wall, W1, Wg, W2. cbn [app disjoint_from].
        assert (KS0 : dsp <= T /\ uspd <= 2^47 /\ alloc_ceiling <= dsp - 688) by (clear -CEIL LOW SPHI HI47; lia).
        assert (K1 : kHighMemBeg <= fac_ /\ fac_ + 4 * nf <= fe /\ fe + len <= sb + kSpaceSize /\ sb + kSpaceSize <= ri /\ fac_ + 4 * nf + 4 * h <= fe + len /\
                     sb <= fac_ /\ ri + 4096 <= alloc_ceiling /\ kHighMemBeg <= sb /\ 0 <= len /\ 0 <= nf /\ 0 <= h).
        { fold sb in RI0. clear -FACB FEE RGF5 FEB RI0 NM1 FAB RHI SBLO Gcr LEN0 RFR0. unfold len, nf, h, fac_, free_array_of, region_beg in *. kung_all. lia. }
        assert (K2 : sfe + len / 8 <= kHighMemBeg /\ kLowShadowMapBeg <= sfe) by (clear -SHB; lia).
        assert (THRD : (ri <= a /\ a + l <= ri + 4096) \/ (sb <= a /\ a + l <= sb + kSpaceSize) \/ alloc_ceiling <= a -> a + l <= thr \/ thr + 4096 <= a).
        { unfold apart in SP1, SP4. fold sb in SP4. clear -SP1 SP4 PTC Hl. kung_all. lia. }
        assert (ZONE : (ri <= a /\ a + l <= ri + 4096) \/ (sb <= a /\ a + l <= sb + kSpaceSize) \/ alloc_ceiling <= a).
        { destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [left| left| right; left| right; right]; clear -Ha Hl KS0 K1 Gcr; try unfold Ra in *; lia. }
        specialize (THRD ZONE). clear ZONE.
        destruct Ha as [Ha|[Ha|[Ha|Ha]]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit;
          first [ clear -Ha Hl KS0 K1 K2 Gcr; try unfold Ra in *; kung_all; lia
                | clear -Ha Hl THRD Gcr; lia ]. }
      assert (OUT : forall a, (Ra + 32 <= a < Ra + 80 \/ Ra + 96 <= a < Ra + 128 \/ fac_ <= a < fac_ + 4 * nf \/ T <= a < uspd) -> outside Wall a).
      { intros a Ha. apply (disjoint_outside _ a 1); [| clear; lia]. apply DISJ; [clear; lia|]. clear -Ha. lia. }
    assert (P_mx : u64_at rsegs m3 (ri + 128 * c) 0) by (apply u64_of_rw; [clear; lia| exact RX']).
    (* [comment removed for export] *)
    assert (KSE : firstn (length (pk_chunks (a_cache A c))) ks = map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) (pk_chunks (a_cache A c))) by exact KSF.
    assert (OUTW : firstn (Z.to_nat h) (skipn (Z.to_nat (max_count c - h)) ks) = map (fun k0 => wz (k0 * class_size c / kCompactPtrScale)) out).
    { unfold out, drain_out. fold hN. replace (Z.to_nat (max_count c - h)) with (length (pk_chunks (a_cache A c)) - hN)%nat by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      rewrite firstn_skipn_comm. replace (length (pk_chunks (a_cache A c)) - hN + hN)%nat with (length (pk_chunks (a_cache A c))) by (clear -HLEN; lia).
      rewrite KSE, skipn_map. reflexivity. }
    assert (MFA3 : mapped m3 (free_array_beg sb c) nm).
    { rewrite FAE. fold fac_. intros i0 Hi0. destruct (Z_lt_le_dec (fac_ + i0) fe) as [Lo|Hi].
      - apply NN; [clear -Hi0 FACB; kung_all; lia| right; clear -Hi0 FACB; kung_all; lia| clear -Lo FEB LENF; lia|]. apply MFAv. rewrite FEE in Lo. clear -Lo Hi0. lia.
      - apply (wmono_NNR _ _ (fac_ + i0) WM2); [right; clear -Hi0 FACB; kung_all; lia| clear -Hi0 Hi FEB FEE NM1 LENF; unfold len in *; kung_all; lia|].
        rewrite (ZFE (fac_ + i0)); [discriminate|]. split; [exact Hi|]. rewrite FEE. unfold len. clear -Hi0. lia. }
    assert (P_regc : region_repr_ LPA sb (reg' c) m3 c).
    { rewrite RGC. pose proof (ar_regions _ _ _ _ _ (proj2 AR) c Gcr) as RR0. change (a_sb A) with sb in RR0.
      (first [ pose proof ((rk_region_facts A v [] AR c Gcr)) as dR_36; dand6 dR_36 as _ _ RG3 _ RG5 _ | pose proof (rk_region_facts A v [] AR c Gcr) as (_ & _ & RG3 & _ & RG5 & _) ]).
      apply (region_return_of_cells_grow v m3 sb (a_reg A c) c out (wz (bv_unsigned nfs + h)) v88 nm Gcr RR0).
      - rewrite OUTL. unfold hN, nf in *. clear -RG3 RG5 CAPN RFR0. kung_all. lia.
      - clear -NM1 NM4 RFR0. unfold nf, h in *. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUNall (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE; kung_all; lia). apply OUT. left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite RIA in Ha. apply (MUNall (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RLO RHI CE; kung_all; lia). apply OUT. right; left. unfold Ra. clear -Ha. lia.
      - intros a Ha. rewrite FAE in Ha. apply (MUNall (wz a)). rewrite unsigned_lit by (clear -Ha Gcr RG3 RG5 SBLO SBRI RHI CE; unfold free_array_of in *; kung_all; lia). apply OUT. right; right; left. unfold fac_, nf. clear -Ha. lia.
      - exact MFA3.
      - intros a Ha Hv. rewrite RBE in Ha. apply NN; [| right| | exact Hv]; clear -Ha Gcr RGF2 SBLO SBRI RHI CE; kung_all; lia.
      - rewrite RIA, OUTL. unfold hN. rewrite Z2Nat.id by (clear -RFR0; unfold h; lia). fold nf. unfold Ra, ri in RNF'. exact RNF'.
      - rewrite RIA. unfold Ra, ri in RMFA'. exact RMFA'.
      - rewrite RIA. unfold Ra, ri in RNFS'. exact RNFS'.
      - rewrite FAE, <- OUTW. fold nf. unfold fac_, sb in ARR'. exact ARR'. }
    (* [comment removed for export] *)
    assert (KKE : forall k', k' * class_size c / kCompactPtrScale = 512 * k').
    { intros k'. change (class_size c) with 8192. unfold kCompactPtrScale. replace (k' * 8192) with (512 * k' * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
    assert (ENC : forall k', In k' (pk_chunks (a_cache A c)) \/ k' = k -> 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { intros k' Hk'. assert (KR' : 0 <= k' < carved_count A c) by (destruct Hk' as [Hk'| ->]; [exact (KRG k' Hk')| exact Gk]).
      rewrite KKE. change (class_size c) with 8192 in RGF6. clear -KR' RGF6 RGF1 RGF2. kung_all. lia. }
    assert (ENT : forall i0 k', nth_error (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]) i0 = Some k' ->
              nth_error (upd ks (Z.to_nat (max_count c - h)) (wz kk)) i0 = Some (wz (k' * class_size c / kCompactPtrScale)) /\ 0 <= k' * class_size c / kCompactPtrScale < 2^32).
    { assert (KL : length (drain_keep (pk_chunks (a_cache A c)) hN) = (length (pk_chunks (a_cache A c)) - hN)%nat) by (apply drain_keep_length; exact HLEN).
      assert (MH : Z.to_nat (max_count c - h) = (length (pk_chunks (a_cache A c)) - hN)%nat) by (unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
      intros i0 k' Hk'. destruct (Nat.lt_ge_cases i0 (length (pk_chunks (a_cache A c)) - hN)) as [LT|GE].
      - rewrite nth_error_app1 in Hk' by (rewrite KL; exact LT). unfold drain_keep in Hk'. rewrite nth_error_firstn in Hk'.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)) - hN)); [| exfalso; clear -LT H; lia].
        split; [| apply ENC; left; eapply nth_error_In; exact Hk'].
        rewrite nth_error_upd_other by (rewrite MH; clear -LT; lia).
        pose proof (f_equal (fun l => nth_error l i0) KSF) as E. cbv beta in E. rewrite nth_error_firstn in E.
        destruct (Nat.ltb_spec i0 (length (pk_chunks (a_cache A c)))); [| exfalso; clear -LT H0; lia]. rewrite E, nth_error_map, Hk'. reflexivity.
      - rewrite nth_error_app2 in Hk' by (rewrite KL; exact GE). rewrite KL in Hk'. destruct (i0 - (length (pk_chunks (a_cache A c)) - hN))%nat as [|x] eqn:EQ; cbn in Hk'; [injection Hk' as <-| destruct x; discriminate].
        assert (i0 = (length (pk_chunks (a_cache A c)) - hN)%nat) by (clear -GE EQ; lia). subst i0. split; [| apply ENC; right; reflexivity].
        rewrite MH. rewrite nth_error_upd_same by (rewrite LKS; unfold hN, cntc in *; clear -FULL MCR RFR0; lia). rewrite KKE. reflexivity. }
    pose proof LN' as LNx.
    replace (max_count c - h + 1) with (Z.of_nat (length (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]))) in LNx
      by (rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0; lia).
    pose proof (line_of_cells m3 (thr + 208 + 80 * c) c (upd ks (Z.to_nat (max_count c - h)) (wz kk)) (drain_keep (pk_chunks (a_cache A c)) hN ++ [k]) (a_cache_inited A) Gcr CI
                  ltac:(rewrite upd_length; exact LKS) ltac:(rewrite length_app, (drain_keep_length _ _ HLEN); cbn [length]; unfold hN, cntc in *; clear -FULL MCE RFR0 MCR; lia) ENT
                  LNx) as P_linec.
    rewrite <- CAE in P_linec.
    replace (thr + 208 + 80 * c) with (thr + off_th_per_class c) in P_linec by (unfold off_th_per_class, off_th_alloc_cache, kPerClassSize; clear; lia).
    assert (MFA8 : rg_mapped_fa (a_reg A c) mod 8 = 0) by (apply (mod0_down _ kFreeArrayMapSize 8); [exists (2^15); reflexivity| exact RGF4]).
    assert (R'E : rg_mapped_user (reg' c) = rg_mapped_user (a_reg A c) /\ rg_allocated_user (reg' c) = rg_allocated_user (a_reg A c) /\
                  rg_mapped_fa (a_reg A c) <= rg_mapped_fa (reg' c) /\ rg_mapped_fa (reg' c) <= kFreeArraySize /\ rg_mapped_fa (reg' c) mod 8 = 0).
    { rewrite RGC, reg_return_mapped_user, reg_return_allocated, reg_return_mapped_fa. fold mfa. clear -NM1 NM3 NM4 NOFIT. unfold kFreeArraySize, kFaMap in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity; lia. }
    (first [ pose proof ((chunk_shadow A v [] AR c k Gcr Gk)) as dR_37; dand4 dR_37 as CS1 CS2 CS3 CS4 | pose proof (chunk_shadow A v [] AR c k Gcr Gk) as (CS1 & CS2 & CS3 & CS4) ]). fold sb in CS1, CS2, CS3, CS4.
    change (chunk_addr sb c k) with b in CS1, CS2, CS3, CS4.
    assert (AGSH : forall z, sh b <= z < sh b + class_size c / 8 -> m3 (wz z) = v (wz z)).
    { intros z Hz. apply (AG_shadow_maps A v m3 [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU z).
      - exact (heap_shadow_rangeT A z (WFT_of_WFR A W) (CS2 z Hz)).
      - intros [].
      - rewrite RGC, reg_return_mapped_fa. change (free_array_of (a_sb A) c) with fac_. change (rg_mapped_fa (a_reg A c)) with mfa. rewrite <- FEE. change (sh fe) with sfe. change (nm - mfa) with len.
        intros X. assert (SHBD : sh b + class_size c / 8 <= sfe).
        { rewrite SFE. unfold sh. change (class_size c) with 8192. change (8192 / 8) with 1024.
          assert (BE : b = sb + 24 * 2^32 + 16 * (512 * k)) by exact BFORM.
          assert (Qd : (b + 8192) / 8 <= fe / 8) by (apply Z.div_le_mono; [clear; lia| clear -BE KB0 KBH FEL; unfold c, kQuarantineBatchClass in *; kung_all; lia]).
          replace (b + 8192) with (1024 * 8 + b) in Qd by (clear; lia). rewrite Z.div_add_l in Qd by (clear; lia). clear -Qd. lia. }
        clear -X Hz SHBD. lia. }
    assert (VSH : bytes_at rsegs m3 (sh b) (pshadow_free c)).
    { eapply bytes_at_xfer; [exact RBSH|]. intros z Hz. apply AGSH. unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size c) with 8192; clear; lia). exact Hz. }
    assert (P_fash : bytes_at rsegs m3 (sh (fac_ + mfa)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat ((rg_mapped_fa (reg' c) - mfa) / 8)))).
    { rewrite RGC, reg_return_mapped_fa. rewrite <- FEE. exact SHF'. }
    pose proof (recp_arepr A v m3 [] c k more reg' cache' AR W Wn WNH SHP SHPW CVe NE_live NEB NE_rest
                  CAO ltac:(intros k' Hk'; rewrite CAE in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|[<-|[]]]; [left; exact (proj2 (drain_in_iff _ hN k') (or_introl Hk'))| right; reflexivity])
                  RGO R'E ltac:(intros k' Hk'; rewrite RGC, reg_return_free in Hk'; apply in_app_iff in Hk'; destruct Hk' as [Hk'|Hk']; [left; exact Hk'| right; exact (proj2 (drain_in_iff _ hN k') (or_intror Hk'))])
                  MU NN P_mx P_regc P_linec VSH P_fash more) as AR'.
    change (recA' _ _ _ _) with A' in AR'.
    (* [comment removed for export] *)
    assert (INmore : forall b' e', In b' more -> In e' (ba_entries b') -> In e' ([] ++ q_entries more)).
    { intros b' e' Hb' He'. cbn [app]. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He'). }
    assert (RCM : forall cur, match cur with None => True | _ => False end -> rcells A' m3 T cur more).
    { intros cur Hcur. constructor.
      - exact AR'.
      - exact TC'.
      - apply (tmp_chain_xfer A v m3 [] c k k _ more reg' cache' AR W L' Wn WNH SHP SHPW CVe NEB R'E MU more); [intros b' Hb'; exact Hb'| exact RCH].
      - intros b' e' Hb' He'. apply (lentry_xfer A v m3 [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU NN e').
        + apply (limbo_in A k _ more W L'). exact (INmore b' e' Hb' He').
        + apply NEL. unfold q_entries. apply in_flat_map. exists b'. exact (conj Hb' He').
        + exact (RME b' e' Hb' He').
      - intros b' Hb'. destruct (RMO b' Hb') as [LB SHBx]. pose proof (more_in A k _ more W L' b' Hb') as Hb2.
        destruct (lbatch_xfer A v m3 [] c k reg' cache' AR Wn WNH SHP SHPW CVe R'E MU NN (ba_idx b') (ba_entries b') 0%nat (batch_bytes b')
                    (batch_carved A v [] AR b' Hb2) (NEB b' (or_intror Hb')) (proj2 (batch_known A v [] AR b' Hb2)) LB) as [LB' SHB'].
        split; [exact LB'| exact (SHB' SHBx)].
      - destruct cur; [destruct Hcur| exact I]. }
      (* [comment removed for export] *)
      assert (AMD1 : amd_frame md md1) by exact (wamd_sbm md md1 SB1 HLT).
      (first [ pose proof ((cr_model A md md1 fe len W LED1 HH1 HI1 COV1 TOP1 RANGE AMD1 md3 SB3)) as dR_38; dand5 dR_38 as LED3 COV3 TOP3 AMD3 HH3 | destruct (cr_model A md md1 fe len W LED1 HH1 HI1 COV1 TOP1 RANGE AMD1 md3 SB3) as (LED3 & COV3 & TOP3 & AMD3 & HH3) ]).
      assert (MFH : forall z, 0 <= z < 2^64 -> hidc (pa_hull A') (wz z) = true -> Mf (wz z) = m (wz z)).
      { intros z Hz V1. unfold Mf, munrestrict. rewrite V1, ZSPEC. unfold in_range. rewrite unsigned_lit by exact Hz.
        destruct (Z_lt_le_dec z fe) as [Lo|Hi0]; [| destruct (Z_lt_le_dec z (fe + len)) as [Lo2|Hi2]].
        - replace ((fe <=? z) && (z <? fe + len)) with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; exact Lo).
          unfold M1, munrestrict. rewrite (APopG5.hidc_grow_le (pa_hull A) (pa_hull A') HLE (wz z) V1). reflexivity.
        - exfalso. rewrite (VISFA z (conj Hi0 Lo2)) in V1. discriminate.
        - replace ((fe <=? z) && (z <? fe + len)) with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; exact Hi2).
          unfold M1, munrestrict. rewrite (APopG5.hidc_grow_le (pa_hull A) (pa_hull A') HLE (wz z) V1). reflexivity. }
      assert (MFV : forall z, hidc (pa_hull A') (wz z) = false -> Mf (wz z) = m3 (wz z)) by (intros z V1; unfold Mf, munrestrict; rewrite V1; reflexivity).
      assert (D2 : (mfa + len) / 8 = mfa / 8 + len / 8).
      { pose proof (Z_div_mod_eq_full mfa 8) as X0. assert (M8 : mfa mod 8 = 0) by (clear -RGF4; unfold kFreeArrayMapSize in *; lia). rewrite M8 in X0.
        replace (mfa + len) with (mfa / 8 * 8 + len) by (clear -X0; lia). rewrite Z.div_add_l by (clear; lia). reflexivity. }
      assert (NEWHS : forall z, sfe <= z < sfe + len / 8 -> heap_shadow A' z).
      { intros z Hz. unfold heap_shadow, heap_shadow_, A', recA'. cbn [a_pl a_reg a_sec]. right; left. exists c. split; [exact Gcr|]. cbv zeta.
        rewrite (proj2 RCX). fold mfa. unfold a_sb. cbn [a_pl]. fold (a_sb A). rewrite D2. rewrite SHFA in Hz.
        assert (0 <= mfa / 8) by (apply Z.div_pos; [clear -RGF3; lia| clear; lia]). clear -Hz H. lia. }
      assert (GHV : forall z, ghost_hs_ (a_pl A) z -> 0 <= z < 2^64 /\ 0x60a000 <= z /\ ~ (fe <= z < fe + len)).
      { intros z [SMz _]. unfold in_shadow_maps in SMz. clear -SMz FEB. kung_all. lia. }
      assert (VOLD : forall z, 0 <= z < 2^64 -> hidc (pa_hull A') (wz z) = false -> ~ (fe <= z < fe + len) -> ~ (sfe <= z < sfe + len / 8) -> hidc (pa_hull A) (wz z) = false).
      { intros z Hz V1 N1 N2. destruct (hidc (pa_hull A) (wz z)) eqn:V0; [| reflexivity]. exfalso. unfold hidc in V0, V1. apply negb_true_iff in V0. apply negb_false_iff in V1.
        rewrite unsigned_lit in V0, V1 by exact Hz. destruct (NEWH z V1 V0) as [X0|X0]; [exact (N1 X0)| exact (N2 X0)]. }
      assert (HID' : hidden_repr (a_pl A') (a_reg A') (a_sec A') Mf).
      { apply (gw_hidden A c reg' cache' more len (proj1 AR) LEN0 RGO RCX m Mf HID).
        - intros z Gz Pz. (first [ pose proof ((GHV z Gz)) as dR_39; dand3 dR_39 as Z64 ZI NFE | destruct (GHV z Gz) as (Z64 & ZI & NFE) ]). destruct (hidc (pa_hull A') (wz z)) eqn:V1; [rewrite (MFH z Z64 V1); exact Pz|].
          rewrite (MFV z V1). destruct (classic (sfe <= z < sfe + len / 8)) as [INS|NS].
          + apply (wmono_NNR _ _ z WM2); [right; exact ZI| exact Z64|]. replace z with (sfe + (z - sfe)) by (clear; lia). apply MS2. clear -INS. lia.
          + apply NN; [clear -Z64; lia| right; exact ZI| clear -Z64; lia|]. unfold v, aview_of, mrestrict. rewrite (VOLD z Z64 V1 NFE NS). exact Pz.
        - intros z Gz NHS. (first [ pose proof ((GHV z Gz)) as dR_40; dand3 dR_40 as Z64 ZI NFE | destruct (GHV z Gz) as (Z64 & ZI & NFE) ]). destruct (hidc (pa_hull A') (wz z)) eqn:V1; [exact (MFH z Z64 V1)|].
          rewrite (MFV z V1). assert (NS : ~ (sfe <= z < sfe + len / 8)) by (intros INS; exact (NHS (NEWHS z INS))).
          destruct Gz as [SMz NVz].
          rewrite (AG_shadow_maps A v m3 [] c k reg' AR Wn WNH SHP SHPW CVe R'E MU z SMz).
          + unfold v, aview_of, mrestrict. rewrite (VOLD z Z64 V1 NFE NS). reflexivity.
          + intros [].
          + rewrite RGC, reg_return_mapped_fa. change (free_array_of (a_sb A) c) with fac_. change (rg_mapped_fa (a_reg A c)) with mfa. rewrite <- FEE. change (sh fe) with sfe. change (nm - mfa) with len. exact NS.
        - intros z Hz NVz Pz. assert (Z64 : 0 <= z < 2^64 /\ 0x60a000 <= z /\ ~ (fe <= z < fe + len) /\ ~ (sfe <= z < sfe + len / 8)) by (clear -Hz FEB SHB; kung_all; lia).
          (first [ dand4 Z64 as Z64 ZI NFE NS | destruct Z64 as (Z64 & ZI & NFE & NS) ]). destruct (hidc (pa_hull A') (wz z)) eqn:V1; [rewrite (MFH z Z64 V1); exact Pz|].
          rewrite (MFV z V1). apply NN; [clear -Z64; lia| right; exact ZI| clear -Z64; lia|]. unfold v, aview_of, mrestrict. rewrite (VOLD z Z64 V1 NFE NS). exact Pz. }
      assert (RIM : forall cur, match cur with None => True | _ => False end -> a_qlimbo A' = limbo_of cur more -> RINV A' Mf md3 T cur more).
      { intros cur Hcur Hl. constructor.
        - exact W'.
        - exact Hl.
        - rewrite VIEW. exact (RCM cur Hcur).
        - exact HID'.
        - exact EXTRA.
        - exact (gw_aledger A c reg' len Gcr RGO RCX md3 LED3 (lazy_free_sbm _ _ _ _ SB3 LZ2)).   (* [comment removed for export] *)
        - exact HI3.
        - exact HH3.
        - exact COV3.
        - exact TOP3. }
      (* [comment removed for export] *)
      assert (PF' : put_frame (p_thr (a_pl A)) m3).
      { unfold put_frameG in *. eapply rw_cells_transport; [exact PF| exact MUNall| exact WMall|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
      assert (RF' : rec_frame (p_thr (a_pl A)) m3).
      { unfold rec_frameG in *. eapply rw_cells_transport; [exact RF| exact MUNall| exact WMall|]. apply DISJ; [cbn; clear; lia|]. right; right; right. cbn [cells_size csize Nat.add length]. clear -LOW. lia. }
      assert (SMT : mapped m3 T (uspd - T)).
      { intros q Hq. pose proof TC' as TM'. unfold tmp_hdr in TM'.
        destruct (Z.lt_ge_cases (T + q) (T + 32)) as [C3|C3].
        { pose proof (rw_mapped_hi m3 _ _ TM' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
          exact (M q ltac:(clear -Hq C3; lia)). }
        destruct (Z.lt_ge_cases (T + q) (T + 80)) as [C4|C4].
        { pose proof (rw_mapped_hi m3 _ _ RF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
          specialize (M (T + q - (T + 32)) ltac:(clear -C3 C4; lia)). replace (T + 32 + (T + q - (T + 32))) with (T + q) in M by (clear; lia). exact M. }
        pose proof (rw_mapped_hi m3 _ _ PF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add length] in M.
        specialize (M (T + q - (uspd + -80)) ltac:(clear -C4 Hq; lia)). replace (uspd + -80 + (T + q - (uspd + -80))) with (T + q) in M by (clear; lia). exact M. }
      assert (SM' : mapped m3 lo (uspd - lo)).
      { intros q Hq. destruct (Z.lt_ge_cases (lo + q) T) as [C1|C1]; [| specialize (SMT (lo + q - T) ltac:(clear -C1 Hq; lia)); replace (T + (lo + q - T)) with (lo + q) in SMT by (clear; lia); exact SMT].
        destruct CASE as [(_ & _ & DF' & STK')|(_ & _ & STK')].
        - destruct (Z.lt_ge_cases (lo + q) dsp) as [C0|C0].
          { exact (stk_mapped_pa m3 lo dsp lo (dsp - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C0; lia)). }
          pose proof (rw_mapped_hi m3 _ _ DF' ltac:(clear -CEIL LOW CE; lia) ltac:(cbn; clear -CEIL LOW CE SPR; lia)) as M. cbn [cells_size csize Nat.add dorec_frG dorec_frame length] in M.
          specialize (M (lo + q - dsp) ltac:(clear -C0 C1; lia)). replace (dsp + (lo + q - dsp)) with (lo + q) in M by (clear; lia). exact M.
        - exact (stk_mapped_pa m3 lo (dsp + 112) lo (dsp + 112 - lo) STK' CEIL ltac:(clear; lia) ltac:(clear; lia) q ltac:(clear -Hq C1; lia)). }
      (* [comment removed for export] *)
      assert (DEADB : forall dlo dhi, In (dlo, dhi) (a_deadsh A) -> dhi <= kHighMemBeg).
      { intros dlo dhi Hd. (first [ pose proof ((wrE A W)) as dR_42; dand3 dR_42 as _ DF0 _ | destruct (wrE A W) as (_ & DF0 & _) ]). pose proof (proj1 (Forall_forall _ _) DF0 _ Hd) as (D1 & _). cbn [fst snd] in D1. clear -D1. kung_all. unfold kShadowGapBeg in *. lia. }
      assert (NLF : forall a, fac_ <= a < fac_ + kFreeArraySize -> ~ in_live_user A a /\ ~ in_live_frame A a).
      { intros a Ha. split.
        - intros LU. exact (proj2 (live_user_not_foot A v [] c k reg' AR CVe R'E a LU) Ha).
        - intros LF. pose proof (live_frame_zoneT A a (proj1 AR) LF) as Z1. (first [ pose proof ((bm_nth_fixed A)) as dR_43; dand8 dR_43 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
          pose proof (bm_sepT A 6 0 _ _ _ _ (proj1 AR) E6 E0 ltac:(lia)) as D.
          assert (INSP : a_sb A <= a < a_sb A + kSpaceSize + 4096) by (rewrite FAB in Ha; unfold region_beg in Ha; clear -Ha Gcr; kung_all; lia).
          pose proof (primary_in_b6T A a (proj1 AR) INSP) as XB6.
          unfold a_fs, a_b6 in *. clear -Z1 D XB6. unfold kFakeStackBytes, kFakeFramesOffset in *. lia. }
      assert (RS : rstep (pa_owned A) (pa_owned A') lo uspd v m3).
      { unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
        - intros a Ha NO NO' NW. apply MU; [exact Ha|]. intros Fa.
          destruct (foot_owned A v [] c k reg' AR Wn SHP SHPW CVe NE_live R'E a Fa) as [X|[X|[X|X]]].
          + apply NW. subst Wn. cbv beta in X. clear -X LOW CEIL. lia.
          + exact (NO X).
          + apply NO'. rewrite RGC, reg_return_mapped_fa in X. change (free_array_of (a_sb A) c) with fac_ in X. change (rg_mapped_fa (a_reg A c)) with mfa in X.
            destruct (NLF a ltac:(clear -X RGF3 NM4; unfold kFreeArraySize; lia)) as [NU NF].
            apply (gw_fa_owned A c reg' cache' more len Gcr RCX a); [| exact NU| exact NF]. rewrite <- FAB. fold mfa. unfold len. clear -X RGF3. lia.
          + apply NO'. rewrite RGC, reg_return_mapped_fa in X. change (free_array_of (a_sb A) c) with fac_ in X. change (rg_mapped_fa (a_reg A c)) with mfa in X.
            apply (gw_fsh_owned A c reg' cache' more len (proj1 AR) Gcr LEN0 DMF RCX a). rewrite <- FAB. fold mfa. exact X.
        - intros a Ha NI Hv. right. apply NN; [clear -Ha; lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| clear -Ha; lia| exact Hv].
        - exact SM'.
        - intros a Ha O'. destruct (gw_owned_new A c reg' cache' more len (proj1 AR) Gcr RGO RCX ltac:(fold mfa; unfold len, kFreeArraySize; clear -NM4 RGF3; lia) a O') as [O|NEWa]; [left; exact O| right].
          rewrite FAE2 in NEWa. split.
          + unfold v, aview_of, mrestrict. replace (hidc (pa_hull A) (wz a)) with true; [reflexivity|]. symmetry. unfold hidc. apply negb_true_iff. rewrite unsigned_lit by exact Ha.
            apply (prim_unmapped_hidden A (proj1 AR) EXTRA DEADB c a Gcr). right. rewrite FAE2. unfold region_beg, kRegionSize. change (a_sb A) with sb. clear -NEWa FEL. unfold kFreeArrayOffset in *. lia.
          + unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear -NEWa FEB CE. kung_all. lia.
        - intros a Ha O NO'. exfalso. apply NO'. exact (gw_owned_mono A c reg' cache' more len (proj1 AR) LEN0 RGO RCX a O). }
      assert (NZ : a_reg A c <> region_zero).
      { intros E. pose proof Gk as X. unfold carved_count, carved_count_ in X. rewrite E in X. cbn in X. clear -X.
        pose proof (Z.div_0_l (class_size c)). rewrite Zdiv_0_l in X. lia. }
      pose proof (RHIST_step A0 v0 md0 p n0 uspd lo hi A v md A' m3 md3 HIST (WFT_of_WFR A W) (WFT_of_WFR A' W') CEIL ltac:(clear -LOW; lia) SPHI HI47 VB
                    eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                    (fun c0 NE V0 => gw_virgin A c reg' cache' more RGO c0 NZ CAO V0)
                    AMD3 RS) as HIST'.
      (* [comment removed for export] *)
      destruct CASE as [(NE & E & DF' & STK')|(EQ & E & STK')]; rewrite MSE in E; injection E as Er Ep; subst regs pcw.
      + assert (CU' : CUR A' Mf md3 None more scr).
        { constructor; rewrite ?VIEW.
          - apply RIM; [exact I| reflexivity].
          - exact HIST'.
          - exact MI'.
          - exact STK'.
          - exact PF'.
          - exact RF'.
          - exact DF'.
          - exact I.
          - exact QB'. }
        specialize (KM A' Mf md3 a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y NE CU' eq_refl).
        unfold head_cfgG in KM. fold tn in KM. exact KM.
      + subst more.
        assert (XCU' : XCUR A' Mf md3).
        { constructor; rewrite ?VIEW.
          - apply RIM; [exact I| reflexivity].
          - exact HIST'.
          - exact MI'.
          - replace T with (dsp + 112) by (clear; lia). exact STK'.
          - exact PF'.
          - exact RF'. }
        specialize (K0 A' Mf md3 a1y a2y a3y a4y a5y a6y a7y t0y t1y t2y t3y t4y t5y t6y eq_refl XCU' eq_refl).
        unfold exit_cfgG in K0. cbn [a_pl] in K0. fold thr in K0. replace (dsp + 112) with T by (clear; lia). exact K0.
  Qed.
End RIter.

(* [comment removed for export] *)
Theorem step_bdm_ok {Clg : Ceiling} : step_bdm_stmt.
Proof.
  unfold step_bdm_stmt. intros rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 A1 m1 md1 b0 more scr
         ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CEIL LOW SPHI HI47 SPA VB CU FULL NOROOM KH KX.
  apply (step_batch_drainmap rac spd gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A0 m0 md0 p n0 stkobj lo hi TS xs2 xs5 CEIL LOW SPHI HI47 SPA VB
           A1 m1 md1 b0 more scr ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' CU FULL NOROOM).
  - intros A' m' md' a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x NE CU' PL.
    exact (KH A' m' md' _ a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x _ s6' s7' s8' s9' NE CU' PL).
  - intros A' m' md' a1x a2x a3x a4x a5x a6x a7x t0x t1x t2x t3x t4x t5x t6x EQ XCU' PL.
    exact (KX A' m' md' t0x t1x t2x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x XCU' PL).
Qed.
