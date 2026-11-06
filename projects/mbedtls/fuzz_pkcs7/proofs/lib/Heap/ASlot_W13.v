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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A3 ASlot_W1 ASlot_W10 ASlot_W12.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_W13 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.region"; "stdpp.base.lookup"; "Corelib.Numbers.BinNums.N"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc.Known"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.Heap.Malloc.wr8"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.ZArith.BinInt.Z.shiftl"; "OSSVerify.KrLib.Heap.Malloc.wr16"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.enframe_at"; "ENF.enf0_st"].


Section ENF.
Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : mrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

#[using="SO"] Lemma enf_facts : ltac2:(CDefT.buildp (gd_tbl_ASlot_W13 ()) "(0.(1.$2.(3.Vmr,)(4.$5.Vb,))(0.(1.(6.$7.)(8.$9.$7.(:.$9.$;.$<.$7.)(=.$9.$;.$<.$7.)(>.$9.$?.Vb,)(10.Vst,))(4.$7.Vr,))(0.(1.$11.(12.Vr,)$13.)(0.(14.=(15.$9.$?.Vb,))(0.(1.$?.(16.(15.$9.$?.Vb,)+10.)=)(0.(0.(14.=Vidx,)(14.Vidx,(17.Vmr,)))(0.(18.(17.Vmr,)+20.)(0.(14.(19.(19.(15.$9.$?.Vb,)+10.)(1:.Vstride,(19.(17.Vmr,)+1.)))(1;.(1<.Vr,)))(0.(14.+10.Vstride,)(0.(1.$?.(16.Vstride,+10.)=)(0.Pb',(1=.$9.$?.)Pgh,$1>.P,(1.(6.$1>.)(8.(1=.$9.$?.)$1>.(:.$5.(1?.$9.$;.$?.$20.)(21.$9.$;.$<.$?.$20.$22.)$1>.)(=.$5.(1?.$9.$;.$?.$20.)(21.$9.$;.$<.$?.$20.$22.)$1>.)R2.(23.Vst,))(4.$1>.R1.))P,(1.$9.(>.$9.$?.R3.)(>.$9.$?.Vb,))(24.(14.(19.(15.$9.$?.R4.)+9.)(25.(19.(19.(15.$9.$?.Vb,)+10.)(1:.Vstride,Vidx,))+4.))(14.(25.(19.(19.(19.(15.$9.$?.Vb,)+10.)(1:.Vstride,Vidx,))Vstride,)+4.)(15.$9.$?.R4.)))(0.(1.$26.(27.(28.Vst,(>.$9.$?.Vb,))(25.(19.(19.(15.$9.$?.Vb,)+10.)(1:.Vstride,Vidx,))+4.))(29.=))Poff,$?.P,(14.=R1.)P,(14.(19.(19.(1:.+10.R2.)VN,)+4.)Vstride,)(18.(2:.(19.(1:.Vstride,Vidx,)(1:.+10.R3.))+10.)+10000.)))))))))))))")
(* [comment removed for export] *).
Proof.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
  repeat (split; [assumption|]). exact Q16.
Qed.


(* [comment removed for export] *)
Definition enf0_st : mstate := ltac2:(CDefT.buildp (gd_tbl_ASlot_W13 ()) "(2;.(2<.$9.$?.(>.$9.$?.Vb,)(19.(19.(15.$9.$?.Vb,)(19.+10.(1:.Vstride,Vidx,)))-3.))(19.(2=.Vidx,+1?.)(2>.=+5.))(2;.(2<.$9.$?.(>.$9.$?.Vb,)(19.(19.(15.$9.$?.Vb,)(19.+10.(1:.Vstride,Vidx,)))-3.))Vidx,(2?.(2<.$9.$?.(>.$9.$?.Vb,)(19.(19.(15.$9.$?.Vb,)(19.+10.(1:.Vstride,Vidx,)))-2.))(2:.(25.(19.(15.$9.$?.Vb,)(19.+10.(1:.Vstride,Vidx,)))(19.(15.$9.$?.Vb,)+10.))+10.)Vst,)))")
(* [comment removed for export] *).

#[using="r B P STR SO"] Lemma enf0_st_eq : ltac2:(CDefT.buildp (gd_tbl_ASlot_W13 ()) "(0.(1.$30.(>.$30.$5.(31.Vst,Vg,Vidx,VN,=))$32.)(1.$5.(15.$30.$5.(31.Vst,Vg,Vidx,VN,=))(2<.$9.$?.(>.$9.$?.Vb,)(19.(15.$9.$?.Vb,)(19.+10.(1:.Vstride,Vidx,))))))")
(* [comment removed for export] *).
Proof.
  pose proof enf_facts as (Hmem & _).
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
  change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
  unfold set_size. cbn [fst snd].
  replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
  cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.

(* [comment removed for export] *)
#[using="st g b idx j mr stride B P N"] Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
  (intros dd_H; ddestruct dd_H as (LI & FB & SC & ML)). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
  rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.


(* [comment removed for export] *)
Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).

End ENF.
