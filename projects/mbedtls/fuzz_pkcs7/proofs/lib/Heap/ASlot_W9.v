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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_W9 () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.MallocRep.CTX"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.MallocRep.meta_slot"; "OSSVerify.KrLib.Heap.Malloc.conc"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.ASlot_W0.ta_rel"; "gmf"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.MallocFacts_AS.mw_ok"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.m_freeable"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.lowbit"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "OSSVerify.KrLib.Heap.Malloc.upd_meta"; "OSSVerify.KrLib.Heap.Malloc.m_set_avail"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Heap.MallocTree.pres_except"; "ta_fp"; "OSSVerify.KrLib.Heap.MallocTree.implT"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"].


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_W9 ()) "(0.(1.(2.O3.O1.)(3.O1.O2.))(0.(1.(2.$4.O1.)(3.O1.(5.$4.+3:0.)))(0.(6.$7.Lq,$7.(1.(8.O4.R1.)(1.(2.(9.O4.R1.)O1.)(3.O1.(5.(9.O4.R1.)+28.)))))(6.$7.Lb,$7.(6.$:.Lgh,$:.(1.(;.(<.$:.)(=.$7.$:.(>.$7.(?.$10.$11.$12.$13.)(14.$10.$11.$15.$12.$13.$16.)$:.)(17.$7.(?.$10.$11.$12.$13.)(14.$10.$11.$15.$12.$13.$16.)$:.)R2.(18.O4.))(19.$:.R1.))(1.(2.(9.O4.R2.)O1.)(3.O1.(5.(9.O4.R2.)+9.)))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
  gmf_slot : meta_slot st g;
  gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  gmf_mw : mw_ok (get_meta_rec st g);
  gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
  gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
  gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
             /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
             /\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
             /\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
  gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.

(* [comment removed for export] *)
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmf_geom st st1 sc g : ltac2:(CDefT.buildp (gd_tbl_ASlot_W9 ()) "P,(1:.O2.O4.O3.)P,(1;.O4.O2.O1.)(1.(8.O3.O1.)(1.(1.(2.=(1<.(1=.O3.O1.)))(3.(1<.(1=.O3.O1.))(1>.+2.+20.)))(1.(1.(2.=(1?.(1=.O3.O1.)))(3.(1?.(1=.O3.O1.))(1>.+2.+20.)))(1.(20.(1=.O3.O1.))(1.(;.$21.(22.(1=.O3.O1.))(22.(1=.O4.O1.)))(1.(;.$12.(23.(1=.O3.O1.))(23.(1=.O4.O1.)))(1.(;.$12.(24.(1=.O3.O1.))(24.(1=.O4.O1.)))(1.(;.$12.(25.(1=.O3.O1.))(25.(1=.O4.O1.)))(;.$12.(9.O3.O1.)(9.O4.O1.))))))))))")
(* [comment removed for export] *).
Proof.
  intros TR GM. destruct (tr_geom _ _ _ TR g) as (E1 & E2 & E3 & E4 & E5).
  destruct (tr_mrange _ _ _ TR g (gmf_avail _ _ _ GM) (gmf_freed _ _ _ GM)) as [RA RF].
  pose proof (gmf_mw _ _ _ GM) as MW. unfold mw_ok in *. rewrite E2, E3, E4, E5.
  split; [eapply meta_slot_same_areas; [apply (tr_areas _ _ _ TR)| apply (gmf_slot _ _ _ GM)]|].
  repeat (split; [first [assumption| lia| reflexivity]|]).
  unfold conc, get_region. rewrite (tr_regions _ _ _ TR). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma disjoint_high (C : Z) W A n : (forall lo hi, In (lo, hi) W -> hi <= C) -> C <= A -> disjoint_from W A n.
Proof.
  induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
  split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.


(* [comment removed for export] *)
Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof. unfold decay_bounces. destruct (_ && _); [right; eexists; reflexivity| left; reflexivity]. Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof. destruct (decay_cases c st) as [-> | [v ->]]; reflexivity. Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : s_ceil st <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

(* [comment removed for export] *)
Hypothesis HK1 : ltac2:(CDefT.buildp (gd_tbl_ASlot_W9 ()) "PstX,$26.Pg3,$7.Pmsk,$12.Pk,$12.Pm',P,(27.&40.)(<.(27.&8.))Pt1',(27.&40.)Pt3',(27.&40.)Pt4',(27.&40.)Pa2',(27.&40.)Pa3',(27.&40.)Pa4',(27.&40.)Pa5',(27.&40.)Pa6',(27.&40.)Pa7',(27.&40.)P,(1:.Vsc,Vst,R>.)P,(;.$21.(28.R?.Vsc,)(19.$7.R>.))P,(1;.Vst,Vsc,R?.)P,(;.$12.R?.(1<.(1=.R11.R10.)))P,(1.(3.=R10.)(3.R10.(1>.+2.+20.)))P,(;.$12.(29.R11.)(1>.+2.R10.))P,(1.(2.=R11.)(3.R11.+20.))P,(2:.(2;.R14.(2<.(2=.R13.(29.R13.)))R15.)R11.)P,(2>.$2?.R12.)P,(30.$2?.R13.Vlo,Vspv,)P,(31.(32.Vst,Vlo,Vspv,)Vm,R14.)(33.VR,Vo,A2.VK,(2;.R18.(2<.(2=.R17.(29.R17.)))R19.)(29.R17.)Vs,VQ,(34.(35.Vra,Vsp,Vgp,Vtp,Vt0,R14.Vt2,Vs0,Vs1,(36.R16.)Va1,R11.R10.R?.R>.R=.R<.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R13.R12.Vt5,Vt6,)VF,(37.Vra,)Vfc,(38.(27.&40.))R15.(39.$2?.)))")
(* [comment removed for export] *).


End PHASE.
