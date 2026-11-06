(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase MemImageType RiscvSemantics StackLayout State Run.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec StepTac StreamSim AllocSim Footprint.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_StoreOk () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "mem_grows"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.Run.zeros_cover"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_zeros"; "OSSVerify.KrLib.ABoot.AllocSim.zmem"; "store_grant_ok"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.find_segment"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_writable"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.segment_byte_at"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_bytes"; "Stdlib.ZArith.BinInt.Z.to_N"; "Stdlib.ZArith.BinInt.Z.of_N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.seg_base"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.StreamSim.wseg_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_aux"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_map"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_writable_byte"; "OSSVerify.KrLib.ABoot.Footprint.covers"; "OSSVerify.KrLib.ABoot.Footprint.heap_rg"].


(* [comment removed for export] *)
Definition mem_grows (m m' : word -> option byte) : Prop :=
  forall x, m x <> None -> m' x <> None.

Lemma mem_grows_refl : forall m, mem_grows m m.
Proof. intros m x H. exact H. Qed.

Lemma mem_grows_trans : forall m1 m2 m3,
  mem_grows m1 m2 -> mem_grows m2 m3 -> mem_grows m1 m3.
Proof. intros m1 m2 m3 H12 H23 x Hx. apply H23, H12, Hx. Qed.

(* [comment removed for export] *)
Lemma wview_grows : forall segs m m' x,
  mem_grows m m' ->
  wview segs m x <> None -> wview segs m' x <> None.
Proof.
  intros segs m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:Hm'; [discriminate|].
  destruct (m x) as [b|] eqn:Hm.
  - exfalso. apply (Hg x); [rewrite Hm; discriminate|exact Hm'].
  - exact Hx.
Qed.

Lemma store_ok_mono : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pn,$2.Pm,P,(3.&40.)(4.(3.&8.))Pm',P,(3.&40.)(4.(3.&8.))Pa,(3.&40.)P,(5.R3.R2.)P,(6.$7.(8.R6.R4.R2.R5.)$9.)(6.$7.(8.R7.R4.R3.R6.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs n; induction n as [|n IH]; intros m m' a Hg H; [reflexivity|].
  cbn [store_ok] in *.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  destruct (wview segs m' a) as [b'|] eqn:Hv'.
  - apply (IH m m'); assumption.
  - exfalso. apply (wview_grows segs m m' a Hg); [rewrite Hv; discriminate|exact Hv'].
Qed.

(* [comment removed for export] *)

Lemma wbytes_grows : forall bs m a, mem_grows m (wbytes m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [wbytes]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_zeros_grows : forall zs m, mem_grows m (apply_zeros m zs).
Proof.
  intros zs m x Hx. unfold apply_zeros.
  destruct zs as [|z zs']; [exact Hx|].
  destruct (zeros_cover (z :: zs') x); [discriminate|exact Hx].
Qed.

Lemma zmem_grows : forall m b l, mem_grows m (zmem m b l).
Proof.
  intros m b l x Hx. unfold zmem.
  destruct (Z.leb _ _ && Z.ltb _ _)%bool; [discriminate|exact Hx].
Qed.

Lemma write_to_mem_grows : forall bs m a, mem_grows m (write_to_mem m a bs).
Proof.
  induction bs as [|b rest IH]; intros m a x Hx; [exact Hx|].
  cbn [write_to_mem]. apply IH.
  destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.

Lemma apply_writes_grows : forall ws m, mem_grows m (apply_writes m ws).
Proof.
  induction ws as [|w ws' IH]; intros m x Hx.
  - exact Hx.
  - destruct w as [a bs]. cbn [apply_writes].
    apply IH. apply write_to_mem_grows. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_all : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pn,$2.Pm,P,(3.&40.)(4.(3.&8.))Pa,(3.&40.)P,(:.(;.(<.&40.R1.)(=.R3.))(>.+2.+40.))P,Px,(3.&40.)P,(?.(:.(<.&40.R3.)(<.&40.R1.))(10.(<.&40.R1.)(;.(<.&40.R3.)(=.R5.))))(11.(6.(4.(3.&8.))(12.R7.R5.R2.)(13.(3.&8.))))(6.$7.(8.R6.R4.R3.R5.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs n; induction n as [|n IH]; intros m a Hnw Hall; [reflexivity|].
  cbn [store_ok].
  destruct (wview segs m a) as [b|] eqn:Hv.
  2: { exfalso. refine (Hall a _ Hv). rewrite Nat2Z.inj_succ. lia. }
  (* [comment removed for export] *)
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1)
    by (apply u_add1; rewrite Nat2Z.inj_succ in Hnw; lia).
  apply IH.
  - rewrite Hu1. lia.
  - intros x Hx. rewrite Hu1 in Hx. apply Hall.
    rewrite Nat2Z.inj_succ. lia.
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_window_defined : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Pph,$14.Psp,(3.&40.)Pargv,(0.(0.(3.&8.)))Penvp,(0.(0.(3.&8.)))Px,(3.&40.)Puid,(3.&40.)Phw,(3.&40.)Prnd,$15.P,(:.(16.(<.&40.R7.)$17.)(<.&40.R4.))P,(10.(<.&40.R5.)(<.&40.R8.))(11.(6.(4.(3.&8.))(18.R:.R9.R8.R7.R5.R4.R3.R6.)(13.(3.&8.))))")
(* [comment removed for export] *).
Proof.
  intros ph sp argv envp x uid hw rnd Hlo Hhi. unfold wrap_mem.
  destruct (stack_to_mem sp (entry_stack_image ph sp argv envp uid hw rnd) x) as [b|];
    [discriminate|].
  rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.ltb_lt _ _) Hhi).
  cbn. discriminate.
Qed.

Lemma store_ok_wrap_window : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pph,$14.Psp,(3.&40.)Pargv,(0.(0.(3.&8.)))Penvp,(0.(0.(3.&8.)))Pa,(3.&40.)Pn,$2.Puid,(3.&40.)Phw,(3.&40.)Prnd,$15.P,(:.(16.(<.&40.R8.)$17.)(<.&40.R5.))P,(:.(;.(<.&40.R6.)(=.R5.))(<.&40.R9.))(6.$7.(8.R<.(18.R;.R:.R9.R8.R5.R4.R3.)R7.R6.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs ph sp argv envp a n uid hw rnd Hlo Hhi.
  assert (Hsp : bv_unsigned sp < 2 ^ 64) by apply bv_unsigned_in_range.
  apply store_ok_of_all; [lia|].
  intros x Hx. unfold wview.
  destruct (wrap_mem ph sp argv envp uid hw rnd x) as [b|] eqn:Hw; [discriminate|].
  exfalso. revert Hw. apply wrap_mem_window_defined; lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zeros_hit : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pzs,(0.(19.(3.&40.)(3.&40.)))Pa,(3.&40.)Pn,$2.P,(11.(6.(0.(19.(3.&40.)(3.&40.)))R3.(1:.(19.(3.&40.)(3.&40.)))))P,(:.(;.(<.&40.R3.)(=.R2.))(>.+2.+40.))P,Px,(3.&40.)P,(?.(:.(<.&40.R5.)(<.&40.R1.))(10.(<.&40.R1.)(;.(<.&40.R5.)(=.R4.))))(6.$7.(1;.R7.R2.)$9.)(6.$7.(8.R8.(1<.R7.R6.)R5.R4.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs m zs a n Hne Hnw Hcov.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, apply_zeros.
  destruct zs as [|z zs']; [contradiction|].
  rewrite (Hcov x Hx). discriminate.
Qed.

(* [comment removed for export] *)
Lemma store_ok_zmem : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pb,(3.&40.)Pl,(3.&40.)Pa,(3.&40.)Pn,$2.P,(:.(;.(<.&40.R2.)(=.R1.))(>.+2.+40.))P,(:.(<.&40.R5.)(<.&40.R3.))P,(:.(;.(<.&40.R4.)(=.R3.))(;.(<.&40.R6.)(<.&40.R5.)))(6.$7.(8.R9.(1=.R8.R7.R6.)R5.R4.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs m b l a n Hnw Hlo Hhi.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview, zmem.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  cbn. discriminate.
Qed.

(* [comment removed for export] *)
Definition store_grant_ok (segs : list Segment) (m : word -> option byte)
                    (b l : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Pa,(3.&40.)Pn,$2.P,(:.(<.&40.O2.)(<.&40.R2.))P,(:.(;.(<.&40.R3.)(=.R2.))(;.(<.&40.O2.)(<.&40.O1.)))(6.$7.(8.O4.O3.R4.R3.)$9.)")
(* [comment removed for export] *).

Lemma store_grant_zmem : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pb,(3.&40.)Pl,(3.&40.)P,(:.(;.(<.&40.R2.)(<.&40.R1.))(>.+2.+40.))(1>.R5.(1=.R4.R3.R2.)R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros segs m b l Hnw a n Hlo Hhi. apply store_ok_zmem; lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_zmem_prefix : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pb,(3.&40.)Plogical,(3.&40.)Pphysical,(3.&40.)P,(:.(<.&40.R2.)(<.&40.R1.))P,(:.(;.(<.&40.R4.)(<.&40.R2.))(>.+2.+40.))(1>.R7.(1=.R6.R5.R3.)R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs m b logical physical Hle Hnw a n Hlo Hhi.
  apply store_ok_zmem; lia.
Qed.

Lemma store_grant_mono : forall segs m m' b l,
  mem_grows m m' -> store_grant_ok segs m b l -> store_grant_ok segs m' b l.
Proof.
  intros segs m m' b l Hg H a n Hlo Hhi.
  eapply store_ok_mono; [exact Hg|]. apply H; assumption.
Qed.

(* [comment removed for export] *)
Lemma store_ok_seg_writable : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pa,(3.&40.)Pn,$2.P,(:.(;.(<.&40.R2.)(=.R1.))(>.+2.+40.))P,Px,(3.&40.)P,(?.(:.(<.&40.R4.)(<.&40.R1.))(10.(<.&40.R1.)(;.(<.&40.R4.)(=.R3.))))(1?.$1.Lseg,$1.(?.(6.(4.$1.)(20.R8.(<.&40.R3.)+1.)(21.$1.R1.))(?.(6.$7.(22.R1.)$9.)(11.(6.(4.(3.&8.))(23.(24.R1.)(25.(16.(<.&40.R3.)(26.(27.R1.)))))(13.(3.&8.)))))))(6.$7.(8.R6.R5.R4.R3.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs m a n Hnw Hall.
  apply store_ok_of_all; [exact Hnw|].
  intros x Hx. unfold wview.
  destruct (m x) as [b|]; [discriminate|].
  destruct (Hall x Hx) as [seg [Hfind [Hw Hb]]].
  rewrite Hfind, Hw. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma store_ok_wseg : forall segs m a n,
  wseg_ok segs a n = true -> store_ok segs m a n = true.
Proof.
  intros segs m a n; revert a m; induction n as [|n IH]; intros a m H; [reflexivity|].
  cbn [wseg_ok] in H.
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
  apply andb_true_iff in H as [H Hrec].
  apply andb_true_iff in H as [Hwr Hbyte].
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
    [|discriminate].
  cbn [store_ok]. unfold wview at 1.
  destruct (m a) as [b0|]; [apply IH, Hrec|].
  rewrite Hseg, Hwr, Hb. apply IH, Hrec.
Qed.

(* [comment removed for export] *)
Lemma store_ok_all : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pn,$2.Pa,(3.&40.)P,(:.(;.(<.&40.R1.)(=.R2.))(>.+2.+40.))P,(6.$7.(8.R5.R4.R2.R3.)$9.)Px,(3.&40.)P,(?.(:.(<.&40.R4.)(<.&40.R1.))(10.(<.&40.R1.)(;.(<.&40.R4.)(=.R5.))))(11.(6.(4.(3.&8.))(12.R8.R7.R2.)(13.(3.&8.))))")
(* [comment removed for export] *).
Proof.
  intros segs m n; induction n as [|n IH]; intros a Hnw H x Hx;
    [cbn in Hx; lia|].
  cbn [store_ok] in H.
  destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
  rewrite Nat2Z.inj_succ in Hnw, Hx.
  destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
  { assert (x = a) by (apply bv_eq; exact Heq). subst x.
    rewrite Hv. discriminate. }
  (* [comment removed for export] *)
  assert (Hn : (1 <= Z.of_nat n)%Z) by lia.
  assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1) by (apply u_add1; lia).
  (* [comment removed for export] *)
  eapply IH; [ | exact H | ]; lia.
Qed.

Lemma store_ok_sub : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Plo,(3.&40.)Pa,(3.&40.)PN,$2.Pn,$2.P,(:.(;.(<.&40.R4.)(=.R2.))(>.+2.+40.))P,(6.$7.(8.R7.R6.R5.R3.)$9.)P,(:.(<.&40.R6.)(<.&40.R5.))P,(:.(;.(<.&40.R6.)(=.R4.))(;.(<.&40.R7.)(=.R5.)))(6.$7.(8.R:.R9.R7.R5.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs m lo a N n Hnw Hok Hl Hh.
  apply store_ok_of_all; [lia|].
  intros x Hx. apply (store_ok_all segs m N lo Hnw Hok). lia.
Qed.

(* [comment removed for export] *)
Lemma store_ok_window : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Plo,(3.&40.)Pa,(3.&40.)PN,$2.Pn,$2.Pbase,$28.Phi,$28.P,(6.$28.(<.&40.R6.)R2.)P,(6.$28.(;.R3.(=.R5.))R2.)P,(:.R3.(>.+2.+40.))P,(6.$7.(29.R;.R9.R7.)$9.)P,(:.R6.(<.&40.R9.))P,(:.(;.(<.&40.R:.)(=.R8.))R6.)(6.$7.(8.R>.R=.R;.R9.)$9.)")
(* [comment removed for export] *).
Proof.
  intros segs m lo a N n base hi Hbase Htop Hnw Hw Hl Hh.
  eapply store_ok_sub; [ | apply store_ok_wseg, Hw | | ]; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma store_ok_read_aux : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pm,P,(3.&40.)(4.(3.&8.))Pn,$2.Pa,(3.&40.)P,(6.$7.(8.R4.R3.R1.R2.)$9.)(1?.(0.(3.&8.))Lw,(0.(3.&8.))(6.(4.(0.(3.&8.)))(2:.(12.R6.R5.)R3.R4.)(21.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs m n; induction n as [|n IH]; intros a H.
  - exists []. reflexivity.
  - cbn [store_ok] in H. cbn [read_bytes_aux].
    destruct (wview segs m a) as [b|] eqn:Hv; [|discriminate].
    destruct (IH (a + 1)%bv H) as [w Hw]. rewrite Hw. exists (b :: w). reflexivity.
Qed.

Lemma store_ok_wbuf : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pms,$2;.Pbuf,(3.&40.)Pcnt,(3.&40.)P,(6.$7.(8.R4.(2<.R3.)R2.(2=.R1.))$9.)(1?.(0.(3.&8.))Lw,(0.(3.&8.))(6.(4.(0.(3.&8.)))(2>.(2?.R6.R5.)R4.R3.)(21.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms buf cnt H.
  rewrite read_bytes_map_eq. unfold ms_writable_byte.
  apply store_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
Lemma of_nat_word_to_nat : forall w : word,
  Z.of_nat (word_to_nat w) = bv_unsigned w.
Proof.
  intro w. unfold word_to_nat. pose proof (u64_range w). lia.
Qed.

(* [comment removed for export] *)
Lemma store_grant_wbuf : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pms,$2;.Pb,(3.&40.)Pl,(3.&40.)Pbuf,(3.&40.)Pcnt,(3.&40.)P,(1>.R6.(2<.R5.)R4.R3.)P,(:.(<.&40.R5.)(<.&40.R3.))P,(:.(;.(<.&40.R4.)(<.&40.R3.))(;.(<.&40.R6.)(<.&40.R5.)))(1?.(0.(3.&8.))Lw,(0.(3.&8.))(6.(4.(0.(3.&8.)))(2>.(2?.R:.R9.)R6.R5.)(21.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms b l buf cnt Hg Hlo Hhi.
  apply store_ok_wbuf, Hg; rewrite ?of_nat_word_to_nat; lia.
Qed.

(* [comment removed for export] *)
Lemma heap_rg_wbuf : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pms,$2;.Pb,(3.&40.)Pl,(3.&40.)Pbuf,(3.&40.)Pcnt,(3.&40.)Pcur,$28.P,(1>.R7.(2<.R6.)R5.R4.)P,(:.R2.(16.(;.(<.&40.R6.)(<.&40.R5.))(<.&40.R6.)))P,(30.(31.R7.R3.)R5.(2=.R4.))(1?.(0.(3.&8.))Lw,(0.(3.&8.))(6.(4.(0.(3.&8.)))(2>.(2?.R;.R:.)R7.R6.)(21.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms b l buf cnt cur Hg Hcur Hc.
  destruct Hc as [Hlo Hhi]. cbn [heap_rg rg_lo rg_hi] in Hlo, Hhi.
  rewrite of_nat_word_to_nat in Hhi.
  eapply store_grant_wbuf; [exact Hg | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma zmem_wbuf : ltac2:(CDefT.buildp (gd_tbl_StoreOk ()) "Psegs,(0.$1.)Pms,$2;.Pm,P,(3.&40.)(4.(3.&8.))Pb,(3.&40.)Pl,(3.&40.)Pbuf,(3.&40.)Pcnt,(3.&40.)P,(5.(1=.R5.R4.R3.)(2<.R6.))P,(:.(;.(<.&40.R5.)(<.&40.R4.))(>.+2.+40.))P,(:.(<.&40.R6.)(<.&40.R4.))P,(:.(;.(<.&40.R5.)(<.&40.R4.))(;.(<.&40.R7.)(<.&40.R6.)))(1?.(0.(3.&8.))Lw,(0.(3.&8.))(6.(4.(0.(3.&8.)))(2>.(2?.R<.R;.)R7.R6.)(21.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs ms m b l buf cnt Hgr Hnw Hlo Hhi.
  eapply store_grant_wbuf; [ | exact Hlo | exact Hhi ].
  eapply store_grant_mono; [exact Hgr|]. apply store_grant_zmem. exact Hnw.
Qed.

(* [comment removed for export] *)
Example drain_buffer_in_grant : forall segs ms m (b l buf cnt : word) a bs,
  ms_mem ms = wbytes (zmem m b l) a bs ->
  bv_unsigned b + bv_unsigned l <= 2 ^ 64 ->
  bv_unsigned b <= bv_unsigned buf ->
  bv_unsigned buf + bv_unsigned cnt <= bv_unsigned b + bv_unsigned l ->
  exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w.
Proof.
  intros segs ms m b l buf cnt a bs Hm Hnw Hlo Hhi.
  eapply zmem_wbuf;
    [ rewrite Hm; apply wbytes_grows | exact Hnw | exact Hlo | exact Hhi ].
Qed.

(* [comment removed for export] *)
Ltac store_ok_peel :=
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)
Ltac store_ok_base :=
  first
    [ apply store_ok_wrap_window; unfold stack_max_size; u_norm; lia
    | eapply store_ok_zeros_hit;
      [ discriminate | u_norm; lia | intros; u_norm; lia ]
    | apply store_ok_zmem; u_norm; lia ].

(* [comment removed for export] *)
Ltac solve_store_ok :=
  store_ok_peel;
  first [ store_ok_base
        | eapply store_ok_mono; [apply zmem_grows|];
          store_ok_peel; store_ok_base ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Create HintDb store_ok_db.

Ltac store_ok_grows := solve [ eauto with store_ok_db ].

Ltac solve_store_ok_inv :=
  first [ solve_store_ok
        | store_ok_peel;
          eapply store_ok_mono; [ store_ok_grows | ]; solve_store_ok ].

(* [comment removed for export] *)
Ltac solve_mem_grows :=
  repeat first
    [ solve [ eauto with store_ok_db ]
    | apply mem_grows_refl
    | eapply mem_grows_trans; [ | apply wbytes_grows ]
    | eapply mem_grows_trans; [ | apply zmem_grows ]
    | eapply mem_grows_trans; [ | apply write_to_mem_grows ]
    | eapply mem_grows_trans; [ | apply apply_zeros_grows ]
    | eapply mem_grows_trans; [ | apply apply_writes_grows ] ].
