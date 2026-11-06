(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux HeapIface.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_SInv () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.Frame.ivl"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.Lib.Frame.disjoint_from"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.and"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "si_fp"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "si_P"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.HeapIface.hl_written"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "OSSVerify.KrLib.Lib.HeapIface.hl_static"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.None"].


Record sinv (L : heap_layout) := mkSI {
  si_P : mem -> Prop;
  si_fp : list ivl;
  si_frame : forall m m' : mem, si_P m -> (forall a, 0 <= a < 2^64 -> ~ outside si_fp a -> m' (wa a) = m (wa a)) -> si_P m';
  si_init : forall m : mem, (forall a, 0 <= a < 2^64 -> ~ outside si_fp a -> m (wa a) = None) -> si_P m;
  si_data : forall a, ~ outside si_fp a -> hl_data_lo L <= a < hl_data_hi L /\ hl_written L a /\ ~ hl_static L a;
  si_wf : Forall (fun iv => fst iv < snd iv) si_fp
}.
Arguments si_P {L}. Arguments si_fp {L}. Arguments si_frame {L}. Arguments si_init {L}. Arguments si_data {L}. Arguments si_wf {L}.

Lemma outside_app : forall (W1 W2 : list ivl) a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[u v] W1 IH]; cbn; intros W2 a; [tauto|]. rewrite IH. tauto. Qed.
Lemma disjoint_from_app : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "PW1,(0.$1.)PW2,(0.$1.)Pa,$2.Pn,$2.(3.(4.(5.$1.R4.R3.)R2.R1.)(6.(4.R4.R2.R1.)(4.R3.R2.R1.)))")
(* [comment removed for export] *).
Proof. induction W1 as [|[u v] W1 IH]; cbn; intros W2 a n; [tauto|]. rewrite IH. tauto. Qed.

(* [comment removed for export] *)
Definition si_trivial (L : heap_layout) : sinv L.
Proof.
  refine (mkSI L (fun _ => True) [] _ _ _ _); [intros; exact I| intros; exact I| | constructor].
  intros a H. exfalso. exact (H I).
Defined.

Section Laws.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable SI : sinv L.

  #[using="Type"] Lemma si_below : forall a, ~ outside (si_fp SI) a -> a < hl_data_hi L.
  Proof. intros a H. destruct (si_data SI a H). lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma in_window_not_outside : forall (W : list ivl) u v a, In (u, v) W -> u <= a < v -> ~ outside W a.
  Proof.
    induction W as [|[x y] W IH]; cbn; intros u v a Hin Ha; [destruct Hin|].
    destruct Hin as [E|Hin]; [injection E as -> ->; tauto|]. intros [_ O]. exact (IH _ _ _ Hin Ha O).
  Qed.
  #[using="Type"] Lemma si_win : forall u v, In (u, v) (si_fp SI) -> hl_data_lo L <= u /\ v <= hl_data_hi L.
  Proof.
    intros u v Hin. pose proof (proj1 (Forall_forall _ _) (si_wf SI) _ Hin) as WF. simpl in WF.
    destruct (si_data SI u (in_window_not_outside _ u v u Hin ltac:(lia))) as (D1 & _).
    destruct (si_data SI (v - 1) (in_window_not_outside _ u v (v - 1) Hin ltac:(lia))) as (D2 & _). lia.
  Qed.
  #[using="Type"] Lemma si_fp_disjoint_gen : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "PA,$2.Pn,$2.P,Pu,$2.Pv,$2.P,(7.(8.$2.$2.)(9.$2.$2.R2.R1.)(:.VL,VSI,))(;.(<.(=.R5.R4.)R3.)(<.R2.R5.))(4.(:.VL,VSI,)R3.R2.)")
(* [comment removed for export] *).
  Proof.
    intros A n H. generalize dependent H. generalize (si_fp SI). induction l as [|[u v] W IH]; cbn; intros H; [exact I|].
    split; [apply H; left; reflexivity|]. apply IH. intros u' v' Hin. apply H. right. exact Hin.
  Qed.
  #[using="Type"] Lemma si_fp_disjoint_hi : forall A n, hl_data_hi L <= A -> disjoint_from (si_fp SI) A n.
  Proof. intros A n H. apply si_fp_disjoint_gen. intros u v Hin. destruct (si_win u v Hin). lia. Qed.
  #[using="Type"] Lemma si_fp_disjoint_offimg : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "PA,$2.Pn,$2.P,(;.(<.(=.R2.R1.)(>.VL,))(<.(?.VL,)R2.))P,(<.(>.VL,)(10.VL,))P,(<.(11.VL,)(?.VL,))(4.(:.VL,VSI,)R5.R4.)")
(* [comment removed for export] *).
  Proof. intros A n H D1 D2. apply si_fp_disjoint_gen. intros u v Hin. destruct (si_win u v Hin). lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma si_munch : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "PW,(0.$1.)Pm,P,(12.&40.)(13.(12.&8.))Pm',P,(12.&40.)(13.(12.&8.))P,(14.VL,VSI,R2.)P,(15.R4.R3.R2.)P,Pa,$2.P,(16.(17.(:.VL,VSI,)R1.))(17.R7.R2.)(14.VL,VSI,R4.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' HP MU HO. eapply (si_frame SI); [exact HP|]. intros a Ha NO.
    apply MU. rewrite wa_unsigned by exact Ha. exact (HO _ NO).
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma si_munch_offdata : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "PW,(0.$1.)Pm,P,(12.&40.)(13.(12.&8.))Pm',P,(12.&40.)(13.(12.&8.))P,(14.VL,VSI,R2.)P,(15.R4.R3.R2.)P,Pa,$2.P,(6.(<.(10.VL,)R1.)(18.R1.(11.VL,)))P,(19.VL,R2.)(17.R8.R3.)(14.VL,VSI,R4.)")
(* [comment removed for export] *).
  Proof. intros W m m' HP MU HO. eapply si_munch; [exact HP| exact MU|]. intros a NO. destruct (si_data SI a NO) as (D & WR & _). exact (HO a D WR). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma si_heap_presx : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "PLB,(0.$1:.)PSP,$2.PX,(0.$1.)Pm,P,(12.&40.)(13.(12.&8.))Pm',P,(12.&40.)(13.(12.&8.))P,(14.VL,VSI,R2.)P,(1;.Vsegs,VL,R6.R5.R4.R3.R2.)P,Pa,$2.P,(16.(17.(:.VL,VSI,)R1.))(17.R7.R2.)(14.VL,VSI,R4.)")
(* [comment removed for export] *).
  Proof.
    intros LB SP X m m' HP PX HO. eapply (si_frame SI); [exact HP|]. intros a Ha NO.
    destruct (si_data SI a NO) as (D & WR & NS). exact (proj1 (PX a Ha ltac:(right; left; split; [exact D| exact NS]) (HO a NO))).
  Qed.
  #[using="Type"] Lemma si_heap_pres : forall LB SP m m', si_P SI m -> heap_pres segs L LB SP m m' -> si_P SI m'.
  Proof. intros LB SP m m' HP PR. eapply si_heap_presx with (X := []); [exact HP| apply heap_presx_of_pres; exact PR| intros a H; exact I]. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma si_of_pristine : ltac2:(CDefT.buildp (gd_tbl_SInv ()) "Pm,Px,(12.&40.)(13.(12.&8.))P,Pa,$2.P,(6.(<.(10.VL,)R1.)(18.R1.(11.VL,)))P,(19.VL,R2.)P,(16.(1<.VL,R3.))(1=.(13.(12.&8.))A1.R5.(1>.R4.)(1?.(12.&8.)))(14.VL,VSI,R2.)")
(* [comment removed for export] *).
  Proof. intros m H. apply (si_init SI). intros a Ha NO. destruct (si_data SI a NO) as (D & WR & NS). exact (H a D WR NS). Qed.
End Laws.
