(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Cells Step CellsX Frame Arr Tac MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_hide H := lazymatch type of H with ?T => change (id T) in H end.
Ltac lx_unhide := repeat match goal with H : id ?T |- _ => change T in H end.
Ltac lx_unhide1 H := lazymatch type of H with id ?T => change T in H end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_LxAMpiTac () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.S"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.sub_fp"; "Corelib.Init.Datatypes.nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.add_inv"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.w32"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Peano.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.upd_bytes"; "Stdlib.ZArith.BinInt.Z.b2z"; "Stdlib.ZArith.BinInt.Z.ltb"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zlow"; "RocqVerifyHarness.AgentSubmission.LX.LxExpr.zswrap"; "stdpp.bitvector.definitions.bv_unsigned"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sub_inv"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sub_int_inv"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.nth"; "w0"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.sxz"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.div"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L68635160193.1500000ES1A1i2Hi3pre4Hlen3Hlp". (* [comment removed for export] *)
Lemma u32ro_cell : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pw,(0.&40.)P,(4.$5.R5.R4.(6.R3.))P,(7.(1.(0.&40.))(8.(0.&40.)R4.(9.R3.))(:.(0.&40.)R2.))P,(;.=R4.)(<.$5.R8.(=.R7.(>.+4.R5.))(?.$10.(11.R4.)(12.$10.)))")
(* [comment removed for export] *).
Proof.
  intros m A ws i w HB HN Hi.
  destruct (u32s_split ws (Z.to_nat i) w HN) as (pre & post & E & Hlen & Hu & Hlp).
  pose proof HB as HB'. rewrite Hu in HB'. apply bytes_at_app in HB' as [_ HB2]. apply bytes_at_app in HB2 as [HB3 _].
  rewrite Hlp in HB3. replace (A + Z.of_nat (4 * Z.to_nat i)) with (A + 4 * i) in HB3 by lia.
  split; [cbn; tauto|]. cbn -[le4]. rewrite ?app_nil_r. exact HB3.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L21917803222.11L40818989526.11L42872111828.11L46840727756.11L55008919423.1000000900B00N00W00`S2ws1i2HLS2ws1i2HLS2ws1i2Hi2HLS2ws1i2HLS2ws1i2HL". (* [comment removed for export] *)
Lemma u32rw_cell : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pw,(0.&40.)P,(13.$5.R5.R4.R3.)P,(7.(1.(0.&40.))(8.(0.&40.)R4.(9.R3.))(:.(0.&40.)R2.))P,(;.=R4.)(14.$5.R8.(=.R7.(>.+4.R5.))(?.$10.(11.R4.)(12.$10.)))")
(* [comment removed for export] *).
Proof.
  intros m A ws i w [HB HW] HN Hi.
  split; [exact (u32ro_cell m A ws i w HB HN Hi)|].
  cbn [cells_size csize Nat.add].
  assert (HL : (Z.to_nat i < length ws)%nat) by (apply nth_error_Some; rewrite HN; discriminate).
  replace (4 * Z.of_nat (length ws)) with (4 * i + (4 + (4 * Z.of_nat (length ws) - 4 * i - 4))) in HW by lia.
  apply wr_at_app in HW; [|lia|lia]. destruct HW as [_ HW2]. apply wr_at_app in HW2; [|lia|lia]. destruct HW2 as [HW3 _]. exact HW3.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_limb_tac H i w V :=
  let N := fresh "N" in let C := fresh "LC" w in
  lazymatch type of H with
  | bytes_at ?sg ?mm ?A (u32s ?l) =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32ro_cell mm A l i w H N ltac:(lia)) as C;
      pose proof (limb32_nth_error _ _ _ N) as V; clear N
  | u32arr ?sg ?mm ?A ?l =>
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32ro_cell mm A l i w (u32arr_ro _ _ _ _ H) N ltac:(lia)) as C;
      pose proof (limb32_nth_error _ _ _ N) as V; clear N
  end.
Tactic Notation "lx_limb" constr(H) constr(i) ident(w) ident(V) := lx_limb_tac H i w V.

(* [comment removed for export] *)
Ltac lx_limb0_tac H FS i w V :=
  let N := fresh "N" in let C := fresh "LC" w in
  let go sg mm A l HB :=
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; lia];
      pose proof (u32ro_cell mm A l i w HB N ltac:(lia)) as C;
      pose proof (same_from_limb32 _ _ _ _ _ FS (PeanoNat.Nat.le_refl _) N) as V; clear N in
  lazymatch type of H with
  | bytes_at ?sg ?mm ?A (u32s ?l) => go sg mm A l H
  | u32arr ?sg ?mm ?A ?l => go sg mm A l (u32arr_ro _ _ _ _ H)
  end.
Tactic Notation "lx_limb0" constr(H) constr(FS) constr(i) ident(w) ident(V) := lx_limb0_tac H FS i w V.


(* [comment removed for export] *)
Lemma u32ro_cell_at : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pe,$2.Pw,(0.&40.)P,(4.$5.R6.R5.(6.R4.))P,(7.(1.(0.&40.))(8.(0.&40.)R5.(9.R4.))(:.(0.&40.)R2.))P,(;.=R5.)P,(7.$2.R5.(=.R8.(>.+4.R6.)))(<.$5.R:.R6.(?.$10.(11.R5.)(12.$10.)))")
(* [comment removed for export] *).
Proof. intros m A ws i e w H N Hi ->. exact (u32ro_cell m A ws i w H N Hi). Qed.
Lemma u32rw_cell_at : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pe,$2.Pw,(0.&40.)P,(13.$5.R6.R5.R4.)P,(7.(1.(0.&40.))(8.(0.&40.)R5.(9.R4.))(:.(0.&40.)R2.))P,(;.=R5.)P,(7.$2.R5.(=.R8.(>.+4.R6.)))(14.$5.R:.R6.(?.$10.(11.R5.)(12.$10.)))")
(* [comment removed for export] *).
Proof. intros m A ws i e w H N Hi ->. exact (u32rw_cell m A ws i w H N Hi). Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11799360824.24L13337980383.24L44286282321.24L68622580765.24L9766228530.27 00000S01401U02602WS1A2ws1i3pre4post4Hlen3Hlp2HL5Hlen'S1A2ws1i3pre2Hi4Hlen3Hlp2HL5Hlen'S1A2ws1i3pre2Hi4Hlen3Hlp2HL5Hlen'S1A2ws1i3pre2Hi4Hlen3Hlp2HL5Hlen'S2ws1i3pre4Hlen3Hlp2HL4pre'5Hlen'". (* [comment removed for export] *)
Lemma u32arr_upd_of_cell : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pe,$2.Pw,(0.&40.)Pv,(0.&40.)P,(13.$5.R8.R6.R5.)P,(7.(1.(0.&40.))(8.(0.&40.)R6.(9.R5.))(:.(0.&40.)R3.))P,(;.=R6.)P,(7.$2.R6.(=.R9.(>.+4.R7.)))P,(15.(?.(16.$2.$2.)(17.$2.$2.R7.(=.R7.+4.))(12.(16.$2.$2.)))R<.R;.)P,(18.$5.R=.R<.)P,(14.$5.R=.R9.(?.$10.(11.R7.)(12.$10.)))(13.$5.R>.R=.(19.(0.&40.)R<.(9.R;.)R8.))")
(* [comment removed for export] *).
Proof.
  intros m m' A ws i e w v [HB HW] N Hi -> MU WM [[_ HC] _].
  cbn -[le4] in HC. rewrite app_nil_r in HC.
  destruct (u32s_split ws (Z.to_nat i) w N) as (pre & post & E & Hlen & Hu & Hlp).
  assert (HL : (Z.to_nat i < length ws)%nat) by (apply nth_error_Some; rewrite N; discriminate).
  destruct (upd_app_split ws (Z.to_nat i) v HL) as (pre' & y & post' & E' & Hlen' & Hupd).
  rewrite E in E'. apply list_basics.list.app_inj_1 in E' as [E1 E2]; [|lia]. injection E2 as E3 E4. subst pre' post' y.
  split.
  - rewrite Hupd, u32s_app. cbn [u32s flat_map]. fold (u32s post). rewrite Hu in HB.
    apply bytes_at_app in HB as [HB1 HB2]. apply bytes_at_app in HB2 as [_ HB3].
    apply bytes_at_app. split.
    + eapply bytes_at_transport; [exact HB1 | exact MU |]. cbn [disjoint_from]. rewrite Hlp. lia.
    + rewrite Hlp. replace (A + Z.of_nat (4 * Z.to_nat i)) with (A + 4 * i) by lia.
      apply bytes_at_app. split; [exact HC|]. rewrite length_le4.
      eapply bytes_at_transport; [| exact MU |].
      { rewrite length_le4, Hlp in HB3. replace (A + Z.of_nat (4 * Z.to_nat i) + Z.of_nat 4) with (A + 4 * i + Z.of_nat 4) in HB3 by lia. exact HB3. }
      cbn [disjoint_from]. lia.
  - rewrite upd_length. eapply wr_at_transport; [exact HW | exact WM].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L19506921979.21L30270589791.23L44279943791.2100000900M00gS2xs2ys1iS2xs2ys2lx2la3ELA2LXS1X1A2xs2ys2lx2la1i3DA'2Hi". (* [comment removed for export] *)
Lemma u32ro_next : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PX,$2.PA,$2.Pxs,(3.(0.&40.))Pxs0,(3.(0.&40.))Pys,(3.(0.&40.))Pys0,(3.(0.&40.))Plx,$2.Pla,$2.Pi,$2.Pe,$2.Pv,(0.&40.)P,(1:.(1;.(7.$2.R:.R;.)(1;.(7.$2.R4.R5.)(7.(3.(0.&40.))R6.R8.)))(1:.(;.(=.R:.(>.+4.R4.))R;.)(;.(=.R;.(>.+4.R5.))R:.)))P,(13.$5.R=.R<.(19.(0.&40.)R:.(9.R4.)R2.))P,(7.$2.(1<.(1=.(0.&40.)R;.))R7.)P,(1>.(0.&40.)(9.R6.)R<.R;.)P,(4.$5.R11.R>.(6.R;.))P,(7.$2.(1<.(1=.(0.&40.)R<.))R9.)P,(1>.(0.&40.)(9.R9.)R=.R<.)P,(1;.(;.=R:.)(1?.R:.R<.))P,(7.$2.R:.(=.R13.(>.+4.R;.)))P,(15.(?.(16.$2.$2.)(17.$2.$2.R;.(=.R;.+4.))(12.(16.$2.$2.)))R16.R15.)(20.(3.(0.&40.))Lys',(3.(0.&40.))(1;.(4.$5.R17.R15.(6.R1.))(1;.(7.$2.(1<.(1=.(0.&40.)R1.))R?.)(1>.(0.&40.)(21.(9.R>.))R1.R11.))))")
(* [comment removed for export] *).
Proof.
  intros m m' X A xs xs0 ys ys0 lx la i e v DA HX LX FX HA LA FA Hi -> MU.
  destruct DA as [(EA & ELA & EYA)|DA'].
  - exists (upd xs (Z.to_nat i) v). split; [rewrite EA; exact (u32arr_ro _ _ _ _ HX)|].
    split; [rewrite upd_length; lia| rewrite EYA; apply same_from_upd; exact FX].
  - exists ys. split; [eapply u32ro_transport; [exact HA| exact MU| cbn [disjoint_from]; rewrite LA; lia]|].
    split; [exact LA| eapply same_from_weaken; [exact FA|lia]].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_limb_ro_tac H FS i E B0 B w V :=
  let N := fresh "N" in let C := fresh "LC" w in let HB := fresh "IB" w in let HB0 := fresh "IZ" w in
  let go mm A l HA :=
      pose proof (B0 : 0 <= i) as HB0; pose proof (B : (Z.to_nat i < length l)%nat) as HB;
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; clear - N HB; lia];
      pose proof (u32ro_cell_at mm A l i _ w HA N HB0 E) as C;
      pose proof (same_from_limb32 _ _ _ _ _ FS (PeanoNat.Nat.le_refl _) N) as V; clear N HB HB0 in
  lazymatch type of H with
  | bytes_at _ ?mm ?A (u32s ?l) => go mm A l H
  | u32arr _ ?mm ?A ?l => go mm A l (u32arr_ro _ _ _ _ H)
  end.
Tactic Notation "lx_limb_ro" constr(H) constr(FS) constr(i) constr(E) uconstr(B0) uconstr(B) ident(w) ident(V) := lx_limb_ro_tac H FS i E B0 B w V.
(* [comment removed for export] *)
Ltac lx_limb_rw_tac H i E B0 B w N :=
  let C := fresh "LC" w in let HB := fresh "IB" w in let HB0 := fresh "IZ" w in
  lazymatch type of H with
  | u32arr _ ?mm ?A ?l =>
      pose proof (B0 : 0 <= i) as HB0; pose proof (B : (Z.to_nat i < length l)%nat) as HB;
      destruct (nth_error l (Z.to_nat i)) as [w|] eqn:N; [| exfalso; apply nth_error_None in N; clear - N HB; lia];
      pose proof (u32rw_cell_at mm A l i _ w H N HB0 E) as C; clear HB HB0
  end.
Tactic Notation "lx_limb_rw" constr(H) constr(i) constr(E) uconstr(B0) uconstr(B) ident(w) ident(N) := lx_limb_rw_tac H i E B0 B w N.

(* [comment removed for export] *)
Ltac lx_limbs_clear := repeat match goal with C : ro_cells _ _ _ [C4 _] |- _ => clear C end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac lx_cur_mem :=
  lazymatch goal with
  | |- _ (MS _ _ _ _ _ ?mx _) => mx
  | |- context [MS _ _ _ _ _ ?mx (seg_rom _)] => mx
  end.
Tactic Notation "lx_rn_u32" constr(A) ident(N) :=
  let mx := lx_cur_mem in match goal with H : u32arr _ mx A _ |- _ => rename H into N end.
Tactic Notation "lx_rn_ro32" constr(A) ident(N) :=
  let mx := lx_cur_mem in match goal with H : bytes_at _ mx A (u32s _) |- _ => rename H into N end.
Tactic Notation "lx_rn_rw" constr(A) ident(N) :=
  let mx := lx_cur_mem in match goal with H : rw_cells _ mx A _ |- _ => rename H into N end.
Tactic Notation "lx_rn_stk" ident(N) :=
  let mx := lx_cur_mem in match goal with H : stk _ mx _ _ |- _ => rename H into N end.
Tactic Notation "lx_rn_munch" ident(N) :=
  let mx := lx_cur_mem in match goal with H : munch _ _ mx |- _ => rename H into N end.
Tactic Notation "lx_rn_wmono" ident(N) :=
  let mx := lx_cur_mem in match goal with H : wmono _ _ mx |- _ => rename H into N end.
Tactic Notation "lx_rn_mi" ident(N) :=
  let mx := lx_cur_mem in match goal with H : mem_inv _ mx |- _ => rename H into N end.
Tactic Notation "lx_rn_aobj" constr(A) ident(N) :=
  let mx := lx_cur_mem in match goal with H : aobj _ _ _ mx A _ |- _ => rename H into N end.

(* [comment removed for export] *)
Ltac lx_munch_as W :=
  let mx := lx_cur_mem in
  match goal with H : munch ?W' ?m0 mx |- _ =>
    tryif constr_eq W W' then idtac else (replace W' with W in H by (repeat (f_equal; try lia)); idtac) end.

(* [comment removed for export] *)
Lemma upd_length_Z : forall (l : list word) i v n, Z.of_nat (length l) = n -> Z.of_nat (length (upd l i v)) = n.
Proof. intros. rewrite upd_length. assumption. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Tactic Notation "xlia" ne_hyp_list(l) := clear - l; lia.
Ltac xlia0 := clear; lia.
(* [comment removed for export] *)
Definition lx_keepv {A : Type} (x : A) : Prop := True.
Lemma lx_keepv_intro {A : Type} (x : A) : lx_keepv x. Proof. exact I. Qed.
Ltac lx_arith_shapeM T :=
  lazymatch T with
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac | @eq Z _ _ => idtac | @eq nat _ _ => idtac
  | ?A /\ ?B => lx_arith_shapeM A; lx_arith_shapeM B | ?A \/ ?B => lx_arith_shapeM A; lx_arith_shapeM B | ~ ?A => lx_arith_shapeM A
  | False => idtac
  end.
(* [comment removed for export] *)
Ltac lx_prune_mpi :=
  repeat match goal with H : ?T |- _ =>
    lazymatch type of T with Prop => tryif lx_arith_shapeM T then fail else clear H end end.
Ltac lx_data_var T :=   (* [comment removed for export] *)
  match goal with
  | y : Z |- _ => lazymatch T with context [y] => idtac end
  | y : bv _ |- _ => lazymatch T with context [y] => idtac end
  | y : list _ |- _ => lazymatch T with context [y] => idtac end
  | y : nat |- _ => lazymatch T with context [y] => idtac end
  end.
Ltac lx_slim :=
  lx_prune_mpi;
  repeat match goal with x : _ |- _ =>
    lazymatch goal with _ : lx_keepv x |- _ => fail | _ =>
      lazymatch type of x with Prop => fail | _ =>
        lazymatch goal with |- context [x] => pose proof (lx_keepv_intro x) end end end end;
  repeat match goal with H : ?T |- _ =>
    lazymatch T with lx_keepv _ => fail | _ =>
      lazymatch type of T with Prop =>
        tryif (match goal with K : lx_keepv ?x |- _ => lazymatch T with context [x] => idtac end end) then fail
        else tryif lx_data_var T then clear H else fail end end end;
  repeat match goal with K : lx_keepv _ |- _ => clear K end.
(* [comment removed for export] *)
Ltac lx_stray_var T :=
  match goal with
  | y : ?Ty |- _ => lazymatch type of Ty with Prop => fail | _ =>
      lazymatch T with context [y] => lazymatch goal with |- context [y] => fail | |- _ => idtac end end end
  end.
(* [comment removed for export] *)
Ltac lx_slim_tight :=
  lx_prune_mpi;
  repeat match goal with H : ?T |- _ =>
    lazymatch type of T with Prop => tryif lx_stray_var T then clear H else fail end end.
Ltac klia := first [ lx_slim_tight; first [ clear_disj; lia | prune_disj; lia ] | prune_disj; lia | lia ].


(* [comment removed for export] *)
Ltac lx_gc :=
  repeat match goal with
         | H : forall _ : Z, 1 <= _ -> _ |- _ => clear H
         | H : 0 <= ?v, H' : 0 <= - ?v + 7 |- _ => is_var v; clear H H'
         | H : 0 <= ?v, H' : 0 <= - ?v + 18446744073709551615 |- _ =>
             is_var v; lazymatch goal with _ : v = _ |- _ => fail | _ => clear H H' end
         | H : Z.of_nat (length ?l) = Z.of_nat (length ?l) |- _ => clear H
         | H : Z.of_nat ?n = Z.of_nat ?n |- _ => clear H
         end;
  repeat match goal with v : Z |- _ => clear v end.
(* [comment removed for export] *)
Ltac lx_same_mem :=
  let mx := lx_cur_mem in
  lazymatch goal with E : mx = ?mm |- _ =>
    subst mx; repeat match goal with H1 : ?T, H2 : ?T |- _ => clear H2 end;
    try lx_rn_munch MU; try lx_rn_wmono WM
  end.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40231916450.900000FS1a1b2lo2hi2Ha2Hb1x2Hx". (* [comment removed for export] *)
Lemma sub_fp_in1 : forall (a b lo hi : Z) (W : list ivl), lo <= a -> b <= hi -> sub_fp [(a, b)] ((lo, hi) :: W).
Proof. intros a b lo hi W Ha Hb x [Hx _]. cbn. split; [lia| exact I]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L40231916450.1100000FS1a1b2lo2hi2Ha2Hb1x2Hx". (* [comment removed for export] *)
Lemma sub_fp_in2 : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pa,$2.Pb,$2.Plo,$2.Phi,$2.Pi1,$22.PW,(3.$22.)P,(;.R4.R6.)P,(;.R6.R4.)(23.(?.(16.$2.$2.)(17.$2.$2.R8.R7.)(12.(16.$2.$2.)))(?.$22.R4.(?.(16.$2.$2.)(17.$2.$2.R6.R5.)R3.)))")
(* [comment removed for export] *).
Proof. intros a b lo hi [u v] W Ha Hb x [_ [Hx _]]. cbn. split; [lia| exact I]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Lemma munch_local1 : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "PW,(3.$22.)Pm,P,(0.&40.)(1.(0.&8.))Pmm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pa,$2.Pb,$2.Plo,$2.Phi,$2.PW',(3.$22.)P,(7.(3.$22.)R9.(?.(16.$2.$2.)(17.$2.$2.R3.R2.)R1.))P,(15.R:.R9.R8.)P,(15.(?.(16.$2.$2.)(17.$2.$2.R7.R6.)(12.(16.$2.$2.)))R9.R8.)P,(;.R6.R8.)P,(;.R8.R6.)(15.R>.R=.R;.)")
(* [comment removed for export] *).
Proof. intros W m mm m' a b lo hi W' -> MU MUl Ha Hb. eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUl]. apply sub_fp_in1; assumption. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51439815961.6000006S1i2Hi". (* [comment removed for export] *)
Lemma same_from_upd_Z : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.Pv,(0.&40.)P,(1>.(0.&40.)(9.R2.)R4.R3.)P,(;.=R3.)(1>.(0.&40.)(9.(=.R4.+1.))(19.(0.&40.)R6.(9.R4.)R3.)R5.)")
(* [comment removed for export] *).
Proof. intros l l0 i v H Hi. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply same_from_upd. exact H. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L53111326921.5000006S1i2Hi". (* [comment removed for export] *)
Lemma same_from_Z : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.P,(1>.(0.&40.)(9.R1.)R3.R2.)P,(;.=R2.)(1>.(0.&40.)(9.(=.R3.+1.))R5.R4.)")
(* [comment removed for export] *).
Proof. intros l l0 i H Hi. eapply same_from_weaken; [exact H | lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51439815961.5000006S1i2Hi". (* [comment removed for export] *)
Lemma same_from_S_Z : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.P,(1>.(0.&40.)(21.(9.R1.))R3.R2.)P,(;.=R2.)(1>.(0.&40.)(9.(=.R3.+1.))R5.R4.)")
(* [comment removed for export] *).
Proof. intros l l0 i H Hi. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact H. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51439820542.700000>S1l2l01i2Hi2HL". (* [comment removed for export] *)
Lemma skipn_upd_Z : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.Pq,$2.Pv,(0.&40.)P,(1>.(0.&40.)(9.R3.)R5.R4.)P,(;.=R4.)P,(7.$2.R4.(=.R5.+1.))P,(7.$24.(1=.(0.&40.)R8.)(1=.(0.&40.)R7.))(7.(3.(0.&40.))(25.(0.&40.)(9.R6.)(19.(0.&40.)R9.(9.R7.)R5.))(25.(0.&40.)(9.R6.)R8.))")
(* [comment removed for export] *).
Proof.
  intros l l0 i q v FX Hi -> HL. apply same_from_skipn; [| rewrite upd_length; exact HL].
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. apply same_from_upd. exact FX.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35884662729.15000008S1l1i2HL". (* [comment removed for export] *)
Lemma add_inv_next : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Ply,(3.(0.&40.))Plz,(3.(0.&40.))Pi,$2.Pc,$2.Pc',$2.Pwa,(0.&40.)Pwb,(0.&40.)Pv,(0.&40.)P,(26.R9.R6.R5.R8.R7.)P,(;.=R7.)P,(27.(9.R8.)(1=.(0.&40.)R;.))P,(7.$2.(28.R;.(9.R9.))(29.R6.))P,(7.$2.(28.R;.(9.R:.))(29.R6.))P,(7.$2.(=.(29.R6.)(>.(2:.+2.+20.)R9.))(=.(=.(29.R8.)(29.R7.))R:.))(26.(19.(0.&40.)R?.(9.R<.)R7.)(=.R<.+1.)R:.R>.R=.)")
(* [comment removed for export] *).
Proof.
  intros l ly lz i c c' wa wb v INV Hi HL VA VB V.
  eapply add_inv_step; [exact Hi | exact INV | apply lval_upd_ge; lia | rewrite (limb32_upd_same _ _ _ HL), VA, VB; exact V].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L30408843469.12L51087517563.12L59309038033.14L59483276326.1200000L00h01J01fS1l1k1i2bs2Hb2Hi2Hk1j2Hj3HjlS1l1k1i2bs2Hb2Hi2Hk1j2Hj3HjlS1l1k1i2bs2Hb2Hi2Hk1j2Hj3Hjl2l12l2S1l1k1i2bs2Hb2Hi2Hk1j2Hj3Hjl". (* [comment removed for export] *)
Lemma same_from_upd_bytes1 : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&8.))Pl0,(3.(0.&8.))Pk,$24.Pi,$24.Pbs,(3.(0.&8.))P,(1>.(0.&8.)R3.R5.R4.)P,(7.$24.(1=.(0.&8.)R2.)#1.)P,(27.R4.R5.)P,(2;.R6.(1=.(0.&8.)R8.))(1>.(0.&8.)R7.(2<.R9.R6.R5.)R8.)")
(* [comment removed for export] *).
Proof.
  intros l l0 k i bs H Hb Hi Hk j Hj.
  destruct (Nat.lt_ge_cases j (length l)) as [Hjl|Hjl].
  - rewrite upd_bytes_nth by lia. rewrite Hb.
    destruct (Nat.leb_spec0 i j); destruct (Nat.ltb_spec0 j (i + 1)); cbn [andb]; try (apply H; exact Hj). exfalso; lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite upd_bytes_length by lia; lia).
    rewrite <- (H j Hj). symmetry. apply nth_error_None. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30410940490.700000>S1l1i2bs2Hb2Hi". (* [comment removed for export] *)
Lemma upd_bytes1_length_Z : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&8.))Pi,$24.Pbs,(3.(0.&8.))Pq,$2.P,(7.$2.(1<.(1=.(0.&8.)R4.))R1.)P,(7.$24.(1=.(0.&8.)R3.)#1.)P,(27.R5.(1=.(0.&8.)R6.))(7.$2.(1<.(1=.(0.&8.)(2<.R7.R6.R5.)))R4.)")
(* [comment removed for export] *).
Proof. intros l i bs q H Hb Hi. rewrite upd_bytes_length by lia. exact H. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lx_deads := try (exfalso; lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L11607912823.3L14698736771.3L16046136858.3L33237931026.3L38717875063.3L45173510281.3L62544261284.3L63945421208.3L8931307546.3 00000100400<00?00@00C00K00N00TSS1uS1u2Hu1HS1uSS1uS1u2Hu1HS1uS1u2Hu". (* [comment removed for export] *)
Lemma lx_s32_cases : forall u, 0 <= u < 2^32 ->
  zswrap 32 u = (if u <? 2^31 then u else u - 2^32)
  /\ zlow 64 (zswrap 32 u) = (if u <? 2^31 then u else u + 2^64 - 2^32).
Proof.
  intros u Hu. unfold zswrap, zlow. change (2^(32-1)) with (2^31).
  destruct (Z.ltb_spec u (2^31)).
  - rewrite (Z.mod_small (u + 2^31)) by lia. split; [lia|]. rewrite Z.mod_small; lia.
  - replace ((u + 2^31) mod 2^32) with (u + 2^31 - 2^32).
    2:{ rewrite <- (Z.mod_add _ (-1)) by lia. symmetry. rewrite Z.mod_small; lia. }
    split; [lia|]. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0?L10078563561.24L10607966368.23L10610367392.19L1067926784.10 L12894941614.9 L13216454793.12L1345319392.12 L14263214353.12L15377686188.24L16040059680.23L16046136858.24L16046136858.25L18182249067.9 L19253873790.25L19535676378.16L20063186838.24L2732954010.9  L27474026268.12L29960789398.13L29991980614.15L32072517845.25L32174647165.9 L33173938034.16L34049544272.12L34223556460.12L38715563597.23L38715569693.16L38715831964.10L38717875063.24L38717875063.25L39820634055.23L41602857700.25L42468486635.17L42470583725.11L42470663484.4 L42470762042.5 L46834694508.8 L53038309310.16L55391761397.9 L6621013465.9  L6691722417.16 L9979216610.16 00000I00i01C01R01a02:02S02l03E03e04P05:05I06506G07107@07^08308H08`08o09A09Z0:80:T0:f0;30;L0;d0<@0<X0<j0=90=:0=>0=N0=`0>40>H0?40?5S2wa2wb1c2ua2ub3tt22E12E2S2wa2wb1c2ua2ub2tt3tt23Rt22E12E2S2wa2wb1c2ua2ub2tt3tt23Rt2S2wa2wb1c2ua2ubS2wa1c2ua2tt2H1S2wa2wb1c2ua2ub2tt3tt22H1S2wa2wb1c2ua2ub2tt3tt22H1S2wa2wb1c2ua2ub2tt3tt22H1S2wa2wb1c2ua2ub3tt22E12E2S2wa2wb1c2ua2ub2tt3tt23Rt22E12E2S2wa2wb1c2Hc2ua2Ra2ub2Rb2Rt3tt23Rt22E12E21HS2wa2wb1c2Hc2ua2Ra2ub2Rb2tt2Rt3Rt22E12E21HS2wa1c2ua2tt2H1S2wa2wb1c2Hc2ua2Ra2ub2Rb2tt2Rt3Rt22E12E21W1HS2wa2wb1c2ua2ub2ttS2wa2wb1c2Hc2ua2Ra2ub2Rt3tt23Rt22E12E21W1HS2wa1c2ua2tt2H1S2wa2wb1c2ua2ub2tt3tt21H2H02H1S2wa2wb1c2ua2ub2tt2RtS2wa2wb1c2ua2ub2Rb2ttS2wa2wb1c2ua2ub2tt2E12E2S2wa1c2ua2tt2H1S2wa2wb1c2ua2ub2ttS2wa2wb1c2ua2ub2tt3tt22H1S2wa2wb1c2ua2ub2tt3tt21H2H02H1S2wa2wb1c2ua2ub2tt3tt22E12E2S2wa2wb1c2ua2ub2ttS2wa2wb2ua2ubS2wa2wb1c2ua2ub3tt22E12E2S2wa2wb1c2ua2ub2tt2E12E2S2wa2wb1c2ua2ub2tt3tt22E12E2S2wa2wb1c2ua2ub2tt2E12E2S2wa2wb1c2ua2ub2ttS2wa2wb1c2ua2ubSS2waS2wa2wb2ua2Ra2ubS2wa2wb1c2ua2ub2ttS2wa1c2ua2tt1H2H02H1S2wa1c2ua2tt1H2H02H1S1c2Hc2ua2ub2tt3tt23Ett2H14Ett22Rb2H22Ra3Rt2F". (* [comment removed for export] *)
Lemma lx_core_add_exact : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pwa,(0.&40.)Pwb,(0.&40.)Pc,$2.Pc',$2.P,(1;.(;.=R2.)(;.R2.+1.))P,(7.$2.R2.(=.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R5.))))))(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.(30.+20.(2?.+20.(31.&40.R4.)))(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.))))))))))(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))))))(1;.(1;.(;.=R3.)(;.R3.+1.))(7.$2.(=.(29.(32.&40.(30.+20.(2?.+20.(=.(30.+20.(2?.+20.(31.&40.R5.)))(30.+20.(2?.+20.(=.R4.(30.+20.(2?.+20.(31.&40.R6.)))))))))))(>.(2:.+2.+20.)R3.))(=.(=.(29.R6.)(29.R5.))R4.)))")
(* [comment removed for export] *).
Proof.
  intros wa wb c c' Hc ->.
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  unfold w32. change (zlow 32 (bv_unsigned wa)) with (bv_unsigned wa mod 2^32). change (zlow 32 (bv_unsigned wb)) with (bv_unsigned wb mod 2^32).
  set (ua := bv_unsigned wa mod 2^32) in *. set (ub := bv_unsigned wb mod 2^32) in *.
  destruct (lx_s32_cases ua ltac:(lia)) as [Ea Ua]. rewrite Ua.
  assert (Et : zlow 32 (c + zswrap 32 ua) = (c + ua) mod 2^32).
  { unfold zlow. rewrite Ea. destruct (ua <? 2^31); [reflexivity|]. rewrite <- (Z.mod_add _ 1) by lia. f_equal. lia. }
  rewrite Et. pose proof (Z.mod_pos_bound (c + ua) (2^32) ltac:(lia)) as Rt. set (tt := (c + ua) mod 2^32) in *.
  destruct (lx_s32_cases tt ltac:(lia)) as [Etz Ut]. rewrite Ut.
  destruct (lx_s32_cases ub ltac:(lia)) as [Eb _].
  assert (Et2 : zlow 32 (zswrap 32 ub + zswrap 32 tt) = (ub + tt) mod 2^32).
  { unfold zlow. rewrite Eb, Etz. destruct (ub <? 2^31); destruct (tt <? 2^31);
    first [reflexivity | rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia | rewrite <- (Z.mod_add _ 2) by lia; f_equal; lia]. }
  rewrite Et2. pose proof (Z.mod_pos_bound (ub + tt) (2^32) ltac:(lia)) as Rt2. set (tt2 := (ub + tt) mod 2^32) in *.
  destruct (lx_s32_cases tt2 ltac:(lia)) as [Et2z Ut2]. rewrite Ut2.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 tt2)) with (zlow 64 (zswrap 32 tt2)). rewrite Ut2.
  assert (E1 : (if tt <? 2^31 then tt else tt + 2^64 - 2^32) <? (if ua <? 2^31 then ua else ua + 2^64 - 2^32) = (tt <? ua)).
  { clear - Rt Ra. destruct (Z.ltb_spec tt (2^31)); destruct (Z.ltb_spec ua (2^31)); destruct (Z.ltb_spec tt ua);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  assert (E2 : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) <? (if tt <? 2^31 then tt else tt + 2^64 - 2^32) = (tt2 <? tt)).
  { clear - Rt Rt2. destruct (Z.ltb_spec tt2 (2^31)); destruct (Z.ltb_spec tt (2^31)); destruct (Z.ltb_spec tt2 tt);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite E1, E2.
  assert (W : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) mod 2^32 = tt2).
  { destruct (tt2 <? 2^31). apply Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
  rewrite W.
  assert (Ett : tt = c + ua - (if c + ua <? 2^32 then 0 else 2^32)).
  { subst tt. destruct (Z.ltb_spec (c + ua) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Ett2 : tt2 = ub + tt - (if ub + tt <? 2^32 then 0 else 2^32)).
  { subst tt2. destruct (Z.ltb_spec (ub + tt) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  clearbody ua ub tt tt2. clear - Hc Ra Rb Rt Rt2 Ett Ett2.
  destruct (Z.ltb_spec (c + ua) (2^32)); destruct (Z.ltb_spec (ub + tt) (2^32));
  destruct (Z.ltb_spec tt ua); destruct (Z.ltb_spec tt2 tt); cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00Z0?L10607966368.24L10610367392.20L13479810524.17L16040059680.24L16046136858.25L16046136858.26L20945666908.11L20970880066.26L22474624769.11L22559072846.17L22690972462.25L24426245150.17L24477672798.26L29960789398.15L29991978449.10L31475996805.7 L32787949434.12L33728999712.12L36251267854.25L38305541067.7 L38715563597.24L38715831837.12L38715833611.17L38717875063.25L38717875063.26L39820634055.24L42468486635.18L42470583725.13L42470663484.4 L42470762042.5 L44693612646.17L45461859852.11L46834694508.8 L48655913200.11L49477572544.11L52625655997.25L53051919823.17L55544828537.11L62510211689.26L6691722675.14 L68706118984.17L7968970551.17 00000P00j00k01K01i02F02`03503J03\04:04;04X04m05=05I05X05g06=06N06j07707I07_08408P08b09109209609H09b0:20:G0:\0;20;30;H0;]0<C0<U0<gS2wa2wb1c2ua2ub2tt3tt23Rt22E12E2S2wa2wb1c2ua2ub2tt3tt23Rt2FS2wa2wb1c2ua2ub2tt3tt23Rt22E12E2S2wa2wb1c2Hc2ua2Ra2ub3tt22E21HS2wa2wb1c2ua2ub2Rb2tt2Rt2E11HS2wa2wb1c2ua2ub2tt1H2H02H1S2wa2wb1c2ua2ub2tt2E1S2wa2wb1c2ua2ub2tt2H1S2wa2wb1c2ua2ub2ttS2wa2wb1c2Hc2ua2Ra2ub3tt22E21HFS2wa2wb1c2ua2ub2Rb2tt2Rt2E11HS2wa2wb1c2ua2ub2tt2RtS2wa2wb2ua2ub2RbS2wa1c2ua2H0S2wa2wb1c2ua2ubS2wa2wb1c2ua2ubS2wa2wb1c2ua2ub3tt22E2S2wa1c2Hc2ua1H2H0S2wa2wb1c2ua2ub2tt3tt22E12E2S2wa2wb2ua2ubS2wa2wb1c2ua2ub2ttS2wa2wb1c2ua2ub3tt22E2S2wa2wb1c2ua2ub2tt2E1S2wa2wb1c2ua2ub2tt3tt22E12E2S2wa2wb1c2ua2ub2ttS2wa2wb1c2ua2ubSS2waS2wa2wb1c2ua2ub2ttS2wa2wb1c2ua2ub2tt1H2H02H1S2wa2wb2ua2Ra2ubS2wa2wb1c2ua2ub2tt2H1S2wa2wb1c2ua2ub2tt2H1S2wa2wb1c2ua2ub3tt22E2FS2wa2wb1c2ua2ub2tt2H1S2wa2wb1c2ua2ub2tt2E1S1c2Hc2ua2Ra2ub2Rb2tt3tt23Rt23Ett4Ett2S2wa2wb1c2ua2ub2ttS2wa2wb1c2ua2ub2tt". (* [comment removed for export] *)
Lemma lx_core_sub_exact : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pwa,(0.&40.)Pwb,(0.&40.)Pc,$2.Pc',$2.P,(1;.(;.=R2.)(;.R2.+1.))P,(7.$2.R2.(=.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(31.&40.R5.))))R3.))(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.(33.R3.)(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R4.))))))))(1;.(1;.(;.=R3.)(;.R3.+1.))(7.$2.(34.(29.(32.&40.(30.+20.(2?.+20.(=.(33.(30.+20.(2?.+20.(31.&40.R5.))))(30.+20.(2?.+20.(=.(33.R4.)(30.+20.(2?.+20.(31.&40.R6.)))))))))))(>.(2:.+2.+20.)R3.))(34.(34.(29.R6.)(29.R5.))R4.)))")
(* [comment removed for export] *).
Proof.
  intros wa wb c c' Hc ->.
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  pose proof (Z.mod_pos_bound (bv_unsigned wb) (2^32) ltac:(lia)) as Rb.
  unfold w32. change (zlow 32 (bv_unsigned wa)) with (bv_unsigned wa mod 2^32). change (zlow 32 (bv_unsigned wb)) with (bv_unsigned wb mod 2^32).
  set (ua := bv_unsigned wa mod 2^32) in *. set (ub := bv_unsigned wb mod 2^32) in *.
  destruct (lx_s32_cases ua ltac:(lia)) as [Ea Ua]. rewrite Ua.
  destruct (lx_s32_cases ub ltac:(lia)) as [Eb Ub]. rewrite Ub.
  assert (Et : zlow 32 (- c + zswrap 32 ua) = (ua - c) mod 2^32).
  { unfold zlow. rewrite Ea. destruct (ua <? 2^31); [f_equal; lia|]. rewrite <- (Z.mod_add _ 1) by lia. f_equal. lia. }
  rewrite Et. pose proof (Z.mod_pos_bound (ua - c) (2^32) ltac:(lia)) as Rt. set (tt := (ua - c) mod 2^32) in *.
  destruct (lx_s32_cases tt ltac:(lia)) as [Etz Ut]. rewrite Ut.
  assert (Et2 : zlow 32 (- zswrap 32 ub + zswrap 32 tt) = (tt - ub) mod 2^32).
  { unfold zlow. rewrite Eb, Etz. destruct (ub <? 2^31); destruct (tt <? 2^31);
    first [f_equal; lia | rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia | rewrite <- (Z.mod_add _ (-1)) by lia; f_equal; lia]. }
  rewrite Et2. pose proof (Z.mod_pos_bound (tt - ub) (2^32) ltac:(lia)) as Rt2. set (tt2 := (tt - ub) mod 2^32) in *.
  destruct (lx_s32_cases tt2 ltac:(lia)) as [Et2z Ut2].
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 tt2)) with (zlow 64 (zswrap 32 tt2)). rewrite Ut2.
  assert (E1 : (if ua <? 2^31 then ua else ua + 2^64 - 2^32) <? c = (ua <? c)).
  { clear - Ra Hc. destruct (Z.ltb_spec ua (2^31)); destruct (Z.ltb_spec ua c); first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  assert (E2 : (if tt <? 2^31 then tt else tt + 2^64 - 2^32) <? (if ub <? 2^31 then ub else ub + 2^64 - 2^32) = (tt <? ub)).
  { clear - Rt Rb. destruct (Z.ltb_spec tt (2^31)); destruct (Z.ltb_spec ub (2^31)); destruct (Z.ltb_spec tt ub);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite E1, E2.
  assert (W : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) mod 2^32 = tt2).
  { destruct (tt2 <? 2^31). apply Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
  rewrite W.
  assert (Ett : tt = ua - c + (if ua <? c then 2^32 else 0)).
  { subst tt. destruct (Z.ltb_spec ua c). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. rewrite Z.mod_small; lia. }
  assert (Ett2 : tt2 = tt - ub + (if tt <? ub then 2^32 else 0)).
  { subst tt2. destruct (Z.ltb_spec tt ub). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. rewrite Z.mod_small; lia. }
  clearbody ua ub tt tt2. clear - Hc Ra Rb Rt Rt2 Ett Ett2.
  destruct (Z.ltb_spec ua c); destruct (Z.ltb_spec tt ub); cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35884662729.15000008S1l1i2HL". (* [comment removed for export] *)
Lemma sub_inv_next : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Ply,(3.(0.&40.))Plz,(3.(0.&40.))Pi,$2.Pc,$2.Pc',$2.Pwa,(0.&40.)Pwb,(0.&40.)Pv,(0.&40.)P,(35.R9.R6.R5.R8.R7.)P,(;.=R7.)P,(27.(9.R8.)(1=.(0.&40.)R;.))P,(7.$2.(28.R;.(9.R9.))(29.R6.))P,(7.$2.(28.R;.(9.R:.))(29.R6.))P,(7.$2.(34.(29.R6.)(>.(2:.+2.+20.)R9.))(34.(34.(29.R8.)(29.R7.))R:.))(35.(19.(0.&40.)R?.(9.R<.)R7.)(=.R<.+1.)R:.R>.R=.)")
(* [comment removed for export] *).
Proof.
  intros l ly lz i c c' wa wb v INV Hi HL VA VB V.
  eapply sub_inv_step; [exact Hi | exact INV | apply lval_upd_ge; lia | rewrite (limb32_upd_same _ _ _ HL), VA, VB; exact V].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L10073075360.12L10610367392.10L10610367392.25L1067422848.15 L13216454793.14L1345319392.14 L14263214353.14L14932978186.11L16040053745.11L16041771040.10L16046136858.11L16046136858.6 L19253873790.11L19535939788.22L20391258919.9 L22132457208.6 L26383540702.9 L27474026268.14L29960789398.20L32072517845.11L32851065882.17L34049544272.14L34223556460.14L382104538.6   L38713785677.10L38715569820.11L38715833095.17L38715833611.22L38717875063.11L38717875063.6 L39012151722.9 L39818314951.10L41495978278.9 L41602857700.11L42468486635.23L42468565044.7 L42470583725.18L42470763425.8 L46834694508.10L46835005933.11L46841243916.12L48971658986.9 L5320509443.6  L56987601383.9 L6691722417.18 00000B00c01F01_02?02_03?03L03\04=04^04o05P05k06:06C06W07<07Z08308K08k09P09a0:>0:K0:a0;<0;U0;\0;k0<H0<\0=50=P0=Q0=i0=m0>=0>M0>b0?10?:0?I0@5S2wx2wa2mk2ux2ua1BS2wx2wa1c3cnd2ux2ua2ub2tt3tt23Rt2S2wx2wa1c3cnd2ux2ua1B2ub2tt3tt23Rt2S2wx2wa3cnd2ux2Rx2ua1B2ubS2wx2wa1c3cnd2ux2ua2ub2tt3tt22H1S2wx2wa1c3cnd2ux2ua2ub2tt3tt22H1S2wx2wa1c3cnd2ux2ua2ub2tt3tt22H1S2wx2wa2ux2uaS2wx2wa2ux2ua2RaS2wx2wa1c3cnd2ux2ua2ub2tt3tt23Rt2S2wx2wa1c3cnd2ux2ua2ub2Rb2tt2Rt1HS2wx1c2Hc2ux2Rx1HS2wx2wa1c3cnd2ux2ua2ub2Rb2tt2Rt1HS2wx2wa1c3cnd2ux2ua1B2ub2ttS2wx1c2ux2tt2H1S2wx1c2uxS2wx1c2ux2tt1H2H02H1S2wx2wa1c3cnd2ux2ua2ub2tt3tt21H2H02H1S2wx2wa1c3cnd2ux2ua1B2ub2tt2RtS2wx2wa1c3cnd2ux2ua2ub2ttS2wx2wa1c3cnd2ux2ua1B2ubS2wx2wa1c3cnd2ux2ua2ub2tt3tt22H1S2wx2wa1c3cnd2ux2ua2ub2tt3tt21H2H02H1S2wx1c2Hc2ux2Rx1HS2wx2wa1c3cnd2ux2ua2ub2tt3tt2S2wx2wa2ux2uaS2wx2wa3cnd2ux2ua1B2ubS2wx2wa1c3cnd2ux2ua1B2ub2ttS2wx2wa1c3cnd2ux2ua2ub2ttS2wx2uxS2wx1c2ux2tt2H1S2wx2wa1c3cnd2ux2ua2ub2tt3tt2S2wx1c2ux2tt1H2H02H1S2wx2wa1c3cnd2ux2ua2ub2ttS2wx2wa1c3cnd2ux2ua1B2ub2ttSS2wx2wa1c3cnd2ux2ua1B2ubS2wxS2wx2wa2ux2ua2RaS2wx2wa2ux2ua2RaS2wx2wa2mk2ux2ua2Ra1BS2wx1c2ux2tt2H1S2wx1c2uxS2wx1c2ux2tt2H1S1c2Hc2ux2ub2tt3tt23Ett2H14Ett22Rb2H22Rx3Rt2". (* [comment removed for export] *)
Lemma lx_core_addif_exact : forall (wx wa : word) (c c' mk cnd : Z), 0 <= c <= 1 -> mk = (if cnd =? 0 then 0 else -1) ->
  c' = Z.b2z (zlow 64 (zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wx))))) <? zlow 64 (zswrap 32 (zlow 32 (bv_unsigned wx))))
       + Z.b2z (zlow 64 (zswrap 32 (zlow 32 (Z.land (zswrap 32 (zlow 32 (bv_unsigned wa))) mk + zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wx)))))))
                <? zlow 64 (zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wx)))))) ->
  0 <= c' <= 1
  /\ w32 (Z_to_bv 64 (zswrap 32 (zlow 32 (Z.land (zswrap 32 (zlow 32 (bv_unsigned wa))) mk + zswrap 32 (zlow 32 (c + zswrap 32 (zlow 32 (bv_unsigned wx))))))))
     + 2^32 * c' = w32 wx + (if cnd =? 0 then 0 else w32 wa) + c.
Proof.
  intros wx wa c c' mk cnd Hc Hmk ->.
  pose proof (Z.mod_pos_bound (bv_unsigned wx) (2^32) ltac:(lia)) as Rx.
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  unfold w32. change (zlow 32 (bv_unsigned wx)) with (bv_unsigned wx mod 2^32). change (zlow 32 (bv_unsigned wa)) with (bv_unsigned wa mod 2^32).
  set (ux := bv_unsigned wx mod 2^32) in *. set (ua := bv_unsigned wa mod 2^32) in *.
  set (B := Z.land (zswrap 32 ua) mk).
  set (ub := if cnd =? 0 then 0 else ua).
  assert (Rb : 0 <= ub < 2^32) by (subst ub; destruct (cnd =? 0); lia).
  assert (EB : B mod 2^32 = ub).
  { subst B ub mk. destruct (cnd =? 0).
    - rewrite Z.land_0_r. reflexivity.
    - rewrite Z.land_m1_r. destruct (lx_s32_cases ua ltac:(lia)) as [Ea _]. rewrite Ea.
      destruct (ua <? 2^31). apply Z.mod_small; lia. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
  clearbody B.
  destruct (lx_s32_cases ux ltac:(lia)) as [Ex Ux]. rewrite Ux.
  assert (Et : zlow 32 (c + zswrap 32 ux) = (c + ux) mod 2^32).
  { unfold zlow. rewrite Ex. destruct (ux <? 2^31); [reflexivity|]. rewrite <- (Z.mod_add _ 1) by lia. f_equal. lia. }
  rewrite Et. pose proof (Z.mod_pos_bound (c + ux) (2^32) ltac:(lia)) as Rt. set (tt := (c + ux) mod 2^32) in *.
  destruct (lx_s32_cases tt ltac:(lia)) as [Etz Ut]. rewrite Ut.
  assert (Et2 : zlow 32 (B + zswrap 32 tt) = (ub + tt) mod 2^32).
  { unfold zlow. rewrite <- Zplus_mod_idemp_l, EB. rewrite Etz. destruct (tt <? 2^31); [reflexivity|].
    rewrite <- (Z.mod_add _ 1) by lia. f_equal. lia. }
  rewrite Et2. pose proof (Z.mod_pos_bound (ub + tt) (2^32) ltac:(lia)) as Rt2. set (tt2 := (ub + tt) mod 2^32) in *.
  destruct (lx_s32_cases tt2 ltac:(lia)) as [Et2z Ut2]. rewrite Ut2.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 tt2)) with (zlow 64 (zswrap 32 tt2)). rewrite Ut2.
  assert (E1 : (if tt <? 2^31 then tt else tt + 2^64 - 2^32) <? (if ux <? 2^31 then ux else ux + 2^64 - 2^32) = (tt <? ux)).
  { clear - Rt Rx. destruct (Z.ltb_spec tt (2^31)); destruct (Z.ltb_spec ux (2^31)); destruct (Z.ltb_spec tt ux);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  assert (E2 : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) <? (if tt <? 2^31 then tt else tt + 2^64 - 2^32) = (tt2 <? tt)).
  { clear - Rt Rt2. destruct (Z.ltb_spec tt2 (2^31)); destruct (Z.ltb_spec tt (2^31)); destruct (Z.ltb_spec tt2 tt);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite E1, E2.
  assert (W : (if tt2 <? 2^31 then tt2 else tt2 + 2^64 - 2^32) mod 2^32 = tt2).
  { clear - Rt2. destruct (tt2 <? 2^31). apply Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
  rewrite W.
  assert (Ett : tt = c + ux - (if c + ux <? 2^32 then 0 else 2^32)).
  { subst tt. clear - Hc Rx. destruct (Z.ltb_spec (c + ux) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Ett2 : tt2 = ub + tt - (if ub + tt <? 2^32 then 0 else 2^32)).
  { subst tt2. clear - Rb Rt. destruct (Z.ltb_spec (ub + tt) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  replace (if cnd =? 0 then 0 else ua) with ub by reflexivity.
  clearbody ux ua ub tt tt2. clear - Hc Rx Ra Rb Rt Rt2 Ett Ett2.
  destruct (Z.ltb_spec (c + ux) (2^32)); destruct (Z.ltb_spec (ub + tt) (2^32));
  destruct (Z.ltb_spec tt ux); destruct (Z.ltb_spec tt2 tt); cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L14521264942.8L24093133417.7L24093133544.6L36776597965.5L36782809976.700000800>00D00J00PS1a1b2H3S1a2HaS1a2HaS1b2HbS1b2Hb". (* [comment removed for export] *)
Lemma lx_lor_neg_ge : forall a b : Z, a < 0 -> b < 0 -> a <= Z.lor a b.
Proof.
  intros a b Ha Hb.
  assert (E : Z.lor a b = Z.lnot (Z.land (Z.lnot a) (Z.lnot b))) by (rewrite <- Z.lnot_lor, Z.lnot_involutive; reflexivity).
  rewrite E. unfold Z.lnot.
  pose proof (LxSoundDec.land_le_r (Z.pred (- a)) (Z.pred (- b)) ltac:(lia)) as H1.
  assert (H2 : 0 <= Z.land (Z.pred (- a)) (Z.pred (- b))) by (apply Z.land_nonneg; left; lia).
  pose proof (land_le_l (Z.pred (- a)) (Z.pred (- b)) ltac:(lia) ltac:(lia)) as H3. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00@0>L18926748705.2L22601333812.5L25419331756.8L2944553800.7 L32982217803.2L40102225204.7L43370070761.8L44007645543.8L44015172475.2L4678770535.3 L48892801899.5L51072042096.3L58784925145.2L65326342780.3L66376149475.8L6755913323.2 00000100600F00R00S00e00h00k00l00m01901A01F01N01^01_SS3cndS3cnd2Hc1v2L12L2S3cnd2Hc1n1hSS3cnd2Hc1n1h2Hh2n0S1vS1vSSS3cnd2Hc1n1hS3cnd2HcS3cndS3cnd2HcS3cnd2Hc1v2L12L2S". (* [comment removed for export] *)
Lemma lx_ct_mask_sra : forall cnd, 0 <= cnd < 2 ^ 32 ->
  Z.shiftr (zswrap 64 (Z.lor (- Z.shiftr (Z.shiftr (4294967296 * cnd) 32) 1) (- Z.shiftr (4294967296 * cnd) 32))) 63
  = (if cnd =? 0 then 0 else -1).
Proof.
  intros cnd Hc. rewrite !Z.shiftr_div_pow2 by lia.
  replace (4294967296 * cnd / 2 ^ 32) with cnd by (change (2^32) with 4294967296; rewrite Z.mul_comm, Z.div_mul; lia).
  unfold zswrap. change (2 ^ (64 - 1)) with (2^63).
  destruct (Z.eqb_spec cnd 0).
  - subst cnd. reflexivity.
  - assert (Hh : 0 <= cnd / 2 ^ 1 <= cnd) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    set (h := cnd / 2 ^ 1) in *.
    assert (L1 : Z.lor (- h) (- cnd) < 0) by (apply Z.lor_neg; lia).
    assert (L2 : - cnd <= Z.lor (- h) (- cnd)).
    { destruct (Z.eq_dec h 0) as [->|]. { cbn [Z.opp]. rewrite Z.lor_0_l. lia. } rewrite Z.lor_comm. apply lx_lor_neg_ge; lia. }
    set (v := Z.lor (- h) (- cnd)) in *. clearbody v. clearbody h.
    replace ((v + 2 ^ 63) mod 2 ^ 64) with (v + 2^63) by (symmetry; apply Z.mod_small; lia).
    replace (v + 2 ^ 63 - 2 ^ 63) with v by lia.
    symmetry. apply (Z.div_unique v (2^63) (-1) (v + 2^63)); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00D0?L16039673958.5 L16046136858.6 L22690972462.6 L2351079255.5  L29960789398.10L29960789398.5 L31475996805.7 L32787949563.7 L33728999841.7 L36251267854.6 L38305541067.7 L38715831964.7 L38715882763.5 L38717875063.6 L38907314636.8 L42470583725.8 L42470663484.3 L46834694637.5 L52625655997.6 L58582530748.8 00000?00P00a00m01<01K01W01`01i02202C02J02V02]02j03303403>03G03TS2wa1c2ua2tt2RtS2wa1c2Hc2ua2Ra1HS2wa1c2Hc2ua2Ra1HS2wa1c2ua2ttS2wa1c2ua2tt2RtS2wa1c2ua2tt2RtS2wa1c2ua2H0S2wa1c2uaS2wa1c2uaS2wa1c2uaS2wa1c2Hc2ua1H2H0S2wa2uaS2wa1c2ua2ttS2wa2uaS1c2ua2tt3EttS2wa1c2uaSS2wa2ua2RaS2wa1c2uaS1c2ua2tt3Ett". (* [comment removed for export] *)
Lemma lx_core_sub_int_exact : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pwa,(0.&40.)Pc,$2.Pc',$2.P,(1;.(;.=R2.)(1?.R2.(2:.+2.+1?.)))P,(7.$2.R2.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(31.&40.R4.))))R3.)))(1;.(1;.(;.=R3.)(;.R3.+1.))(7.$2.(34.(29.(32.&40.(30.+20.(2?.+20.(=.(33.R4.)(30.+20.(2?.+20.(31.&40.R5.))))))))(>.(2:.+2.+20.)R3.))(34.(29.R5.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros wa c c' Hc ->.
  pose proof (Z.mod_pos_bound (bv_unsigned wa) (2^32) ltac:(lia)) as Ra.
  unfold w32. change (zlow 32 (bv_unsigned wa)) with (bv_unsigned wa mod 2^32).
  set (ua := bv_unsigned wa mod 2^32) in *.
  destruct (lx_s32_cases ua ltac:(lia)) as [Ea Ua]. rewrite Ua.
  assert (Et : zlow 32 (- c + zswrap 32 ua) = (ua - c) mod 2^32).
  { unfold zlow. rewrite Ea. destruct (ua <? 2^31); [f_equal; lia|]. rewrite <- (Z.mod_add _ 1) by lia. f_equal. lia. }
  rewrite Et. pose proof (Z.mod_pos_bound (ua - c) (2^32) ltac:(lia)) as Rt. set (tt := (ua - c) mod 2^32) in *.
  destruct (lx_s32_cases tt ltac:(lia)) as [Etz Ut].
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 tt)) with (zlow 64 (zswrap 32 tt)). rewrite Ut.
  assert (E1 : (if ua <? 2^31 then ua else ua + 2^64 - 2^32) <? c = (ua <? c)).
  { clear - Ra Hc. destruct (Z.ltb_spec ua (2^31)); destruct (Z.ltb_spec ua c); first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite E1.
  assert (W : (if tt <? 2^31 then tt else tt + 2^64 - 2^32) mod 2^32 = tt).
  { clear - Rt. destruct (tt <? 2^31). apply Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
  rewrite W.
  assert (Ett : tt = ua - c + (if ua <? c then 2^32 else 0)).
  { subst tt. clear - Hc Ra. destruct (Z.ltb_spec ua c). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. rewrite Z.mod_small; lia. }
  clearbody ua tt. clear - Hc Ra Rt Ett.
  destruct (Z.ltb_spec ua c); cbn [Z.b2z]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L35884662729.13000008S1l1i2HL". (* [comment removed for export] *)
Lemma sub_int_inv_next : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Ply,(3.(0.&40.))Pi,$2.Pc0,$2.Pc,$2.Pc',$2.Pwa,(0.&40.)Pv,(0.&40.)P,(36.R8.R6.R4.R7.R5.)P,(;.=R7.)P,(27.(9.R8.)(1=.(0.&40.)R:.))P,(7.$2.(28.R:.(9.R9.))(29.R5.))P,(7.$2.(34.(29.R5.)(>.(2:.+2.+20.)R7.))(34.(29.R6.)R8.))(36.(19.(0.&40.)R=.(9.R;.)R6.)(=.R;.+1.)R8.R<.R:.)")
(* [comment removed for export] *).
Proof.
  intros l ly i c0 c c' wa v INV Hi HL VA V.
  eapply sub_int_inv_step; [exact Hi | exact INV | apply lval_upd_ge; lia | rewrite (limb32_upd_same _ _ _ HL), VA; exact V].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w0 : word := Z_to_bv 64 0.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L62065953426.4L62246692163.4L63816789802.400000:00D00NS2ws1i1k1HS2ws1i1k1HS2ws1i1k1H". (* [comment removed for export] *)
Lemma window_split : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pws,(3.(0.&40.))Pi,$24.Pk,$24.P,(2;.(37.R2.R1.)(1=.(0.&40.)R3.))(1;.(7.(3.(0.&40.))R4.(38.(0.&40.)(39.(0.&40.)R3.R4.)(38.(0.&40.)(39.(0.&40.)R2.(25.(0.&40.)R3.R4.))(25.(0.&40.)(37.R3.R2.)R4.))))(1;.(7.$24.(1=.(0.&40.)(39.(0.&40.)R3.R4.))R3.)(7.$24.(1=.(0.&40.)(39.(0.&40.)R2.(25.(0.&40.)R3.R4.)))R2.)))")
(* [comment removed for export] *).
Proof.
  intros ws i k H. split; [| split; [rewrite firstn_length; lia | rewrite firstn_length, skipn_length; lia]].
  rewrite <- (firstn_skipn i ws) at 1. f_equal. rewrite <- (firstn_skipn k (skipn i ws)) at 1. f_equal.
  rewrite skipn_skipn. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L14289632590.6L27904722566.5L39295676602.5L56075225580.6L67302804817.5L8320363852.6 00000=00H00U00b00o01<S2ws1i1H1k2HkS2ws1i1H2HkS2ws1i1H1k2HkS2ws1i1H1k2HkS2ws1i1H1k2HkS2ws1i1H1k2Hk". (* [comment removed for export] *)
Lemma window8 : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pws,(3.(0.&40.))Pi,$24.P,(2;.(37.R1.#8.)(1=.(0.&40.)R2.))(7.(3.(0.&40.))(39.(0.&40.)#8.(25.(0.&40.)R2.R3.))(?.(0.&40.)(3:.(0.&40.)R2.R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#1.)R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#2.)R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#3.)R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#4.)R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#5.)R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#6.)R3.$3;.)(?.(0.&40.)(3:.(0.&40.)(37.R2.#7.)R3.$3;.)(12.(0.&40.)))))))))))")
(* [comment removed for export] *).
Proof.
  intros ws i H.
  assert (G : forall k, (k < 8)%nat -> nth_error (firstn 8 (skipn i ws)) k = Some (nth (i + k) ws w0)).
  { intros k Hk. rewrite nth_error_firstn by lia. rewrite nth_error_skipn. replace (k <? 8)%nat with true by (symmetry; apply Nat.ltb_lt; lia). apply nth_error_nth'. lia. }
  apply nth_error_ext. intros k.
  destruct (Nat.lt_ge_cases k 8) as [Hk|Hk].
  - rewrite (G k Hk). do 8 (destruct k as [|k]; [cbn; f_equal; f_equal; lia|]). lia.
  - rewrite (proj2 (nth_error_None _ _)) by (rewrite firstn_length, skipn_length; lia).
    symmetry. apply nth_error_None. cbn. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma upd_app_r : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Ppre,(3.(0.&40.))Pl,(3.(0.&40.))Pk,$24.Pv,(0.&40.)(7.(3.(0.&40.))(19.(0.&40.)(38.(0.&40.)R4.R3.)(37.(1=.(0.&40.)R4.)R2.)R1.)(38.(0.&40.)R4.(19.(0.&40.)R3.R2.R1.)))")
(* [comment removed for export] *).
Proof. induction pre as [|x pre IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L11635878458.21L19053133377.21L25541784842.21L36695537066.21L45578415898.21L51436357370.21L53078823039.21L7772340330.21 00000<00E00Q00]00i01501A01MS3pre1i1H2H0S3pre1i1HS3pre1i1H2H0S3pre1i1H2H0S3pre1i1H2H0S3pre1i1H2H0S3pre1i1H2H0S3pre1i1H2H0". (* [comment removed for export] *)
Lemma upd8_window : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Ppre,(3.(0.&40.))Ppost,(3.(0.&40.))Px0,(0.&40.)Px1,(0.&40.)Px2,(0.&40.)Px3,(0.&40.)Px4,(0.&40.)Px5,(0.&40.)Px6,(0.&40.)Px7,(0.&40.)Pv0,(0.&40.)Pv1,(0.&40.)Pv2,(0.&40.)Pv3,(0.&40.)Pv4,(0.&40.)Pv5,(0.&40.)Pv6,(0.&40.)Pv7,(0.&40.)Pi,$2.P,(7.$2.(1<.(1=.(0.&40.)R13.))R1.)P,(;.=R2.)(7.(3.(0.&40.))(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(38.(0.&40.)R15.(38.(0.&40.)(?.(0.&40.)R13.(?.(0.&40.)R12.(?.(0.&40.)R11.(?.(0.&40.)R10.(?.(0.&40.)R?.(?.(0.&40.)R>.(?.(0.&40.)R=.(?.(0.&40.)R<.(12.(0.&40.))))))))))R14.))(9.R3.)R;.)(9.(=.R3.+1.))R:.)(9.(=.R3.+2.))R9.)(9.(=.R3.+3.))R8.)(9.(=.R3.+4.))R7.)(9.(=.R3.+5.))R6.)(9.(=.R3.+6.))R5.)(9.(=.R3.+7.))R4.)(38.(0.&40.)R15.(38.(0.&40.)(?.(0.&40.)R;.(?.(0.&40.)R:.(?.(0.&40.)R9.(?.(0.&40.)R8.(?.(0.&40.)R7.(?.(0.&40.)R6.(?.(0.&40.)R5.(?.(0.&40.)R4.(12.(0.&40.))))))))))R14.)))")
(* [comment removed for export] *).
Proof.
  intros. 
  replace (Z.to_nat i) with (length pre + 0)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 1)) with (length pre + 1)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 2)) with (length pre + 2)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 3)) with (length pre + 3)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 4)) with (length pre + 4)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 5)) with (length pre + 5)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 6)) with (length pre + 6)%nat by lia. rewrite upd_app_r. cbn [upd].
  replace (Z.to_nat (i + 7)) with (length pre + 7)%nat by lia. rewrite upd_app_r. cbn [upd]. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L40818989526.9L48167948719.9L64363405525.8000001004007SS1lS1l". (* [comment removed for export] *)
Lemma rw_cells_of_u32arr : forall m e l, u32arr asegs m e l -> rw_cells asegs m e (map C4 l).
Proof.
  intros m e l. revert e. induction l as [|x l IH]; intros e [HB HW].
  - split; [split; [cbn; tauto| exact HB]| exact HW].
  - apply (proj2 (rw_cells_app asegs m e [C4 x] (map C4 l))). cbn [cells_size csize Nat.add].
    cbn -[le4] in HB. apply bytes_at_app in HB as [HB1 HB2]. rewrite length_le4 in HB2.
    replace (4 * Z.of_nat (length (x :: l))) with (4 + 4 * Z.of_nat (length l)) in HW by (cbn [length]; lia).
    apply wr_at_app in HW; [|lia|lia]. destruct HW as [HW1 HW2].
    split. { split; [split; [cbn; tauto| cbn -[le4]; rewrite app_nil_r; exact HB1]| exact HW1]. }
    apply IH. split; [exact HB2| exact HW2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L40823181676.9L48172144917.9L64365502718.9000001004007SS1lS1l". (* [comment removed for export] *)
Lemma u32arr_of_rw_cells : forall m e l, rw_cells asegs m e (map C4 l) -> u32arr asegs m e l.
Proof.
  intros m e l. revert e. induction l as [|x l IH]; intros e H.
  - destruct H as [[_ HB] HW]. split; [exact HB| exact HW].
  - apply (proj1 (rw_cells_app asegs m e [C4 x] (map C4 l))) in H as [H1 H2]. cbn [cells_size csize Nat.add] in H2.
    apply IH in H2. destruct H1 as [[_ HB1] HW1]. cbn -[le4] in HB1. rewrite app_nil_r in HB1. destruct H2 as [HB2 HW2].
    split.
    + cbn -[le4]. apply bytes_at_app. split; [exact HB1|]. rewrite length_le4. exact HB2.
    + replace (4 * Z.of_nat (length (x :: l))) with (4 + 4 * Z.of_nat (length l)) by (cbn [length]; lia).
      apply wr_at_app; [lia|lia|]. split; [exact HW1| exact HW2].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma ro_cells_of_u32s : forall m e l, bytes_at asegs m e (u32s l) -> ro_cells asegs m e (map C4 l).
Proof.
  intros m e l. revert e. induction l as [|x l IH]; intros e HB.
  - split; [cbn; tauto| exact HB].
  - cbn -[le4] in HB. apply bytes_at_app in HB as [HB1 HB2]. rewrite length_le4 in HB2.
    split. { cbn. split; [tauto|]. clear - HB2 IH. apply IH in HB2. exact (proj1 HB2). }
    cbn -[le4]. apply bytes_at_app. split; [exact HB1|]. rewrite length_le4. apply IH in HB2. exact (proj2 HB2).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L14336479410.10L23359810914.10L28361997314.10L3306533522.10 L33584923811.10L45800023267.10L54137089394.10L68152117442.1000000B00T00f01801L01^02002BS2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2S1A2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2". (* [comment removed for export] *)
Lemma u32rw_cells8 : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pe,$2.P,(13.$5.R5.R4.R3.)P,(;.=R3.)P,(2;.(37.(9.R4.)#8.)(1=.(0.&40.)R5.))P,(7.$2.R4.(=.R7.(>.+4.R5.)))(14.$5.R9.R5.(?.$10.(11.(3:.(0.&40.)(9.R6.)R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+1.))R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+2.))R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+3.))R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+4.))R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+5.))R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+6.))R7.$3;.))(?.$10.(11.(3:.(0.&40.)(9.(=.R6.+7.))R7.$3;.))(12.$10.))))))))))")
(* [comment removed for export] *).
Proof.
  intros m A ws i e HX Hi HL ->.
  destruct (window_split ws (Z.to_nat i) 8 HL) as (E & L1 & L2). rewrite (window8 ws (Z.to_nat i) HL) in E.
  rewrite E in HX. apply u32arr_app in HX as [_ HX]. apply u32arr_app in HX as [HX _]. rewrite L1 in HX.
  replace (A + 4 * Z.of_nat (Z.to_nat i)) with (A + 4 * i) in HX by lia.
  replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia. replace (Z.to_nat (i + 2)) with (Z.to_nat i + 2)%nat by lia.
  replace (Z.to_nat (i + 3)) with (Z.to_nat i + 3)%nat by lia. replace (Z.to_nat (i + 4)) with (Z.to_nat i + 4)%nat by lia.
  replace (Z.to_nat (i + 5)) with (Z.to_nat i + 5)%nat by lia. replace (Z.to_nat (i + 6)) with (Z.to_nat i + 6)%nat by lia.
  replace (Z.to_nat (i + 7)) with (Z.to_nat i + 7)%nat by lia.
  exact (rw_cells_of_u32arr _ _ _ HX).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L39170545813.700000<S2ws1q2Hq2HL". (* [comment removed for export] *)
Lemma u32ro_cellq : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pq,$2.Pe,$2.P,(4.$5.R5.R4.(6.R3.))P,(;.=R3.)P,(27.(9.R4.)(1=.(0.&40.)R5.))P,(7.$2.R4.(=.R7.(>.+4.R5.)))(<.$5.R9.R5.(?.$10.(11.(3:.(0.&40.)(9.R6.)R7.$3;.))(12.$10.)))")
(* [comment removed for export] *).
Proof.
  intros m A ws q e HB Hq HL ->. apply (u32ro_cell m A ws q); [exact HB| |lia]. apply nth_error_nth'. exact HL.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L10351672563.22L11805581219.24L33584923811.24L44279931082.24L68489826095.2200000B00S00g01;01MS2ws1i2Hi2HL2L12L2S1A2ws1i2HL2L12L2S1A2ws1i2Hi2HL2L12L2S1A2ws1i2Hi2HL2L12L2S2ws1i2Hi2HL2L12L2". (* [comment removed for export] *)
Lemma u32arr_upd8_of_cells : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))Pi,$2.Pe,$2.Pf,$2.Pv0,(0.&40.)Pv1,(0.&40.)Pv2,(0.&40.)Pv3,(0.&40.)Pv4,(0.&40.)Pv5,(0.&40.)Pv6,(0.&40.)Pv7,(0.&40.)P,(13.$5.R?.R=.R<.)P,(;.=R<.)P,(2;.(37.(9.R=.)#8.)(1=.(0.&40.)R>.))P,(7.$2.R=.(=.R10.(>.+4.R>.)))P,(15.(?.(16.$2.$2.)(17.$2.$2.R>.R=.)(12.(16.$2.$2.)))R13.R12.)P,(7.$2.R>.(=.R?.+20.))P,(18.$5.R15.R14.)P,(14.$5.R15.R11.(?.$10.(11.R?.)(?.$10.(11.R>.)(?.$10.(11.R=.)(?.$10.(11.R<.)(?.$10.(11.R;.)(?.$10.(11.R:.)(?.$10.(11.R9.)(?.$10.(11.R8.)(12.$10.))))))))))(13.$5.R16.R15.(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)R14.(9.R13.)R10.)(9.(=.R13.+1.))R?.)(9.(=.R13.+2.))R>.)(9.(=.R13.+3.))R=.)(9.(=.R13.+4.))R<.)(9.(=.R13.+5.))R;.)(9.(=.R13.+6.))R:.)(9.(=.R13.+7.))R9.))")
(* [comment removed for export] *).
Proof.
  intros m m' A ws i e f v0 v1 v2 v3 v4 v5 v6 v7 HX Hi HL -> MU -> WM HC.
  destruct (window_split ws (Z.to_nat i) 8 HL) as (E & L1 & L2). rewrite (window8 ws (Z.to_nat i) HL) in E.
  rewrite E at 1. rewrite (upd8_window _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i) by lia.
  rewrite E in HX. apply u32arr_app in HX as [HX1 HX]. apply u32arr_app in HX as [HX2 HX3]. rewrite L1 in HX2, HX3.
  apply u32arr_app. split.
  { eapply u32arr_transport; [exact HX1| exact MU| exact WM|]. cbn [disjoint_from]. rewrite L1. lia. }
  rewrite L1. apply u32arr_app. split.
  { replace (A + 4 * Z.of_nat (Z.to_nat i)) with (A + 4 * i) by lia. exact (u32arr_of_rw_cells m' (A + 4 * i) [v0; v1; v2; v3; v4; v5; v6; v7] HC). }
  eapply u32arr_transport; [exact HX3| exact MU| exact WM|]. cbn [disjoint_from length]. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma limb32_of_nth : forall (l : list word) (q : nat) (d : word), d = nth q l w0 -> limb32 l q = w32 d.
Proof. intros l q d ->. reflexivity. Qed.
Lemma limb32_same_from_nth : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.Pq,$24.Pd,(0.&40.)P,(1>.(0.&40.)(9.R3.)R5.R4.)P,(2;.(9.R4.)R3.)P,(27.R4.(1=.(0.&40.)R7.))P,(7.$24.(1=.(0.&40.)R8.)(1=.(0.&40.)R7.))P,(7.(0.&40.)R5.(3:.(0.&40.)R6.R9.$3;.))(7.$2.(28.R9.R7.)(29.R6.))")
(* [comment removed for export] *).
Proof.
  intros l l0 i q d FS Hq HL EL ->. apply limb32_nth_error. rewrite <- (FS q Hq). apply nth_error_nth'. exact HL.
Qed.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L10358312663.12L35884662729.1200000<00ES2ds1i2Hi2HLS2ds1i2HL". (* [comment removed for export] *)
Lemma vi_mul_stepZ : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pds,(3.(0.&40.))Pds0,(3.(0.&40.))Pss,(3.(0.&40.))Pi,$2.Pi',$2.Pb,$2.Pc,$2.Pc',$2.Pwv,(0.&40.)P,(;.=R6.)P,(27.(9.R7.)(1=.(0.&40.)R:.))P,(7.$2.R7.(=.R8.+1.))P,(7.$2.(=.(3<.R<.R9.)(>.(2:.+2.(>.+20.R9.))R6.))(=.(3<.R;.R9.)(>.(3<.R:.R9.)R7.)))P,(7.$2.(=.(29.R5.)(>.(2:.+2.+20.)R6.))(=.(=.(28.R<.(9.R:.))(>.(28.R;.(9.R:.))R8.))R7.))(7.$2.(=.(3<.(19.(0.&40.)R>.(9.R;.)R6.)R:.)(>.(2:.+2.(>.+20.R:.))R7.))(=.(3<.R=.R:.)(>.(3<.R<.R:.)R9.)))")
(* [comment removed for export] *).
Proof.
  intros ds ds0 ss i i' b c c' wv Hi HL -> VI V. rewrite !lval_succ, pow2_32_succ by lia.
  rewrite lval_upd_ge by lia. rewrite limb32_upd_same by exact HL. set (M := 2 ^ (32 * i)) in *. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L23743590735.23L32257526874.13L39904272949.13L43172971163.1600000S00]01401OS1D1S2ld2ls2ds3ds02ss3DIS1e1f2He2HfS1D2ds3ds0S2ld2ls2ds3ds02LX2L02LSS2ld1i2ds3ds02LX2L01q2Hq2HL". (* [comment removed for export] *)
Lemma lx_sview : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pm,P,(0.&40.)(1.(0.&8.))PD,$2.PS,$2.Pld,$2.Pls,$2.Pi,$2.Pds,(3.(0.&40.))Pds0,(3.(0.&40.))Pss,(3.(0.&40.))P,(13.$5.R9.R8.R3.)P,(7.$2.(1<.(1=.(0.&40.)R4.))R7.)P,(7.$2.(1<.(1=.(0.&40.)R4.))R8.)P,(1>.(0.&40.)(9.R7.)R6.R5.)P,(7.$2.(1<.(1=.(0.&40.)R5.))R9.)P,(;.=R9.)P,(1:.(1;.(7.$2.R=.R>.)(7.(3.(0.&40.))R7.R8.))(1;.(4.$5.R?.R=.(6.R7.))(1:.(;.(=.R=.(>.+4.R;.))R>.)(;.(=.R>.(>.+4.R<.))R=.))))(20.(3.(0.&40.))Lsv,(3.(0.&40.))(1;.(4.$5.R11.R?.(6.R1.))(1;.(7.$2.(1<.(1=.(0.&40.)R1.))R=.)(1;.(1:.(7.$2.(34.R?.R10.)=)(1:.(;.(=.R?.(>.+4.R=.))R10.)(;.(=.R10.(>.+4.R>.))R?.)))(1;.Pq,$24.Pv,(0.&40.)P,(2;.(9.R>.)R2.)P,(27.R3.(1=.(0.&40.)R4.))P,(7.(0.&40.)R3.(3:.(0.&40.)R4.R5.$3;.))(7.$2.(28.R>.R5.)(29.R4.))Pm',P,(0.&40.)(1.(0.&8.))Pe,$2.Pf,$2.P,(15.(?.(16.$2.$2.)(17.$2.$2.R2.R1.)(12.(16.$2.$2.)))R14.R3.)P,(;.R14.R3.)P,(;.R3.(=.R15.(>.+4.R13.)))(1:.(1;.(7.$2.R15.R16.)(7.(3.(0.&40.))R?.R10.))(1;.(4.$5.R6.R15.(6.R?.))(1:.(;.(=.R15.(>.+4.R13.))R16.)(;.(=.R16.(>.+4.R14.))R15.)))))))))")
(* [comment removed for export] *).
Proof.
  intros m D S ld ls i ds ds0 ss HX LX L0 FS LS Hi [[ES ESS]|[HS DIS]].
  - exists ds. subst S ss. split; [exact (u32arr_ro _ _ _ _ HX)|]. split; [lia|]. split; [left; lia|]. split.
    + intros q v Hq HL ->. eapply limb32_same_from_nth; [exact FS| exact Hq| exact HL| lia| reflexivity].
    + intros m' e f MU He Hf. left. split; reflexivity.
  - exists ss. split; [exact HS|]. split; [exact LS|]. split; [right; exact DIS|]. split.
    + intros q v Hq HL ->. reflexivity.
    + intros m' e f MU He Hf. right. split; [|exact DIS].
      eapply bytes_at_transport; [exact HS| exact MU|]. cbn [disjoint_from]. rewrite u32s_length, Nat2Z.inj_mul, LS. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma same_from_upd_Zn : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.Pi',$2.Pv,(0.&40.)P,(1>.(0.&40.)(9.R3.)R5.R4.)P,(;.=R4.)P,(7.$2.R4.(=.R5.+1.))(1>.(0.&40.)(9.R5.)(19.(0.&40.)R8.(9.R6.)R4.)R7.)")
(* [comment removed for export] *).
Proof. intros l l0 i i' v H Hi ->. apply same_from_upd_Z; assumption. Qed.
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L10297692440.13L10351595562.13L13796376801.13L14126101967.13L143988120.13  L14603583128.13L17598865025.13L31298195921.13L3889301425.13 L41154444440.13L41250020593.13L43082429464.13L54968227777.13L61025170328.13L68676218385.13L8514513944.13 00000300900?00B00E00H00N00T00Z00]00c00f00l00o015018S1iS1i2HiS1i2HiS1iS1iS1iS1i2HiS1i2HiS1i2HiS1iS1i2HiS1iS1i2HiS1iS1i2HiS1i". (* [comment removed for export] *)
Lemma same_from_upd8_Z : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pl,(3.(0.&40.))Pl0,(3.(0.&40.))Pi,$2.Pi',$2.Pv0,(0.&40.)Pv1,(0.&40.)Pv2,(0.&40.)Pv3,(0.&40.)Pv4,(0.&40.)Pv5,(0.&40.)Pv6,(0.&40.)Pv7,(0.&40.)P,(1>.(0.&40.)(9.R:.)R<.R;.)P,(;.=R;.)P,(7.$2.R;.(=.R<.+8.))(1>.(0.&40.)(9.R<.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)(19.(0.&40.)R?.(9.R=.)R;.)(9.(=.R=.+1.))R:.)(9.(=.R=.+2.))R9.)(9.(=.R=.+3.))R8.)(9.(=.R=.+4.))R7.)(9.(=.R=.+5.))R6.)(9.(=.R=.+6.))R5.)(9.(=.R=.+7.))R4.)R>.)")
(* [comment removed for export] *).
Proof.
  intros l l0 i i' v0 v1 v2 v3 v4 v5 v6 v7 H Hi ->.
  do 8 (eapply same_from_upd_Zn; [|lia|lia]). exact H.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L38234029620.400000:S2cu2H12H2". (* [comment removed for export] *)
Lemma lx_wc_sxz : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pcu,$2.Pc,$2.P,(;.=R2.)P,(;.=(=.(33.R3.)+????????????????.))P,(7.$2.R4.(3=.R3.))(7.$2.(31.&40.(32.&40.R5.))(3=.R4.))")
(* [comment removed for export] *).
Proof. intros cu c H1 H2 <-. rewrite Z_to_bv_unsigned. apply Z.mod_small. change (bv_modulus 64) with (2^64). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L38717976173.2L44021620876.2000001002SS". (* [comment removed for export] *)
Lemma lx_shl32_shr32 : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Px,(0.&40.)Pb,$2.P,(7.$2.(3>.(31.&40.R2.)(2:.+2.+20.))R1.)(7.$2.(3?.(31.&40.(32.&40.(>.+100000000.(31.&40.R3.))))+20.)R2.)")
(* [comment removed for export] *).
Proof.
  intros x b <-. rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?y) with (y mod 2 ^ 64).
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32). change 4294967296 with (2 ^ 32).
  rewrite Zmult_mod_distr_l. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma lx_shl32_shr32' : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Px,(0.&40.)Pb,$2.P,(7.$2.(3>.(31.&40.R2.)(2:.+2.+20.))R1.)(7.$2.(3?.(2?.+40.(>.+100000000.(31.&40.R3.)))+20.)R2.)")
(* [comment removed for export] *).
Proof. intros x b H. rewrite <- (lx_shl32_shr32 x b H). rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L18169509958.2L6809272997.2 000003006S1uS1u". (* [comment removed for export] *)
Lemma lx_sxz_cases : forall u, 0 <= u < 2 ^ 32 -> sxz u = (if u <? 2 ^ 31 then u else u + 2 ^ 64 - 2 ^ 32).
Proof. intros u Hu. unfold sxz. destruct (u <? 2^31); lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00d0?L11668999122.14L13352413740.15L13570944143.20L16039674720.11L16046136858.12L16046136858.9 L16112276359.12L1954282746.16 L21907924320.11L21907924320.30L24693889556.12L26762292908.12L2678148058.20 L27163916913.9 L27838810017.12L28128672723.12L29520387478.23L29791468393.11L30651097297.15L34390941521.38L34856683152.15L35212933531.16L36583247008.15L38715569562.20L38715780975.14L38715831579.27L38715883021.11L38717875063.12L38717875063.9 L42176330691.12L42468484398.8 L42470583725.21L42470583979.28L42470763820.9 L42470797781.16L42470798813.15L44015165838.14L44470805792.12L45041832306.27L46315022998.12L47485454992.27L48125773281.22L51677037936.9 L52837948142.27L5338738889.15 L56073741190.11L60095764749.12L60671370590.27L62556998108.15L64530367457.39L64672898326.25L7575817642.9  00000B00b01901T02202I02b03403O03m04A04W04n05=05Q05e06A06Y07407d08?08Q08l09A09P09i0:A0:W0:d0;=0;>0;U0;n0<20<A0<P0<_0=30=L0=j0>C0?90?H0?a0@<0@T0@j0@k0AK0B40BP0BgS2ws2wd1b1s1d1P2HPS2ws2wd1b1c1s1d1P2lo1t1r1H2H02H1S2ws2wd1b1c1s1d1P2lo2hiS2ws2wd1b1c1s1d1P2lo1t1r2RrS2ws2wd1b1c1s1d2Rd1P2lo1t2Rt1HS2ws1b1c2Hc1s1P2lo2PL1HS2ws1b1c1s1P2lo1t1H2H02H1S2ws2wd1b1s1d1P2HPS2ws2wd1b1c1s1d1P2lo1t1r2RrS2ws2wd1b1c1s1d1P2lo2hi1t1r2RrS2ws1b1c1s1P2lo1t2H1S2ws2wd1b1c1s1d1P2lo1tS2ws2wd1b1c1s1d1P2lo2hiS2ws1b1c1s1P2loS2ws1b1c1s1P2lo1t2H1S2ws1b1c1s1P2lo1t2H1S2ws2wd1b1c1s1d1P2lo2hi1t2RtS2ws2wd1b1c1s1d1P2lo1t1rS2ws2wd1b1c1s1d1P2lo1t1r2H1S2ws2wd1b1c2cu1s1d2HP2lo2hi1t2Rt1r2Rr2E12E21E2VES2ws2wd1b1c1s1d1P2lo1t1r2H1S2ws2wd1b1s1d1P2HPS2ws2wd1b1c1s1d1P2lo1t1r2H1S2ws2wd1b1s1d1P2lo2hiS2ws2wd1b1s1d1PS2ws2wd1b1c1s1d1P2lo2hi1tS2ws2wd1b1c1s1d1P2lo1t1rS2ws2wd1b1c1s1d1P2lo1tS2ws1b1s1P2loS2ws1b1c1s1P2lo1t1H2H02H1SS2ws2wd1b1c1s1d1P2lo2hiS2ws2wd1b1c1s1d1P2lo2hi1tS2wsS2ws2wd1b1s1d1PS2ws2wd1b1s1d1PS2ws2wd1b1s1d1PS2ws1b1c1s1P2lo1t2H1S2ws2wd1b1c1s1d1P2lo2hi1tS2ws2wd1b1c1s1d2Rd1P2lo1t2Rt1HS2ws2wd1b1c1s1d1P2lo2hi1tS2wd1c1d2Rd2lo2hi2PL2PH1t1r3Ett3Err1H2H02Hc1P2HP2PD2RrS2ws1b1c1s1P2loS2ws2wd1b1c1s1d1P2lo2hi1tS2ws2wd1b1c1s1d1P2lo1t1r2H1S2ws2wd1b1c1s1d1P2lo1t1rS2ws2wd1b1c1s1d1P2lo1tFS2ws2wd1b1c1s1d1P2lo1t1r1H2H02H1S2ws2wd1b1c2cu1s1d1P2lo2hi1t1r2E12E21E2RES2ws2wd1b1c1s1d2Rd1P2lo2hi1tS2ws1b1c2Hc1s1P2lo2PL1H". (* [comment removed for export] *)
Lemma lx_mla_step : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pws,(0.&40.)Pwd,(0.&40.)Pb,$2.Pc,$2.Pcu,$2.Pcu',$2.P,(1;.(;.=R4.)(1?.R4.(2:.+2.+20.)))P,(1;.(;.=R4.)(1?.R4.(2:.+2.+20.)))P,(7.$2.R4.(3=.R5.))P,(7.$2.R4.(2?.+40.(30.+20.(2?.+20.(=.(3?.(2?.+40.(>.(2?.+20.(31.&40.R9.))R7.))+20.)(=.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R5.(>.(2?.+20.(31.&40.R9.))R7.)))))R5.))(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.(30.+20.(2?.+20.(31.&40.R8.)))(30.+20.(2?.+20.(=.R5.(>.(2?.+20.(31.&40.R9.))R7.))))))))(2?.+40.(30.+20.(2?.+20.(=.R5.(>.(2?.+20.(31.&40.R9.))R7.)))))))))))))(20.$2.Lc',$2.(1;.(7.$2.R6.(3=.R1.))(1;.(1;.(;.=R1.)(1?.R1.(2:.+2.+20.)))(7.$2.(=.(29.(32.&40.(30.+20.(2?.+20.(=.(30.+20.(2?.+20.(31.&40.R:.)))(30.+20.(2?.+20.(=.R7.(>.(2?.+20.(31.&40.R;.))R9.)))))))))(>.(2:.+2.+20.)R1.))(=.(=.(29.R:.)(>.(29.R;.)R9.))R8.)))))")
(* [comment removed for export] *).
Proof.
  intros ws wd b c cu cu' Hb Hc Ecu ->.
  pose proof (Z.mod_pos_bound (bv_unsigned ws) (2^32) ltac:(lia)) as Rs.
  pose proof (Z.mod_pos_bound (bv_unsigned wd) (2^32) ltac:(lia)) as Rd.
  unfold w32. change (zlow 32 (bv_unsigned ws)) with (bv_unsigned ws mod 2^32). change (zlow 32 (bv_unsigned wd)) with (bv_unsigned wd mod 2^32).
  set (s := bv_unsigned ws mod 2^32) in *. set (d := bv_unsigned wd mod 2^32) in *.
  assert (HP : 0 <= s * b <= (2^32 - 1) * (2^32 - 1)) by nia.
  set (P := s * b) in *.
  replace (zlow 64 P) with P by (unfold zlow; symmetry; apply Z.mod_small; lia).
  rewrite (Z.shiftr_div_pow2 P 32) by lia.
  pose proof (Z.div_mod P (2^32) ltac:(lia)) as PD. pose proof (Z.mod_pos_bound P (2^32) ltac:(lia)) as PL.
  assert (PH : 0 <= P / 2^32 < 2^32 - 1) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  set (lo := P mod 2^32) in *. set (hi := P / 2^32) in *.
  (* [comment removed for export] *)
  pose proof (lx_sxz_cases c Hc) as Ec. rewrite <- Ecu in Ec.
  assert (Et : zlow 32 (cu + P) = (c + lo) mod 2^32).
  { unfold zlow. rewrite Ec, PD. destruct (c <? 2^31).
    - replace (c + (2^32 * hi + lo)) with (c + lo + hi * 2^32) by lia. apply Z.mod_add. lia.
    - replace (c + 2^64 - 2^32 + (2^32 * hi + lo)) with (c + lo + (hi + 2^32 - 1) * 2^32) by lia. apply Z.mod_add. lia. }
  rewrite !Et. pose proof (Z.mod_pos_bound (c + lo) (2^32) ltac:(lia)) as Rt. set (t := (c + lo) mod 2^32) in *.
  destruct (lx_s32_cases t ltac:(lia)) as [Etz Ut]. rewrite !Ut.
  destruct (lx_s32_cases d ltac:(lia)) as [Ed Ud].
  assert (Er : zlow 32 (zswrap 32 d + zswrap 32 t) = (d + t) mod 2^32).
  { unfold zlow. rewrite Ed, Etz. destruct (d <? 2^31); destruct (t <? 2^31);
    first [reflexivity | rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia | rewrite <- (Z.mod_add _ 2) by lia; f_equal; lia]. }
  rewrite !Er. pose proof (Z.mod_pos_bound (d + t) (2^32) ltac:(lia)) as Rr. set (r := (d + t) mod 2^32) in *.
  destruct (lx_s32_cases r ltac:(lia)) as [Erz Ur]. rewrite !Ur.
  assert (E1 : (if t <? 2^31 then t else t + 2^64 - 2^32) <? cu = (t <? c)).
  { rewrite Ec. clear - Rt Hc. destruct (Z.ltb_spec t (2^31)); destruct (Z.ltb_spec c (2^31)); destruct (Z.ltb_spec t c);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  assert (E2 : (if r <? 2^31 then r else r + 2^64 - 2^32) <? (if t <? 2^31 then t else t + 2^64 - 2^32) = (r <? t)).
  { clear - Rt Rr. destruct (Z.ltb_spec r (2^31)); destruct (Z.ltb_spec t (2^31)); destruct (Z.ltb_spec r t);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite E1, E2.
  set (E := hi + (Z.b2z (t <? c) + Z.b2z (r <? t))).
  assert (Ett : t = c + lo - (if c + lo <? 2^32 then 0 else 2^32)).
  { subst t. clear - Hc PL. destruct (Z.ltb_spec (c + lo) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (Err : r = d + t - (if d + t <? 2^32 then 0 else 2^32)).
  { subst r. clear - Rd Rt. destruct (Z.ltb_spec (d + t) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  assert (HE : 0 <= E < 2^32 /\ r + 2^32 * E = d + P + c).
  { subst E. rewrite PD. clearbody t r lo hi P. clear - Hc PL PH HP PD Rd Rt Rr Ett Err.
    destruct (Z.ltb_spec t c); destruct (Z.ltb_spec r t); destruct (Z.ltb_spec (c + lo) (2^32)); destruct (Z.ltb_spec (d + t) (2^32)); cbn [Z.b2z]; lia. }
  destruct HE as [RE VE].
  exists E. split; [|split; [exact RE|]].
  - unfold zlow at 2. rewrite (Z.mod_small E) by lia. rewrite (lx_sxz_cases E RE).
    destruct (lx_s32_cases E ltac:(lia)) as [_ UE]. exact UE.
  - rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 r)) with (zlow 64 (zswrap 32 r)). rewrite Ur.
    replace ((if r <? 2 ^ 31 then r else r + 2 ^ 64 - 2 ^ 32) mod 2 ^ 32) with r.
    2:{ clear - Rr. destruct (r <? 2^31). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
    subst P. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00N0?L10068899536.17L16039674720.5 L16046136858.6 L16311143842.10L21064770997.10L21907924320.13L21907924320.5 L27861319474.6 L29791468393.5 L35590769241.9 L37310274793.10L38715831579.10L38715883021.5 L38717875063.6 L41664887351.10L42468484398.5 L42470583979.11L47329018049.9 L49941526656.9 L510600819.6   L51740710156.9 L56073741190.5 L59631072368.17L59657562780.9 L6032584876.9  L63079067608.6 L64672634247.8 L66633361952.9 L6801021315.10 L7753286896.9  00000:00G00W00_00g01401A01Q01[01h02002602@02F02G02H02P02]02m03503E03O03Y03k04=04E04N04[04\04iS2wd1c1d1rS2wd1c1d1r2RrS2wd1c2Hc1d2Rd1HS2wd1c1dS2wd1c1dS2wd1c1d1r2RrS2wd1c1d1r2RrS2wd1c2Hc1d2Rd1HS2wd1c1d1rS2wd1c1d1r2H1S2wd1c1dS2wd1dS2wd1c1d1rS2wd1dFSS2wd1c1dS2wd1c1d1r2H1S1c1d1r3Err2Hc1HS2wd1c1dS1c2Hc1d1r3Err1HS2wd1c1d1rS2wd1c1d1rS2wd1c1d1r1H2H02H1S2wd1c1d1r1H2H02H1S2wd1c1dS2wd1d2RdS2wd1c1d1r2H1FS2wd1c1d1r2H1". (* [comment removed for export] *)
Lemma lx_exc_step : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pwd,(0.&40.)Pc,$2.Pcu,$2.P,(1;.(;.=R2.)(1?.R2.(2:.+2.+20.)))P,(7.$2.R2.(3=.R3.))(1;.(1;.(;.=(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R5.)))))))(1?.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R5.))))))(2:.+2.+20.)))(1;.(7.$2.(=.(29.(32.&40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.))))))))(>.(2:.+2.+20.)(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R5.))))))))(=.(29.R5.)R4.))(7.$2.(31.&40.(32.&40.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R5.))))))))(3=.(2=.(2>.(2?.+40.(30.+20.(2?.+20.(=.R3.(30.+20.(2?.+20.(31.&40.R5.)))))))(2?.+40.(30.+20.(2?.+20.(31.&40.R5.))))))))))")
(* [comment removed for export] *).
Proof.
  intros wd c cu Hc Ecu.
  pose proof (Z.mod_pos_bound (bv_unsigned wd) (2^32) ltac:(lia)) as Rd.
  unfold w32. change (zlow 32 (bv_unsigned wd)) with (bv_unsigned wd mod 2^32).
  set (d := bv_unsigned wd mod 2^32) in *.
  pose proof (lx_sxz_cases c Hc) as Ec. rewrite <- Ecu in Ec.
  destruct (lx_s32_cases d ltac:(lia)) as [Ed Ud]. rewrite !Ud.
  assert (Er : zlow 32 (cu + zswrap 32 d) = (c + d) mod 2^32).
  { unfold zlow. rewrite Ec, Ed. destruct (c <? 2^31); destruct (d <? 2^31);
    first [reflexivity | rewrite <- (Z.mod_add _ 1) by lia; f_equal; lia | rewrite <- (Z.mod_add _ (1 - 2^32)) by lia; f_equal; lia
          | rewrite <- (Z.mod_add _ (2 - 2^32)) by lia; f_equal; lia]. }
  rewrite !Er. pose proof (Z.mod_pos_bound (c + d) (2^32) ltac:(lia)) as Rr. set (r := (c + d) mod 2^32) in *.
  destruct (lx_s32_cases r ltac:(lia)) as [Erz Ur]. rewrite !Ur.
  assert (E1 : (if r <? 2^31 then r else r + 2^64 - 2^32) <? (if d <? 2^31 then d else d + 2^64 - 2^32) = (r <? d)).
  { clear - Rr Rd. destruct (Z.ltb_spec r (2^31)); destruct (Z.ltb_spec d (2^31)); destruct (Z.ltb_spec r d);
    first [reflexivity | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia]. }
  rewrite !E1.
  assert (Err : r = c + d - (if c + d <? 2^32 then 0 else 2^32)).
  { subst r. clear - Hc Rd. destruct (Z.ltb_spec (c + d) (2^32)). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small; lia. }
  split; [destruct (r <? d); cbn; lia|]. split.
  - rewrite Z_to_bv_unsigned. change (bv_wrap 64 (zswrap 32 r)) with (zlow 64 (zswrap 32 r)). rewrite Ur.
    replace ((if r <? 2 ^ 31 then r else r + 2 ^ 64 - 2 ^ 32) mod 2 ^ 32) with r.
    2:{ clear - Rr. destruct (r <? 2^31). rewrite Z.mod_small; lia. rewrite <- (Z.mod_add _ (1 - 2^32)) by lia. rewrite Z.mod_small; lia. }
    clearbody r d. clear - Hc Rd Rr Err. destruct (Z.ltb_spec r d); destruct (Z.ltb_spec (c + d) (2^32)); cbn [Z.b2z]; lia.
  - rewrite Z_to_bv_unsigned. unfold sxz. destruct (r <? d); reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lx_sx32 : forall w : word, Z_to_bv 64 (zswrap 32 (zlow 32 (bv_unsigned w))) = sx32 w.
Proof.
  intros w. unfold sx32. f_equal. unfold zswrap, zlow, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (2 ^ (32 - 1)) with (2 ^ 31).
  f_equal. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L1185030438.4 L14698736771.4L16046136858.4L38717875063.4L42465045280.1L62544261284.400000500:00C00H00I00RS1w1uS1w1uS1w1u1R1HS1w1uSS1w1u1R1H". (* [comment removed for export] *)
Lemma lx_w32_eq : forall w : word, zlow 32 (zswrap 32 (zlow 32 (bv_unsigned w))) = w32 w.
Proof.
  intros w. unfold zlow, zswrap, w32. change (2 ^ (32 - 1)) with (2 ^ 31).
  pose proof (Z.mod_pos_bound (bv_unsigned w) (2 ^ 32) ltac:(lia)) as R.
  set (u := bv_unsigned w mod 2 ^ 32) in *.
  destruct (Z.lt_ge_cases u (2 ^ 31)).
  - rewrite (Z.mod_small (u + 2 ^ 31)) by lia. rewrite Z.mod_small; lia.
  - rewrite <- (Z.mod_add (u + 2 ^ 31) (-1)) by lia. rewrite (Z.mod_small (_ + _ * _)) by lia.
    rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L42465045280.1000001S". (* [comment removed for export] *)
Lemma lx_wrap_sx32 : forall w : word, bv_wrap 32 (bv_unsigned (sx32 w)) = w32 w.
Proof.
  intros w. rewrite <- lx_sx32, <- lx_w32_eq. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
  unfold zlow at 1. apply Zaux.Zmod_mod_mult; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L12506770270.9L16045985927.9L20943653621.7L38881069424.8L41422034663.8L43326770808.8L44133177712.8L45831143172.800000800@00G00N00R00Z00^00eS1w2sa1SS1w2sa1SS2sa2HvS2sa2HvS2saS1w2sa1WS2saS2sa2Hv". (* [comment removed for export] *)
Lemma lx_shr_limb_bits : ltac2:(CDefT.buildp (gd_tbl_LxAMpiTac ()) "Pw,(0.&40.)Pr0w,(0.&40.)Psa,$2.PC,$2.P,(1;.(1?.=R2.)(1?.R2.+20.))P,(1;.(;.=R2.)(1?.R2.(2:.+2.R3.)))P,(7.$2.(29.R5.)(>.R3.(2:.+2.(34.+20.R4.))))(7.$2.(29.(32.&40.(40.(30.+20.(3?.(2?.+20.(30.+20.(2?.+20.(31.&40.R7.))))R5.))(31.&40.R6.))))(=.(41.(29.R7.)(2:.+2.R5.))(>.R4.(2:.+2.(34.+20.R5.)))))")
(* [comment removed for export] *).
Proof.
  intros w r0w sa C Hv HC HR.
  rewrite <- (shr_limb_bits w r0w sa C Hv HC HR). do 3 f_equal.
  rewrite (Z.mod_small sa 32) by lia. rewrite lx_w32_eq, lx_wrap_sx32.
  pose proof (w32_range w) as W.
  assert (S : 0 <= w32 w ≫ sa < 2 ^ 31).
  { rewrite Z.shiftr_div_pow2 by lia. split. apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia].
    apply Z.div_lt_upper_bound. apply Z.pow_pos_nonneg; lia.
    eapply Z.lt_le_trans; [apply (proj2 W)|]. change (2 ^ 32) with (2 * 2 ^ 31).
    apply Z.mul_le_mono_nonneg_r; [lia|]. change 2 with (2 ^ 1) at 1. apply Z.pow_le_mono_r; lia. }
  unfold zswrap, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite (Z.mod_small (_ + 2 ^ 31) (2 ^ 32)) by lia. symmetry. apply Z.mod_small. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
