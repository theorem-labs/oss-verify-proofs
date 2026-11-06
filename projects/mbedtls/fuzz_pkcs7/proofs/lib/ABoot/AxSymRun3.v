(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2S.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AxSymRun3 () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "stdpp.bitvector.definitions.bv"; "env_agree"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "sr_vars_lt"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.regs_ok"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sentry"; "log_vars_lt"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.mem_denot"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.log_flat"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.kentry"; "kn_vars_lt"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.Env"; "vals_ev"; "Corelib.Init.Datatypes.app"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.st_ok"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SSR"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.saddr"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "asanreflect_fx"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.scripts"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sym_state"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sidecond"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sym_exec"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.scs_denot"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_regs"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_log"; "OSSVerify.KrLib.ABoot.CatSim.msteps"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_pc"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.eagree"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.itab"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.itab_sound"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sym_execTX"; "Corelib.Init.Peano.le"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_next"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.s_know"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.carry"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.edenot"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.sr_upd"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ridx"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ELit"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.EVar"; "sr_init"; "LinuxProcessSemantics.Riscv.Prelude.bvmap_empty"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "stk_ok"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.kentry_ok"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KWr"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SA"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KWord"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KRange"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KAlign"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KImg"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KZero"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.eb"; "Corelib.Lists.ListDef.nth"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KBlob"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ext_val"; "LinuxProcessSemantics.Riscv.Sem.branch_taken"; "LinuxProcessSemantics.Riscv.Instr.BC_EQ"; "Stdlib.ZArith.BinInt.Z.eqb"; "LinuxProcessSemantics.Riscv.Instr.BC_NE"; "Corelib.Init.Datatypes.negb"; "LinuxProcessSemantics.Riscv.Instr.BC_LTU"; "Stdlib.ZArith.BinInt.Z.ltb"; "LinuxProcessSemantics.Riscv.Instr.BC_GEU"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vals_ev (vals : list word) : nat -> word :=
  fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
  match K with
  | KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
  | KZero a n => saddr_vars_lt b a && expr_vars_lt b n
  | KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KImg _ _ => true
  | KAlign e _ => expr_vars_lt b e
  | KRange e _ _ => expr_vars_lt b e
  | KWr a n => saddr_vars_lt b a && expr_vars_lt b n
  | KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
  | KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
  | KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
  end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
  match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
  end.

Definition env_agree (b : nat) (E E' : env) : Prop :=
  (forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

Lemma edenot_agree : forall b E E' e,
  env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
  intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      end;
    try reflexivity;
    try (rewrite IHe1, IHe2 by assumption; reflexivity);
    try (rewrite IHe by assumption; reflexivity).
  - apply Nat.ltb_lt in H. apply Hv. exact H.
  - rewrite Hb. reflexivity.
Qed.

Lemma adenot_agree : forall b E E' a,
  env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
  intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

Lemma regs_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pb,$0.PE,$1.PE',$1.Psr,(2.$3.)Pregs,(4.&5.(5.&40.))P,(6.R5.R4.R3.)P,(7.$8.(9.R6.R3.)$:.)P,(;.R6.R4.R3.)(;.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
  unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
  assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
  { clear HR r. induction sr as [|e t IH]; intros i.
    - destruct i; reflexivity.
    - cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
      destruct i; [exact He | apply IH; exact Ht]. }
  apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.

Lemma mem_denot_agree : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pb,$0.PE,$1.PE',$1.Pbase,P,(5.&40.)(<.(5.&8.))Plog,(2.$=.)P,(6.R5.R4.R3.)P,(7.$8.(>.R6.R2.)$:.)(7.P,(5.&40.)(<.(5.&8.))(?.R6.R4.R3.)(?.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros b E E' base log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt mem_denot]; intros H.
  - reflexivity.
  - apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    rewrite IH by exact H3. rewrite (adenot_agree b E E' a Ha H1), (edenot_agree b E E' v Ha H2).
    reflexivity.
Qed.

Lemma flat_agree : forall b E E' a n,
  env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
  intros b E E' a n Ha H. unfold flat, estart.
  rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

Lemma log_flat_agree : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pb,$0.PE,$1.PE',$1.Plog,(2.$=.)P,(6.R4.R3.R2.)P,(7.$8.(>.R5.R2.)$:.)P,(10.R5.R3.)(10.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros b E E' log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt log_flat]; intros H Hl.
  - exact I.
  - apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
    destruct Hl as (Hw & Hf & Hr). split; [exact Hw|]. split.
    + apply (flat_agree b E E' a _ Ha H1). exact Hf.
    + apply IH; assumption.
Qed.

Lemma know_ok_agree : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)Pb,$0.PE,$1.PE',$1.Pbase,P,(5.&40.)(<.(5.&8.))Pkn,(2.$12.)P,(6.R5.R4.R3.)P,(7.$8.(13.R6.R2.)$:.)P,(14.R8.R6.R4.R3.)(14.R9.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
  - constructor.
  - apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
    constructor; [| apply IH; assumption].
    destruct Ha as [Hv Hb].
    destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
      [ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
              | rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
              | apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
              | apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
                unfold estart, elenZ in *;
                rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
                        <- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
              | | ].
    + apply andb_prop in HK as [H1 H2].
      rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
      destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
      apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + exact Hk1.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
    + (* [comment removed for export] *)
      apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
      rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
      destruct Hk1 as [A B]. split; [|exact B].
      unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.

(* [comment removed for export] *)
Lemma vals_app_agree : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pvals,(2.(5.&40.))Pextra,(2.(5.&40.))Pebs,P,$0.(2.(5.&8.))(6.(15.(5.&40.)R3.)(16.(17.R3.)R1.)(16.(17.(18.(5.&40.)R3.R2.))R1.))")
(* [comment removed for export] *).
Proof.
  intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
  rewrite app_nth1 by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Run.
Variable segs : list Segment.

(* [comment removed for export] *)
#[using="Type"] Lemma st_ok_entry : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "PE,$1.Pbase,P,(5.&40.)(<.(5.&8.))Prom,P,(5.&40.)(<.(5.&8.))Ppc,$19.Psr,(2.$3.)Pkn,(2.$12.)Pnx,$0.Pregs,(4.&5.(5.&40.))P,(;.R8.R4.R1.)P,(14.Vsegs,R9.R8.R4.)(1:.Vsegs,R:.R9.R8.(1;.R7.R6.(1<.$=.)R5.R4.(1=.$1>.))(1?.$20.R3.(21.&40.R7.)R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
  split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

#[using="Type"] Theorem run_sound : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pfuel,$0.Pstops,(2.$19.)Pscr,$22.Ppc,$19.Psr,(2.$3.)Pkn,(2.$12.)Pnx,$0.Pss',$23.Pscs,(2.$24.)Pscr',$22.PE,$1.Pbase,P,(5.&40.)(<.(5.&8.))Prom,P,(5.&40.)(<.(5.&8.))Pregs,(4.&5.(5.&40.))P,(7.(25.(25.$23.(2.$24.))$22.)(26.Vsegs,R>.$:.R=.R<.(1;.R;.R:.(1<.$=.)R9.R8.(1=.$1>.))(1<.$24.))(27.(25.$23.(2.$24.))$22.(27.$23.(2.$24.)R7.R6.)R5.))P,(;.R5.R;.R2.)P,(14.Vsegs,R6.R5.R;.)P,(28.Vsegs,R6.R7.R9.)(29.(4.&5.(5.&40.))LR,(4.&5.(5.&40.))(2:.(;.R9.(2;.R<.)R1.)(2:.(10.R9.(2<.R<.))(2=.Vsegs,(1?.$20.R6.(21.&40.R10.)R8.R7.)(1?.$20.R1.(21.&40.(2>.R<.))(?.R9.R8.(2<.R<.))R7.)))))")
(* [comment removed for export] *).
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
  eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma eagree_env_agree : forall b E E', eagree b E E' <-> env_agree b E E'.
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma st_okX_entry : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "PE,$1.Pbase,P,(5.&40.)(<.(5.&8.))Prom,P,(5.&40.)(<.(5.&8.))Ppc,$19.Psr,(2.$3.)Pkn,(2.$12.)Pnx,$0.Pregs,(4.&5.(5.&40.))P,(;.R8.R4.R1.)P,(14.Vsegs,R9.R8.R4.)P,(7.$8.(9.R4.R6.)$:.)P,(7.$8.(13.R5.R6.)$:.)PE',$1.P,(2?.R7.R=.R1.)(1:.Vsegs,R2.R=.R<.(1;.R;.R:.(1<.$=.)R9.R8.(1=.$1>.))(1?.$20.R7.(21.&40.R;.)R=.R<.))")
(* [comment removed for export] *).
Proof.
  intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
  apply st_ok_entry.
  - eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
  - eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem runTX_sound : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pt,$30.PK,$0.Pfuel,$0.Pstops,(2.$19.)Ppc,$19.Psr,(2.$3.)Pkn,(2.$12.)Pnx,$0.PE,$1.Pbase,P,(5.&40.)(<.(5.&8.))Prom,P,(5.&40.)(<.(5.&8.))Pregs,(4.&5.(5.&40.))P,(31.Vsegs,R<.)P,(;.R5.R8.R2.)P,(14.Vsegs,R6.R5.R8.)P,(7.$8.(9.R8.R:.)$:.)P,(7.$8.(13.R9.R:.)$:.)Zss',$23.(32.Vsegs,R11.R10.R?.$:.R>.(1;.R=.R<.(1<.$=.)R;.R:.(1=.$1>.)))(29.$1.LE',$1.(29.(4.&5.(5.&40.))LR,(4.&5.(5.&40.))(2:.(6.R=.R<.R2.)(2:.(33.R=.(34.R3.))(2:.(;.R2.(2;.R3.)R1.)(2:.(10.R2.(2<.R3.))(2:.(14.Vsegs,R2.R;.(35.R3.))(2:.(2=.Vsegs,(1?.$20.R9.(21.&40.R10.)R;.R:.)(1?.$20.R1.(21.&40.(2>.R3.))(?.R2.R;.(2<.R3.))R:.))PE'',$1.P,(6.(34.R4.)R3.R1.)(1:.Vsegs,R2.R=.R<.R5.(1?.$20.R3.(21.&40.(2>.R5.))(?.R4.R=.(2<.R5.))R<.))))))))))")
(* [comment removed for export] *).
Proof.
  intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
  destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
              (st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
  exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
  split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
  intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem carry_after : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "PE,$1.Pbase,P,(5.&40.)(<.(5.&8.))Plog,(2.$=.)Pkn,(2.$12.)Phints,(2.$8.)Pkn',(2.$12.)Pscs,(2.$24.)Phs',(2.$8.)P,(7.(25.(25.(2.$12.)(2.$24.))(2.$8.))(36.R6.R5.R4.)(27.(25.(2.$12.)(2.$24.))(2.$8.)(27.(2.$12.)(2.$24.)R3.R2.)R1.))P,(10.R9.R7.)P,(14.Vsegs,R:.R9.R7.)P,(28.Vsegs,R:.R;.R5.)(14.Vsegs,R<.(?.R<.R;.R:.)R7.)")
(* [comment removed for export] *).
Proof. intros. eapply carry_sound; eauto. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma regs_ok_set : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "PE,$1.Psr,(2.$3.)PR,(4.&5.(5.&40.))Prd,(5.&5.)Pv,(5.&40.)Pe,$3.P,(;.R6.R5.R4.)P,(37.(7.(5.&5.)R4.(38.&5.=$39.)))P,(7.(5.&40.)(3:.R8.R3.)R4.)(;.R9.(3;.R8.(3<.R6.)R4.)(3=.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros E sr R rd v e HR Hrd He.
  pose proof (regs_ok_upd E sr R rd v e HR He) as H.
  assert (Hb : bv_eqb rd 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
  rewrite Hb in H. exact H.
Qed.

End Run.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sr_init : list expr := ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(40.#0.)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(3>.$3.(3?.=)(1<.$3.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Lemma regs_ok_init : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psp,(5.&40.)Prest,(2.(5.&40.))Pebs,P,$0.(2.(5.&8.))(;.(16.(17.(3>.(5.&40.)R3.R2.))R1.)$41.(3=.(3=.(42.&5.(5.&40.))(38.&5.+:.$39.)(21.&40.=))(38.&5.+2.$39.)R3.))")
(* [comment removed for export] *).
Proof.
  intros sp rest ebs r.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hlt.
    rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
    set (n := ridx r) in *. clearbody n.
    do 32 (destruct n as [|n]; [vm_compute in Hr0 |- *; first [discriminate | reflexivity] |]).
    exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pa,(5.&40.)Pn,$0.P,(43.(44.(45.&40.O2.)O1.)(45.&40.R2.))P,(43.(46.(45.&40.R3.)(47.R2.))(45.&40.O2.))(7.$8.(48.O4.O3.R4.R3.)$:.)")
(* [comment removed for export] *).

Lemma stk_ok_vaddi : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)Pmem,P,(5.&40.)(<.(5.&8.))Psp,(5.&40.)PK,$19.Poff,$19.Pn,$0.P,(49.R6.R5.R4.R3.)P,(43.R4.(45.&40.R5.))P,(43.(4:.R5.)R4.)P,(43.(46.R5.(47.R4.))=)(7.$8.(48.R:.R9.(4;.R8.R6.)R5.)$:.)")
(* [comment removed for export] *).
Proof.
  intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
  apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_lit : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)Pmem,P,(5.&40.)(<.(5.&8.))Psp,(5.&40.)PK,$19.Pz,$19.Pn,$0.P,(49.R6.R5.R4.R3.)P,(43.(44.(45.&40.R5.)R4.)R3.)P,(43.(46.R4.(47.R3.))(45.&40.R6.))P,(43.=R5.)(7.$8.(48.R:.R9.(21.&40.R6.)R5.)$:.)")
(* [comment removed for export] *).
Proof.
  intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
  apply Hs; rewrite u_small by lia; lia.
Qed.

Lemma stk_ok_grows : forall segs mem mem' sp K,
  stk_ok segs mem sp K -> mem_grows mem mem' -> stk_ok segs mem' sp K.
Proof.
  intros segs mem mem' sp K Hs Hg a n H1 H2. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
Qed.

Lemma stk_ok_mem_denot : forall segs E mem log sp K,
  stk_ok segs mem sp K -> stk_ok segs (mem_denot E mem log) sp K.
Proof. intros. eapply stk_ok_grows; [eassumption | apply mem_denot_grows]. Qed.

(* [comment removed for export] *)
Lemma stk_ok_init : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)Pph,$4<.Psp,(5.&40.)Pargv,(2.(2.(5.&8.)))Penvp,(2.(2.(5.&8.)))Puid,(5.&40.)Phw,(5.&40.)Prdraw,$4=.(49.R8.(4>.R7.R6.R5.R4.R3.R2.R1.)R6.$4?.)")
(* [comment removed for export] *).
Proof.
  intros segs ph sp argv envp uid hw rdraw a n H1 H2.
  apply store_ok_wrap_window; assumption.
Qed.

Lemma kwr_of_stk_ok : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,P,(5.&40.)(<.(5.&8.))Pe,$3.Psp,(5.&40.)PK,$19.P,(7.(5.&40.)(3:.R5.R3.)R2.)P,(49.R7.R5.R3.R2.)P,(2:.(43.=R3.)(43.R3.(45.&40.R4.)))(50.R9.R8.R7.(51.(52.R6.(4:.R4.))(3?.R4.)))")
(* [comment removed for export] *).
Proof.
  intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. rewrite He.
  pose proof (u64_range sp). rewrite u_small by lia. split; [lia|].
  intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma kword_intro : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,P,(5.&40.)(<.(5.&8.))Pe,$3.Pa,(5.&40.)Poff,$19.Pw,$0.Pv,$3.Px,(5.&40.)P,(7.(5.&40.)(3:.R8.R6.)R5.)P,(7.(5.&40.)(3:.R9.R3.)R2.)P,(33.#1.R5.)P,(33.R6.#8.)P,(43.=(46.(45.&40.R9.)R8.))P,(43.(46.(46.(45.&40.R:.)R9.)(47.R8.))(53.+2.+40.))P,(7.(<.(2.(5.&8.)))(54.R?.R=.(21.&40.(46.(45.&40.R;.)R:.))R9.)(55.(2.(5.&8.))(56.R9.R7.)))(50.R10.R?.R>.(57.(52.R=.R;.)R:.R9.))")
(* [comment removed for export] *).
Proof.
  intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
  cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.

Lemma krange_intro : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,P,(5.&40.)(<.(5.&8.))Pe,$3.Plo,$19.Phi,$19.P,(2:.(43.R2.(45.&40.(3:.R5.R3.)))(43.(45.&40.(3:.R5.R3.))R1.))(50.R7.R6.R5.(58.R4.R3.R2.))")
(* [comment removed for export] *).
Proof. intros. cbn [kentry_ok]. lia. Qed.

Lemma kalign_intro : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,P,(5.&40.)(<.(5.&8.))Pe,$3.Pm,$19.P,(59.=R1.)P,(7.$19.(5:.(45.&40.(3:.R5.R3.))R2.)=)(50.R7.R6.R5.(5;.R4.R3.))")
(* [comment removed for export] *).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kimg_intro : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,Px,(5.&40.)(<.(5.&8.))Plo,$19.Phi,$19.P,(43.=R2.)P,(43.R2.(53.+2.+40.))P,Pi,$19.P,(2:.(43.R5.R1.)(59.R1.R4.))(7.(<.(5.&8.))A1.R7.(21.&40.R2.)(1=.(5.&8.)))(50.R8.R7.R6.(5<.R5.R4.))")
(* [comment removed for export] *).
Proof. intros. cbn [kentry_ok]. auto. Qed.

Lemma kzero_intro : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,Px,(5.&40.)(<.(5.&8.))Pe,$3.Pa,(5.&40.)Poff,$19.Pn,$3.Plen,$19.P,(7.(5.&40.)(3:.R7.R5.)R4.)P,(7.$19.(45.&40.(3:.R8.R3.))R2.)P,(43.=(46.(45.&40.R6.)R5.))P,(59.=R4.)P,(43.(46.(46.(45.&40.R8.)R7.)R5.)(53.+2.+40.))P,Pi,$19.P,(2:.(43.=R1.)(59.R1.R7.))(7.(<.(5.&8.))A1.R=.(21.&40.(46.(46.(45.&40.R;.)R:.)R2.))(55.(5.&8.)(21.&8.=)))(50.R>.R=.R<.(5=.(52.R;.R9.)R8.))")
(* [comment removed for export] *).
Proof.
  intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.

Lemma kblob_intro : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Psegs,(2.$11.)PE,$1.Pmem,Px,(5.&40.)(<.(5.&8.))Pe,$3.Pa,(5.&40.)Poff,$19.Pn,$3.Pk,$0.Pbs,(2.(5.&8.))P,(7.(5.&40.)(3:.R8.R6.)R5.)P,(7.(2.(5.&8.))(5>.R9.R3.)R2.)P,(7.$19.(45.&40.(3:.R:.R5.))(47.(15.(5.&8.)R3.)))P,(43.=(46.(45.&40.R8.)R7.))P,(59.(46.(45.&40.R9.)R8.)(53.+2.+40.))P,(43.(46.(46.(45.&40.R:.)R9.)(47.(15.(5.&8.)R6.)))(53.+2.+40.))P,Pi,$19.P,(2:.(43.=R1.)(59.R1.(47.(15.(5.&8.)R8.))))(7.(<.(5.&8.))A1.R?.(21.&40.(46.(46.(45.&40.R=.)R<.)R2.))(55.(5.&8.)(5?.(5.&8.)(60.R2.)R9.(21.&8.=))))(50.R10.R?.R>.(61.(52.R=.R;.)R:.R9.))")
(* [comment removed for export] *).
Proof.
  intros segs E mem e a off n k bs He Hb Hn H1 H1' H2 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
  cbn [a_base a_off]. rewrite He, Hn, Hb. split; [lia|]. split; [reflexivity | exact Hz].
Qed.

(* [comment removed for export] *)
Lemma wrap_mem_none_low : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pph,$4<.Psp,(5.&40.)Pargv,(2.(2.(5.&8.)))Penvp,(2.(2.(5.&8.)))Puid,(5.&40.)Phw,(5.&40.)Prdraw,$4=.Pi,$19.P,(43.=R1.)P,(59.R2.(44.(45.&40.R8.)$4?.))(7.(<.(5.&8.))(4>.R:.R9.R8.R7.R6.R5.R4.(21.&40.R3.))(1=.(5.&8.)))")
(* [comment removed for export] *).
Proof.
  intros ph sp argv envp uid hw rdraw i H0 Hi. unfold wrap_mem.
  pose proof (u64_range sp) as Hsp.
  assert (Hu : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; unfold stack_max_size in Hi; lia).
  unfold stack_to_mem. rewrite Hu.
  replace (Z.leb (bv_unsigned sp) i) with false by (symmetry; apply Z.leb_gt; unfold stack_max_size in Hi; lia).
  replace (Z.leb (bv_unsigned sp - stack_max_size) i) with false by (symmetry; apply Z.leb_gt; lia).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ext_val_zx_id : forall n (v : word),
  (bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> ext_val false 0 n v = v.
Proof.
  intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma ext_val_sx_id : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pn,$0.Pv,(5.&40.)P,(33.#1.R2.)P,(59.(45.&40.R2.)(53.+2.(44.(62.+8.(47.R3.))+1.)))(7.(5.&40.)(63.$:.#0.R4.R3.)R3.)")
(* [comment removed for export] *).
Proof.
  intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
  assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
  { rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
  change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
  rewrite <- Hp. rewrite Z.div_mul by lia.
  rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
    with (bv_unsigned v) by lia.
  apply Z_to_bv_bv_unsigned.
Qed.

Lemma branch_eq_lit : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pv,(5.&40.)Pz,$19.P,(2:.(43.=R1.)(59.R1.(53.+2.+40.)))(7.$8.(64.$65.R3.(21.&40.R2.))(66.(45.&40.R3.)R2.))")
(* [comment removed for export] *).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ne_lit : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pv,(5.&40.)Pz,$19.P,(2:.(43.=R1.)(59.R1.(53.+2.+40.)))(7.$8.(64.$67.R3.(21.&40.R2.))(68.(66.(45.&40.R3.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ltu_lit_r : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pv,(5.&40.)Pz,$19.P,(2:.(43.=R1.)(59.R1.(53.+2.+40.)))(7.$8.(64.$69.R3.(21.&40.R2.))(6:.(45.&40.R3.)R2.))")
(* [comment removed for export] *).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_ltu_lit_l : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pv,(5.&40.)Pz,$19.P,(2:.(43.=R1.)(59.R1.(53.+2.+40.)))(7.$8.(64.$69.(21.&40.R2.)R3.)(6:.R2.(45.&40.R3.)))")
(* [comment removed for export] *).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_geu_lit_r : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pv,(5.&40.)Pz,$19.P,(2:.(43.=R1.)(59.R1.(53.+2.+40.)))(7.$8.(64.$6;.R3.(21.&40.R2.))(68.(6:.(45.&40.R3.)R2.)))")
(* [comment removed for export] *).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

Lemma branch_geu_lit_l : ltac2:(CDefT.buildp (gd_tbl_AxSymRun3 ()) "Pv,(5.&40.)Pz,$19.P,(2:.(43.=R1.)(59.R1.(53.+2.+40.)))(7.$8.(64.$6;.(21.&40.R2.)R3.)(68.(6:.R2.(45.&40.R3.))))")
(* [comment removed for export] *).
Proof.
  intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac split_scs :=
  lazymatch goal with
  | |- scs_denot _ _ _ [] => constructor
  | |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
  | |- Forall _ [] => constructor
  | |- Forall _ (_ :: _) => constructor; [| split_scs]
  end.

(* [comment removed for export] *)
Ltac ground_mod :=
  repeat match goal with
  | |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with
      | context [bv_unsigned _] => fail
      | _ => lazymatch b with
             | context [bv_unsigned _] => fail
             | _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
             end
      end
  end.

Ltac sc_unfold :=
  unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev eb vals_ev nth];
  rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

(* [comment removed for export] *)
Ltac lit_u :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned _] => fail
      | _ => rewrite (u_small z) by (cbn; lia)
      end
  end.

(* [comment removed for export] *)
Ltac sc_store :=
  match goal with
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
      apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
  | Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
      apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
  end.

Ltac sc_auto extra :=
  sc_unfold;
  first [ lia
        | sc_store
        | extra
        | match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
        | idtac ].

(* [comment removed for export] *)
Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok _ _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; sc_auto extra
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          (eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc ]
          end
      end
    end
  end.
