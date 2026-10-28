(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec StoreOk AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs AsanPlanImages. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMainEntryLemmas () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ct"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.at_"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.wt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "lookup_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.cell_ok"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cinst"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWord"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ainst"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.winst"; "lookup_zero"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CZero"; "lookup_wr"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanMainEntryKit.CWr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_params"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_init"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.NX0"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.pget"; "Corelib.Lists.ListDef.nth"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.pv"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s1"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_argc"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_envc"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_len0"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_wblk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_brk0pg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_s2"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_len1"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_uidw"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_hwd"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.ABoot.AxSymExec3.AX2.ev"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanInit.E0"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanPlanImages.APH"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.me_regs"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.Riscv.Sem.alu64"; "LinuxProcessSemantics.Riscv.Instr.ALU_ADD"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.argc"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanCertDefs.ASEGS"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlanSound.APS.in_hull"; "RocqVerifyHarness.AgentSubmission.ABoot.AsanPlan.AP.BOTH"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_bss_allocator_instance"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_bss_runtime"; "Page"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "SpaceBeg"; "RegionInfoA"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_secv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_map_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_map_thr"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_addi"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_thr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_treg"; "StackTop"; "StackBottom"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_fstk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_map_fstk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_bss_depot"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_bss_stackstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dnodes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dstore"; "lsh_cell_byte"; "lsh_lookup"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.cells_lowshadow"; "LSH_LO"; "LSH_HI"; "img_shb"; "Stdlib.ZArith.BinInt.Z.mul"; "nz_clear"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.CELLS_lowshadow"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.main_entry_A"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Scheme Equality for pv.   (* [comment removed for export] *)

Fixpoint wt_eqb (a b : wt) : bool :=
  match a, b with
  | WLit x, WLit y => Z.eqb x y
  | WVar u, WVar v => pv_beq u v
  | WAlu o a1 a2, WAlu o' b1 b2 | WAluw o a1 a2, WAluw o' b1 b2 => aluop_eqb o o' && wt_eqb a1 b1 && wt_eqb a2 b2
  | WMd o a1 a2, WMd o' b1 b2 | WMdw o a1 a2, WMdw o' b1 b2 => mulop_eqb o o' && wt_eqb a1 b1 && wt_eqb a2 b2
  | WExt s lo n a1, WExt s' lo' n' b1 => Bool.eqb s s' && Nat.eqb lo lo' && Nat.eqb n n' && wt_eqb a1 b1
  | _, _ => false
  end.
Lemma pv_beq_eq : forall u v, pv_beq u v = true -> u = v.
Proof. intros u v H. destruct (pv_eq_dec u v) as [E|NE]; [exact E|]. exfalso. apply internal_pv_dec_bl in H. exact (NE H). Qed.
Lemma wt_eqb_eq : forall a b, wt_eqb a b = true -> a = b.
Proof.
  induction a; destruct b; cbn [wt_eqb]; intros H; try discriminate;
    repeat match goal with
      | H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
      | H : aluop_eqb _ _ = true |- _ => apply aluop_eqb_eq in H
      | H : mulop_eqb _ _ = true |- _ => apply mulop_eqb_eq in H
      | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H
      | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
      | H : Bool.eqb _ _ = true |- _ => apply eqb_prop in H
      | H : pv_beq _ _ = true |- _ => apply pv_beq_eq in H
      end; subst;
    repeat match goal with
      | IH : forall b, wt_eqb ?a b = true -> ?a = b, H : wt_eqb ?a ?b = true |- _ => apply IH in H; subst
      end; reflexivity.
Qed.
Definition at_eqb (a b : at_) : bool :=
  match a, b with
  | ALit x, ALit y => Z.eqb x y
  | AOff u x, AOff v y => wt_eqb u v && Z.eqb x y
  | _, _ => false
  end.
Lemma at_eqb_eq : forall a b, at_eqb a b = true -> a = b.
Proof.
  intros [x|u x] [y|v y] H; cbn [at_eqb] in H; try discriminate.
  - apply Z.eqb_eq in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply wt_eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint lookup_word (l : list ct) (a : at_) (w : nat) : option wt :=
  match l with
  | [] => None
  | TWord a' w' v :: r => if (at_eqb a' a && Nat.eqb w' w)%bool then Some v else lookup_word r a w
  | _ :: r => lookup_word r a w
  end.
Fixpoint lookup_zero (l : list ct) (a : at_) : option wt :=
  match l with
  | [] => None
  | TZero a' n :: r => if at_eqb a' a then Some n else lookup_zero r a
  | _ :: r => lookup_zero r a
  end.
Fixpoint lookup_wr (l : list ct) (a : at_) : option wt :=
  match l with
  | [] => None
  | TWr a' n :: r => if at_eqb a' a then Some n else lookup_wr r a
  | _ :: r => lookup_wr r a
  end.

Section Lookup.
  Variable segs : list Segment.
  Variable M : word -> option byte.
  Variable p : me_params.

  #[using="Type"] Lemma lookup_word_ok : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pl,(0.$1.)Pa,$2.Pw,$3.Pv,$4.P,(5.(6.$4.)(7.R4.R3.R2.)(8.$4.R1.))P,(9.$:.(;.Vsegs,VM,)(<.$1.$:.(=.Vp,)R5.))(;.Vsegs,VM,(>.(?.Vp,R5.)R4.(10.Vp,R3.)))")
(* [comment removed for export] *).
  Proof.
    induction l as [|c l IH]; intros a w v Hl HF; [discriminate|].
    cbn [map] in HF. inversion HF as [|c' l' Hc Hl']; subst.
    destruct c as [a' w' v'|a' n|a' n c8|a' n|a' n|lo hi]; cbn [lookup_word] in Hl; try exact (IH a w v Hl Hl').
    destruct (at_eqb a' a && Nat.eqb w' w)%bool eqn:E; [|exact (IH a w v Hl Hl')].
    injection Hl as <-. apply andb_prop in E as [E1 E2]. apply at_eqb_eq in E1. apply Nat.eqb_eq in E2. subst. exact Hc.
  Qed.
  #[using="Type"] Lemma lookup_zero_ok : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pl,(0.$1.)Pa,$2.Pn,$4.P,(5.(6.$4.)(11.R3.R2.)(8.$4.R1.))P,(9.$:.(;.Vsegs,VM,)(<.$1.$:.(=.Vp,)R4.))(;.Vsegs,VM,(12.(?.Vp,R4.)(10.Vp,R3.)))")
(* [comment removed for export] *).
  Proof.
    induction l as [|c l IH]; intros a n Hl HF; [discriminate|].
    cbn [map] in HF. inversion HF as [|c' l' Hc Hl']; subst.
    destruct c as [a' w' v'|a' n'|a' n' c8|a' n'|a' n'|lo hi]; cbn [lookup_zero] in Hl; try exact (IH a n Hl Hl').
    destruct (at_eqb a' a) eqn:E; [|exact (IH a n Hl Hl')].
    injection Hl as <-. apply at_eqb_eq in E. subst. exact Hc.
  Qed.
  #[using="Type"] Lemma lookup_wr_ok : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pl,(0.$1.)Pa,$2.Pn,$4.P,(5.(6.$4.)(13.R3.R2.)(8.$4.R1.))P,(9.$:.(;.Vsegs,VM,)(<.$1.$:.(=.Vp,)R4.))(;.Vsegs,VM,(14.(?.Vp,R4.)(10.Vp,R3.)))")
(* [comment removed for export] *).
  Proof.
    induction l as [|c l IH]; intros a n Hl HF; [discriminate|].
    cbn [map] in HF. inversion HF as [|c' l' Hc Hl']; subst.
    destruct c as [a' w' v'|a' n'|a' n' c8|a' n'|a' n'|lo hi]; cbn [lookup_wr] in Hl; try exact (IH a n Hl Hl').
    destruct (at_eqb a' a) eqn:E; [|exact (IH a n Hl Hl')].
    injection Hl as <-. apply at_eqb_eq in E. subst. exact Hc.
  Qed.
End Lookup.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac me_group H k :=
  lazymatch type of H with
  | Forall _ ?l =>
      let l' := eval red in l in
      lazymatch l' with
      | map (cinst ?p) ?L => k p L
      | _ => lazymatch l with map (cinst ?p) ?L => k p L | _ => fail "me_*: hypothesis is not a cell-group Forall" end
      end
  end.
Ltac me_word H a w X :=
  me_group H ltac:(fun p L =>
      let r := eval vm_compute in (lookup_word L a w) in
      lazymatch r with
      | Some ?v => pose proof (lookup_word_ok _ _ p L a w v (eq_refl : lookup_word L a w = Some v) H) as X;
                   cbn [cinst ainst winst pget] in X
      | None => fail "me_word: no word cell with that address/width in this group"
      end).
Ltac me_zrun H a X :=
  me_group H ltac:(fun p L =>
      let r := eval vm_compute in (lookup_zero L a) in
      lazymatch r with
      | Some ?n => pose proof (lookup_zero_ok _ _ p L a n (eq_refl : lookup_zero L a = Some n) H) as X;
                   cbn [cinst ainst winst pget] in X
      | None => fail "me_zrun: no zero run at that address in this group"
      end).
Ltac me_wr H a X :=
  me_group H ltac:(fun p L =>
      let r := eval vm_compute in (lookup_wr L a) in
      lazymatch r with
      | Some ?n => pose proof (lookup_wr_ok _ _ p L a n (eq_refl : lookup_wr L a = Some n) H) as X;
                   cbn [cinst ainst winst pget] in X
      | None => fail "me_wr: no writable run at that address in this group"
      end).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope tm_scope.
(* [comment removed for export] *)
Definition SP0 : wt := ((#0x8000 * v_s1) + (#16 * v_s2)).
Definition sp0w (p : me_params) : word := winst p SP0.
(* [comment removed for export] *)
Definition Page (p : me_params) (k : pv) : word := winst p (#0x1000 * k).
(* [comment removed for export] *)
Definition PBASE : wt := ((#0x1000 * v_prim) + (#(-0x1000) * v_pslack)).
Definition SPACEBEG : wt := (PBASE + #0x10000).
Definition REGIONINFO : wt := (PBASE + #0x2000010000).
Definition SpaceBeg (p : me_params) : word := winst p SPACEBEG.
Definition RegionInfoA (p : me_params) : word := winst p REGIONINFO.
Lemma v_addi_alu : forall (x : word) (c : Z), v_addi x c = alu64 Instr.ALU_ADD x (Z_to_bv 64 c).
Proof.
  intros x c. rewrite alu_add. unfold v_addi, v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
Lemma RegionInfoA_addi : forall p, v_addi (winst p PBASE) 0x2000010000 = RegionInfoA p.
Proof. intros p. unfold RegionInfoA, REGIONINFO. cbn [winst]. apply v_addi_alu. Qed.
Lemma SpaceBeg_addi : forall p, v_addi (winst p PBASE) 0x10000 = SpaceBeg p.
Proof. intros p. unfold SpaceBeg, SPACEBEG. cbn [winst]. apply v_addi_alu. Qed.
(* [comment removed for export] *)
Definition STACKTOP : wt := ((#0x8000 * v_s1) + (#0x1000 * v_tpg)).
Definition StackTop (p : me_params) : word := winst p STACKTOP.
Definition StackBottom (p : me_params) : word := winst p (STACKTOP + #(-0x800000)).
Close Scope tm_scope.

Section WithRun.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  (* [comment removed for export] *)
  #[using="Type"] Lemma me_init_E0 : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pp,$15.P,(16.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vuid,Vhw,R1.)Pk,$3.P,(17.R1.$18.)(5.(19.&40.)(1:.R4.(1;.$1<.R2.(1=.$1<.$1>.(1=.$1<.$1?.(1=.$1<.$20.(1=.$1<.$21.(1=.$1<.$22.(1=.$1<.$23.(1=.$1<.$24.(1=.$1<.$25.(1=.$1<.$26.(1=.$1<.$27.(28.$1<.)))))))))))$1>.))(29.(2:.$2;.Vsp,Vrdraw,Vbrk0,Vargv,Venvp,Vuid,Vhw,)R2.))")
(* [comment removed for export] *).
  Proof.
    intros p (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) k Hk.
    destruct k as [|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]; cbn [nth pget]; try (unfold NX0 in Hk; lia);
      first [exact H0 | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact H8 | exact H9].
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma sp0w_eq : forall p, me_init sp brk0 rdraw argv envp uid hw p -> sp0w p = sp.
  Proof.
    intros p HI. rewrite <- (edenot_e_sp0 APH sp rdraw brk0 argv envp uid hw Hsp Hva Hve Hfit).
    unfold sp0w, SP0. cbn [winst pget edenot e_sp0 eadd escale mkAlu mkMd].
    rewrite (me_init_E0 p HI 0%nat ltac:(unfold NX0; lia) : s1 p = _), (me_init_E0 p HI 6%nat ltac:(unfold NX0; lia) : s2 p = _).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit"] Lemma me_regs_sp : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pp,$15.PR,(2<.&5.(19.&40.))P,(16.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vuid,Vhw,R2.)P,(2=.R3.R2.)(2>.(5.(19.&40.)(2?.R3.(30.&5.+1.$31.))(32.&40.+>0::8.))(2>.(5.(19.&40.)(2?.R3.(30.&5.+2.$31.))(33.$34.Vsp,(32.&40.-30.)))(2>.(5.(19.&40.)(2?.R3.(30.&5.+3.$31.))(32.&40.+10800.))(2>.(5.(19.&40.)(2?.R3.(30.&5.+4.$31.))(32.&40.+63<:90.))(2>.(5.(19.&40.)(2?.R3.(30.&5.+:.$31.))(35.R4.))(2>.(5.(19.&40.)(2?.R3.(30.&5.+;.$31.))(33.$34.Vsp,(32.&40.+8.)))(2>.(5.(19.&40.)(2?.R3.(30.&5.+8.$31.))(33.$34.Vsp,(32.&40.+8.)))(2>.(5.(19.&40.)(2?.R3.(30.&5.+9.$31.))(35.R4.))(2>.(5.(19.&40.)(2?.R3.(30.&5.+12.$31.))(32.&40.+970>0.))(2>.(5.(19.&40.)(2?.R3.(30.&5.+14.$31.))(32.&40.=))(2>.(5.(19.&40.)(2?.R3.(30.&5.+15.$31.))(32.&40.=))(2>.(5.(19.&40.)(2?.R3.(30.&5.+16.$31.))(32.&40.=))(2>.(5.(19.&40.)(2?.R3.(30.&5.+17.$31.))(32.&40.=))(2>.(5.(19.&40.)(2?.R3.(30.&5.+18.$31.))(32.&40.=))(2>.(5.(19.&40.)(2?.R3.(30.&5.+19.$31.))(32.&40.=))(2>.(5.(19.&40.)(2?.R3.(30.&5.+1:.$31.))(32.&40.=))(5.(19.&40.)(2?.R3.(30.&5.+1;.$31.))(32.&40.=))))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros p R HI HR. pose proof (sp0w_eq p HI) as S. unfold sp0w, SP0 in S. cbn [winst pget] in S.
    unfold me_regs in HR. cbn [winst pget] in HR. rewrite !S in HR.
    decompose [and] HR. repeat split; assumption.
  Qed.
End WithRun.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cwr_defined : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "PM,P,(19.&40.)(6.(19.&8.))Pa,(19.&40.)Pn,(19.&40.)P,(;.$36.R3.(14.R2.R1.))P,Pz,$37.P,(2>.(38.(39.&40.R4.)R1.)(3:.R1.(3;.(39.&40.R4.)(39.&40.R3.))))(5.$3<.(3=.$3>.R2.)$3?.)Pi,$37.P,(2>.(38.=R1.)(3:.R1.(39.&40.R4.)))(40.(5.(6.(19.&8.))A1.R7.(32.&40.(3;.(39.&40.R6.)R2.))(41.(19.&8.))))")
(* [comment removed for export] *).
Proof.
  intros M a n [Hnw Hs] Hout i Hi X. pose proof (u64_range a) as Ra. pose proof (u64_range n) as Rn.
  assert (Hi1 : i + Z.of_nat 1 <= bv_unsigned n) by (cbn; lia).
  specialize (Hs i 1%nat ltac:(lia) Hi1). cbn [store_ok] in Hs.
  unfold wview in Hs. rewrite X in Hs.
  pose proof (asan_in_hull (Z_to_bv 64 (bv_unsigned a + i))) as Hf.
  assert (U : bv_unsigned (Z_to_bv 64 (bv_unsigned a + i)) = bv_unsigned a + i) by (apply u64_lit; lia).
  rewrite U in Hf. specialize (Hf (Hout (bv_unsigned a + i) ltac:(lia))).
  rewrite U in Hs.
  lazymatch type of Hs with context [find_segment ?S ?z ?o] =>
    replace (find_segment S z o) with (@None Segment) in Hs by (symmetry; exact Hf) end.
  discriminate Hs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope tm_scope.
Section Headline.
  Variable mem : word -> option byte.
  Variable p : me_params.

  (* [comment removed for export] *)
  #[using="Type"] Lemma me_allocator_init : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "P,(9.$:.(;.$36.Vmem,)(42.Vp,))P,(9.$:.(;.$36.Vmem,)(43.Vp,))(2>.(;.$36.Vmem,(>.(32.&40.+106398.)#8.(44.Vp,$45.)))(2>.(;.$36.Vmem,(>.(32.&40.+1063:0.)#8.(32.&40.+2000011000.)))(2>.(;.$36.Vmem,(>.(32.&40.+1063;8.)#8.(46.Vp,)))(2>.(;.$36.Vmem,(>.(32.&40.+1063<0.)#4.(32.&40.+????????????????.)))(2>.(;.$36.Vmem,(>.(32.&40.+1063<8.)#8.(47.Vp,)))(2>.(;.$36.Vmem,(>.(32.&40.+1063=0.)#1.(32.&40.=)))(2>.(;.$36.Vmem,(>.(32.&40.+1063=8.)#8.(32.&40.+1000.)))(2>.(;.$36.Vmem,(>.(32.&40.+1063>0.)#8.(44.Vp,$48.)))(2>.(;.$36.Vmem,(>.(32.&40.+1063>8.)#8.(44.Vp,$48.)))(2>.(;.$36.Vmem,(>.(32.&40.+1063?0.)#8.(32.&40.+800000.)))(2>.(;.$36.Vmem,(>.(32.&40.+1066;0.)#8.(32.&40.+10000000.)))(2>.(;.$36.Vmem,(>.(32.&40.+1066;8.)#8.(32.&40.+>666661.)))(2>.(;.$36.Vmem,(>.(32.&40.+1066<0.)#8.(32.&40.+100000.)))(2>.(;.$36.Vmem,(>.(32.&40.+1071;8.)#8.(32.&40.+10000000000.)))(2>.(;.$36.Vmem,(>.(32.&40.+1071<0.)#2.(32.&40.+10.)))(2>.(;.$36.Vmem,(>.(32.&40.+1071<2.)#2.(32.&40.+800.)))(2>.(;.$36.Vmem,(>.(32.&40.+1071<4.)#1.(32.&40.+1.)))(2>.(;.$36.Vmem,(>.(32.&40.+1099?8.)#8.(32.&40.+7???8000.)))(2>.(;.$36.Vmem,(>.(32.&40.+109:00.)#4.(32.&40.+1.)))(;.$36.Vmem,(>.(32.&40.+10:6=8.)#1.(32.&40.+1.))))))))))))))))))))))")
(* [comment removed for export] *).          (* [comment removed for export] *)
  Proof.
    intros HA HB.
    me_word HA (ALit 0x106398) 8%nat X1. me_word HA (ALit 0x1063a0) 8%nat X2. me_word HA (ALit 0x1063b8) 8%nat X3. me_word HA (ALit 0x1063c0) 4%nat X4.
    me_word HA (ALit 0x1063c8) 8%nat X5. me_word HA (ALit 0x1063d0) 1%nat X6. me_word HA (ALit 0x1063d8) 8%nat X7. me_word HA (ALit 0x1063e0) 8%nat X8.
    me_word HA (ALit 0x1063e8) 8%nat X9. me_word HA (ALit 0x1063f0) 8%nat X10. me_word HA (ALit 0x1066b0) 8%nat X11. me_word HA (ALit 0x1066b8) 8%nat X12.
    me_word HA (ALit 0x1066c0) 8%nat X13. me_word HA (ALit 0x1071b8) 8%nat X14. me_word HA (ALit 0x1071c0) 2%nat X15. me_word HA (ALit 0x1071c2) 2%nat X16.
    me_word HA (ALit 0x1071c4) 1%nat X17. me_word HB (ALit 0x1099f8) 8%nat X18. me_word HB (ALit 0x109a00) 4%nat X19. me_word HB (ALit 0x10a6d8) 1%nat X20.
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact X10|]. split; [exact X11|]. split; [exact X12|]. split; [exact X13|]. split; [exact X14|]. split; [exact X15|]. split; [exact X16|]. split; [exact X17|]. split; [exact X18|]. split; [exact X19|]. exact X20.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma me_regioninfo_zero : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "P,(9.$:.(;.$36.Vmem,)(49.Vp,))(2>.(;.$36.Vmem,(14.(47.Vp,)(32.&40.+1000.)))(;.$36.Vmem,(12.(47.Vp,)(32.&40.+1000.))))")
(* [comment removed for export] *).
  Proof.
    intros H. me_wr H (PBASE .+ 0x2000010000) X1. me_zrun H (PBASE .+ 0x2000010000) X2.
    rewrite RegionInfoA_addi in X1, X2. split; [exact X1 | exact X2].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma me_thread_init : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "P,(9.$:.(;.$36.Vmem,)(4:.Vp,))(2>.(;.$36.Vmem,(>.(4;.(44.Vp,$4<.)=)#8.(44.Vp,$4=.)))(2>.(;.$36.Vmem,(>.(4;.(44.Vp,$4<.)+8.)#8.(4>.Vp,)))(2>.(;.$36.Vmem,(>.(4;.(44.Vp,$4<.)+10.)#8.(4?.Vp,)))(2>.(;.$36.Vmem,(>.(4;.(44.Vp,$4<.)+28.)#1.(32.&40.=)))(2>.(;.$36.Vmem,(>.(4;.(44.Vp,$4<.)+48.)#8.(44.Vp,$50.)))(2>.(;.$36.Vmem,(12.(4;.(44.Vp,$4<.)+50.)(32.&40.+<10.)))(;.$36.Vmem,(14.(4;.(44.Vp,$4<.)=)(32.&40.+1000.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros H.
    me_word H ((#0x1000 * v_thr) .+ 0) 8%nat X1. me_word H ((#0x1000 * v_thr) .+ 8) 8%nat X2. me_word H ((#0x1000 * v_thr) .+ 16) 8%nat X3.
    me_word H ((#0x1000 * v_thr) .+ 40) 1%nat X4. me_word H ((#0x1000 * v_thr) .+ 72) 8%nat X5.
    me_zrun H ((#0x1000 * v_thr) .+ 80) X6. me_wr H ((#0x1000 * v_thr) .+ 0) X7.
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. exact X7.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma me_fakestack_init : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "P,(9.$:.(;.$36.Vmem,)(51.Vp,))(2>.(;.$36.Vmem,(14.(4;.(44.Vp,$50.)=)(32.&40.+;09000.)))(2>.(;.$36.Vmem,(12.(4;.(44.Vp,$50.)=)(32.&40.+58.)))(2>.(;.$36.Vmem,(>.(4;.(44.Vp,$50.)+58.)#8.(32.&40.+14.)))(;.$36.Vmem,(12.(4;.(44.Vp,$50.)+60.)(32.&40.+;08?:0.))))))")
(* [comment removed for export] *).
  Proof.
    intros H. me_wr H ((#0x1000 * v_fstk) .+ 0) X1. me_zrun H ((#0x1000 * v_fstk) .+ 0) X2.
    me_word H ((#0x1000 * v_fstk) .+ 88) 8%nat X3. me_zrun H ((#0x1000 * v_fstk) .+ 96) X4.
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. exact X4.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma me_depot_init : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "P,(9.$:.(;.$36.Vmem,)(52.Vp,))P,(9.$:.(;.$36.Vmem,)(53.Vp,))(2>.(;.$36.Vmem,(>.(32.&40.+5>;8=8.)#4.(32.&40.+1.)))(2>.(;.$36.Vmem,(>.(32.&40.+5>;8>8.)#8.(44.Vp,$54.)))(2>.(;.$36.Vmem,(>.(32.&40.+1=;8=8.)#8.(44.Vp,$55.)))(;.$36.Vmem,(>.(32.&40.+1=;8=0.)#8.(32.&40.+800000.))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  Proof.
    intros HD HS. me_word HD (ALit 0x5eb8d8) 4%nat X1. me_word HD (ALit 0x5eb8e8) 8%nat X2. me_word HS (ALit 0x1db8d8) 8%nat X3. me_word HS (ALit 0x1db8d0) 8%nat X4.
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. exact X4.
  Qed.
End Headline.
Close Scope tm_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alit (a : at_) : option Z := match a with ALit z => Some z | _ => None end.
Definition wlit (t : wt) : option Z := match t with WLit z => Some z | _ => None end.
Lemma alit_sound : forall p a z, alit a = Some z -> ainst p a = Z_to_bv 64 z.
Proof. intros p [x|b off] z H; cbn [alit] in H; [injection H as -> | discriminate H]. reflexivity. Qed.
Lemma wlit_sound : forall p t z, wlit t = Some z -> winst p t = Z_to_bv 64 z.
Proof. intros p t z H. destruct t; cbn [wlit] in H; try discriminate H. injection H as ->. reflexivity. Qed.

(* [comment removed for export] *)
Definition lsh_run_ok (a n z : Z) : bool := ((0 <=? a) && (0 <=? n) && (n <? 2 ^ 62) && (a + n <=? 2 ^ 64) && (a <=? z) && (z <? a + n))%bool.
Definition lsh_cell_byte (c : ct) (z : Z) : option byte :=
  match c with
  | TZero a n => match alit a, wlit n with Some a, Some n => if lsh_run_ok a n z then Some (Z_to_bv 8 0) else None | _, _ => None end
  | TFill a n b => match alit a, wlit n with Some a, Some n => if lsh_run_ok a n z then Some (Z_to_bv 8 b) else None | _, _ => None end
  | TWord a (S O) v => match alit a, wlit v with Some a, Some v =>
      if ((0 <=? a) && (a + 1 <=? 2 ^ 64) && (z =? a))%bool then Some (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 v))) else None | _, _ => None end
  | _ => None
  end.
Fixpoint lsh_lookup (l : list ct) (z : Z) : option byte :=
  match l with [] => None | c :: r => match lsh_cell_byte c z with Some b => Some b | None => lsh_lookup r z end end.
(* [comment removed for export] *)
Definition lsh_ext_ok (a n : Z) : bool := ((0 <=? a) && (0 <=? n) && (n <? 2 ^ 62) && (a + n <=? 2 ^ 64))%bool.
Definition lsh_extent (c : ct) : option (Z * Z) :=
  match c with
  | TZero a n | TFill a n _ => match alit a, wlit n with Some a, Some n => if lsh_ext_ok a n then Some (a, a + n) else None | _, _ => None end
  | TWord a (S O) v => match alit a, wlit v with Some a, Some _ => if ((0 <=? a) && (a + 1 <=? 2 ^ 64))%bool then Some (a, a + 1) else None | _, _ => None end
  | _ => None
  end.
Lemma lsh_run_ok_of_ext : forall a n z, lsh_ext_ok a n = true -> a <= z < a + n -> lsh_run_ok a n z = true.
Proof.
  intros a n z H Hz. unfold lsh_run_ok, lsh_ext_ok in *. rewrite H. cbn [andb].
  apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma lsh_extent_byte : forall c a b z, lsh_extent c = Some (a, b) -> a <= z < b -> exists v, lsh_cell_byte c z = Some v.
Proof.
  intros c a b z He Hz.
  destruct c as [a0 w v|a0 n|a0 n c8|a0 n|a0 n|lo hi]; cbn [lsh_extent] in He; try discriminate He; cbn [lsh_cell_byte].
  - destruct w as [|[|w]]; try discriminate He.
    destruct (alit a0) as [a'|]; [|discriminate He]. destruct (wlit v) as [v'|]; [|discriminate He].
    destruct ((0 <=? a') && (a' + 1 <=? 2 ^ 64))%bool eqn:G; [|discriminate He]. injection He as <- <-.
    cbn [andb]. replace (z =? a') with true by (symmetry; apply Z.eqb_eq; lia). eexists; reflexivity.
  - destruct (alit a0) as [a'|]; [|discriminate He]. destruct (wlit n) as [n'|]; [|discriminate He].
    destruct (lsh_ext_ok a' n') eqn:G; [|discriminate He]. injection He as <- <-.
    rewrite (lsh_run_ok_of_ext a' n' z G Hz). eexists; reflexivity.
  - destruct (alit a0) as [a'|]; [|discriminate He]. destruct (wlit n) as [n'|]; [|discriminate He].
    destruct (lsh_ext_ok a' n') eqn:G; [|discriminate He]. injection He as <- <-.
    rewrite (lsh_run_ok_of_ext a' n' z G Hz). eexists; reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint chain (l : list (Z * Z)) (cur hi : Z) : bool :=
  match l with [] => hi <=? cur | (a, b) :: r => ((a <=? cur) && chain r (Z.max cur b) hi)%bool end.
Lemma chain_sound : forall l cur hi z, chain l cur hi = true -> cur <= z < hi -> exists a b, In (a, b) l /\ a <= z < b.
Proof.
  induction l as [|[a b] r IH]; intros cur hi z Hc Hz; cbn [chain] in Hc.
  - apply Z.leb_le in Hc. lia.
  - apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1.
    destruct (Z_lt_le_dec z b) as [Hlt|Hge].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) hi z H2 ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.
(* [comment removed for export] *)
Fixpoint zins (x : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with [] => [x] | y :: r => if (fst x <=? fst y) then x :: l else y :: zins x r end.
Fixpoint zsort (l : list (Z * Z)) : list (Z * Z) := match l with [] => [] | x :: r => zins x (zsort r) end.
Lemma zins_in : forall x l y, In y (zins x l) -> y = x \/ In y l.
Proof.
  induction l as [|h r IH]; cbn; intros y Hy.
  - destruct Hy as [<-|[]]. left; reflexivity.
  - destruct (fst x <=? fst h); cbn in Hy.
    + destruct Hy as [<-|Hy]; [left; reflexivity | right; exact Hy].
    + destruct Hy as [Hy|Hy]; [right; left; exact Hy|]. destruct (IH y Hy) as [E|Hin]; [left; exact E | right; right; exact Hin].
Qed.
Lemma zsort_in : forall l y, In y (zsort l) -> In y l.
Proof. induction l as [|h r IH]; cbn; intros y Hy; [exact Hy|]. apply zins_in in Hy as [->|Hy]; [left; reflexivity | right; exact (IH y Hy)]. Qed.
Lemma omap_in {X Y} (f : X -> option Y) : forall l y, In y (omap f l) -> exists x, In x l /\ f x = Some y.
Proof.
  induction l as [|x r IH]; cbn; intros y Hy; [destruct Hy|].
  destruct (f x) eqn:E.
  - destruct Hy as [<-|Hy]; [exists x; tauto|]. destruct (IH y Hy) as (x' & H1 & H2). exists x'; tauto.
  - destruct (IH y Hy) as (x' & H1 & H2). exists x'; tauto.
Qed.

Section LowShadowGeneric.
  Variable segs : list Segment.
  Variable M : word -> option byte.
  Variable p : me_params.
  Hypothesis rom_none : forall z, 0x7fffa000 <= z < 0x800c4000 -> seg_rom segs (Z_to_bv 64 z) = None.

  #[using="rom_none"] Lemma lsh_cell_byte_ok : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pc,$1.Pz,$37.Pb,(19.&8.)P,(;.Vsegs,VM,(=.Vp,R3.))P,(5.(6.(19.&8.))(56.R4.R3.)(8.(19.&8.)R2.))P,(2>.(38.+7???:000.R4.)(3:.R4.+800<4000.))(5.(6.(19.&8.))A1.VM,(32.&40.R5.)(8.(19.&8.)R4.))")
(* [comment removed for export] *).
  Proof.
    intros c z b Hc Hb Hz.
    destruct c as [a0 w v|a0 n|a0 n c8|a0 n|a0 n|lo hi]; cbn [lsh_cell_byte] in Hb; try discriminate Hb.
    - (* [comment removed for export] *)
      destruct w as [|[|w]]; try discriminate Hb.
      destruct (alit a0) as [a|] eqn:Ea; [|discriminate Hb]. destruct (wlit v) as [v'|] eqn:Ev; [|discriminate Hb].
      destruct ((0 <=? a) && (a + 1 <=? 2 ^ 64) && (z =? a))%bool eqn:G; [|discriminate Hb]. injection Hb as <-.
      apply andb_prop in G as [G G3]. apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.leb_le in G2. apply Z.eqb_eq in G3. subst z.
      cbn [cinst cell_ok] in Hc. rewrite (alit_sound p a0 a Ea), (wlit_sound p v v' Ev) in Hc. cbn [rdn] in Hc.
      destruct (M (Z_to_bv 64 a)) as [b0|] eqn:HM.
      + cbn in Hc. injection Hc as E. rewrite E. reflexivity.
      + rewrite (rom_none a Hz) in Hc. discriminate Hc.
    - (* [comment removed for export] *)
      destruct (alit a0) as [a|] eqn:Ea; [|discriminate Hb]. destruct (wlit n) as [n'|] eqn:En; [|discriminate Hb].
      destruct (lsh_run_ok a n' z) eqn:G; [|discriminate Hb]. injection Hb as <-. unfold lsh_run_ok in G.
      repeat (apply andb_prop in G as [G ?X]). apply Z.leb_le in G. apply Z.leb_le in X3. apply Z.ltb_lt in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
      cbn [cinst cell_ok] in Hc. rewrite (alit_sound p a0 a Ea), (wlit_sound p n n' En) in Hc. destruct Hc as [_ Hc]. rewrite !u64_lit in Hc by lia.
      specialize (Hc (z - a) ltac:(lia)). replace (a + (z - a)) with z in Hc by lia. exact Hc.
    - (* [comment removed for export] *)
      destruct (alit a0) as [a|] eqn:Ea; [|discriminate Hb]. destruct (wlit n) as [n'|] eqn:En; [|discriminate Hb].
      destruct (lsh_run_ok a n' z) eqn:G; [|discriminate Hb]. injection Hb as <-. unfold lsh_run_ok in G.
      repeat (apply andb_prop in G as [G ?X]). apply Z.leb_le in G. apply Z.leb_le in X3. apply Z.ltb_lt in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
      cbn [cinst cell_ok] in Hc. rewrite (alit_sound p a0 a Ea), (wlit_sound p n n' En) in Hc. destruct Hc as [_ Hc]. rewrite !u64_lit in Hc by lia.
      specialize (Hc (z - a) ltac:(lia)). replace (a + (z - a)) with z in Hc by lia. exact Hc.
  Qed.

  #[using="rom_none"] Lemma lsh_lookup_ok : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pl,(0.$1.)Pz,$37.Pb,(19.&8.)P,(9.$:.(;.Vsegs,VM,)(<.$1.$:.(=.Vp,)R3.))P,(5.(6.(19.&8.))(57.R4.R3.)(8.(19.&8.)R2.))P,(2>.(38.+7???:000.R4.)(3:.R4.+800<4000.))(5.(6.(19.&8.))A1.VM,(32.&40.R5.)(8.(19.&8.)R4.))")
(* [comment removed for export] *).
  Proof.
    induction l as [|c r IH]; intros z b HF Hl Hz; [discriminate|]. cbn [map] in HF. inversion HF as [|c' r' Hc Hr]; subst.
    cbn [lsh_lookup] in Hl. destruct (lsh_cell_byte c z) as [b'|] eqn:E.
    - injection Hl as <-. exact (lsh_cell_byte_ok c z b' Hc E Hz).
    - exact (IH z b Hr Hl Hz).
  Qed.

  #[using="Type"] Lemma lsh_lookup_total : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pl,(0.$1.)Pz,$37.P,(58.$1.Lc,$1.(58.(19.&8.)Lv,(19.&8.)(2>.(59.$1.R2.R4.)(5.(6.(19.&8.))(56.R2.R3.)(8.(19.&8.)R1.)))))(58.(19.&8.)Lb,(19.&8.)(5.(6.(19.&8.))(57.R4.R3.)(8.(19.&8.)R1.)))")
(* [comment removed for export] *).
  Proof.
    induction l as [|c r IH]; intros z (c0 & v & Hin & Hv); [destruct Hin|]. cbn [lsh_lookup].
    destruct (lsh_cell_byte c z) as [b|] eqn:E; [exists b; reflexivity|].
    destruct Hin as [->|Hin]; [congruence|]. apply IH. exists c0, v. tauto.
  Qed.
End LowShadowGeneric.

(* [comment removed for export] *)
Definition LSH_LO : Z := 0x7fffa000.
Definition LSH_HI : Z := 0x800c3e00.
Definition img_shb (z : Z) : byte := match lsh_lookup CELLS_lowshadow z with Some b => b | None => Z_to_bv 8 0 end.

Lemma lowshadow_chain : chain (zsort (omap lsh_extent CELLS_lowshadow)) LSH_LO LSH_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lowshadow_rom_none : forall z, 0x7fffa000 <= z < 0x800c4000 -> seg_rom ASEGS (Z_to_bv 64 z) = None.
Proof.
  intros z Hz. apply (seg_rom_off_hull ASEGS BOTH asan_in_hull). rewrite u64_lit by lia.
  unfold in_hull. cbn [img_lo img_hi BOTH]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)
Theorem me_img_shadow : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pmem,P,(19.&40.)(6.(19.&8.))Pp,$15.P,(9.$:.(;.$36.R2.)(5:.R1.))Pz,$37.P,(2>.(38.$5;.R1.)(3:.R1.$5<.))(5.(6.(19.&8.))A1.R5.(32.&40.R2.)(8.(19.&8.)(5=.R2.)))")
(* [comment removed for export] *).
Proof.
  intros mem p HF z Hz. unfold img_shb.
  destruct (chain_sound _ _ _ z lowshadow_chain Hz) as (a & b & Hin & Hab).
  apply zsort_in in Hin. apply omap_in in Hin as (c & Hc & He).
  destruct (lsh_extent_byte c a b z He Hab) as [v Hv].
  destruct (lsh_lookup_total CELLS_lowshadow z (ex_intro _ c (ex_intro _ v (conj Hc Hv)))) as [b0 Hb0].
  rewrite Hb0. exact (lsh_lookup_ok ASEGS mem p lowshadow_rom_none CELLS_lowshadow z b0 HF Hb0 ltac:(unfold LSH_LO, LSH_HI in Hz; lia)).
Qed.

(* [comment removed for export] *)
Corollary me_img_shadow_granule : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "Pmem,P,(19.&40.)(6.(19.&8.))Pp,$15.P,(9.$:.(;.$36.R2.)(5:.R1.))Pg,$37.P,(2>.(38.+10000.(5>.+8.R1.))(3:.(5>.+8.R1.)+65?000.))(5.(6.(19.&8.))A1.R5.(32.&40.(3;.+7???8000.R2.))(8.(19.&8.)(5=.(3;.+7???8000.R2.))))")
(* [comment removed for export] *).
Proof. intros mem p HF g Hg. apply (me_img_shadow mem p HF). unfold LSH_LO, LSH_HI. lia. Qed.

(* [comment removed for export] *)
Fixpoint zforallb (f : Z -> bool) (z : Z) (n : nat) : bool :=
  match n with O => true | S n' => (f z && zforallb f (z + 1) n')%bool end.
Lemma zforallb_sound : forall f n z x, zforallb f z n = true -> z <= x < z + Z.of_nat n -> f x = true.
Proof.
  induction n as [|n IH]; intros z x H Hx; [lia|]. cbn [zforallb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec x z) as [->|Hne]; [exact H1|]. apply (IH (z + 1) x H2). lia.
Qed.
Definition cell_is_zero (c : ct) : bool := match c with TZero _ _ => true | _ => false end.
(* [comment removed for export] *)
Definition nz_clear (P : Z -> bool) (l : list ct) : bool :=
  forallb (fun c => if cell_is_zero c then true else
                     match lsh_extent c with
                     | Some (a, b) => zforallb (fun z => negb (P (z - 0x7fff8000))) a (Z.to_nat (b - a))
                     | None => true end) l.

Theorem me_img_shadow_zero : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "PP,P,$37.$3<.P,(5.$3<.(5?.R1.$60.)$61.)Pmem,P,(19.&40.)(6.(19.&8.))Pp,$15.P,(9.$:.(;.$36.R2.)(5:.R1.))Pg,$37.P,(5.$3<.A1.R6.R1.$61.)P,(2>.(38.+10000.(5>.+8.R2.))(3:.(5>.+8.R2.)+65?000.))(5.(6.(19.&8.))A1.R6.(32.&40.(3;.+7???8000.R3.))(8.(19.&8.)(32.&8.=)))")
(* [comment removed for export] *).
Proof.
  intros P HP mem p HF g Hg Hr.
  set (z := 0x7fff8000 + g). assert (Hz : LSH_LO <= z < LSH_HI) by (subst z; unfold LSH_LO, LSH_HI; lia).
  destruct (chain_sound _ _ _ z lowshadow_chain Hz) as (a & b & Hin & Hab).
  apply zsort_in in Hin. apply omap_in in Hin as (c & Hc & He).
  destruct (lsh_extent_byte c a b z He Hab) as [v Hv].
  pose proof (proj1 (forallb_forall _ _) HP c Hc) as HPc. cbn beta in HPc.
  destruct (cell_is_zero c) eqn:Zc.
  - (* [comment removed for export] *)
    destruct c as [a0 w v0|a0 n|a0 n c8|a0 n|a0 n|lo hi]; cbn [cell_is_zero] in Zc; try discriminate.
    cbn [lsh_cell_byte] in Hv. destruct (alit a0) as [a'|]; [|discriminate]. destruct (wlit n) as [n'|]; [|discriminate].
    destruct (lsh_run_ok a' n' z); [|discriminate]. injection Hv as <-.
    pose proof (proj1 (Forall_forall _ _) HF (cinst p (TZero a0 n)) (in_map _ _ _ Hc)) as Hcell.
    apply (lsh_cell_byte_ok ASEGS mem p lowshadow_rom_none (TZero a0 n) z (Z_to_bv 8 0) Hcell); [|unfold LSH_LO, LSH_HI in Hz; lia].
    cbn [lsh_cell_byte]. destruct (lsh_extent_byte (TZero a0 n) a b z He Hab) as [v' Hv']. cbn [lsh_cell_byte] in Hv'.
    destruct (alit a0) as [a''|]; [|discriminate]. destruct (wlit n) as [n''|]; [|discriminate].
    destruct (lsh_run_ok a'' n'' z); [reflexivity | discriminate].
  - (* [comment removed for export] *)
    rewrite He in HPc. pose proof (zforallb_sound _ _ a z HPc ltac:(lia)) as X. cbn beta in X.
    replace (z - 0x7fff8000) with g in X by (subst z; lia). rewrite Hg in X. discriminate X.
Qed.

(* [comment removed for export] *)
Section FromMain.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variables uid hw : word.

  #[using="Type"] Lemma Forall_app_l {X} (P : X -> Prop) (l1 l2 : list X) : Forall P (l1 ++ l2) -> Forall P l1.
  Proof. intros H. apply Forall_app in H. tauto. Qed.
  #[using="Type"] Lemma Forall_app_r {X} (P : X -> Prop) (l1 l2 : list X) : Forall P (l1 ++ l2) -> Forall P l2.
  Proof. intros H. apply Forall_app in H. tauto. Qed.

  #[using="Type"] Lemma main_entry_A_lowshadow : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "PR,(2<.&5.(19.&40.))Pmem,P,(19.&40.)(6.(19.&8.))Pmd,$62.P,(63.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vfs,Vuid,Vhw,R3.R2.R1.)(58.$15.Lp,$15.(2>.(16.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vuid,Vhw,R1.)(9.$:.(;.$36.R4.)(5:.R1.))))")
(* [comment removed for export] *).
  Proof.
    intros R mem md (p & HI & _ & _ & _ & HM). exists p. split; [exact HI|].
    destruct HM as (HC & _). unfold cells_common in HC.
    repeat match type of HC with
      | Forall _ (cells_lowshadow _ ++ _) => exact (Forall_app_l _ _ _ HC)
      | Forall _ (cells_lowshadow _) => exact HC
      | Forall _ (_ ++ _) => apply Forall_app_r in HC
      end.
  Qed.

  #[using="Type"] Theorem me_img_shadow_main : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "PR,(2<.&5.(19.&40.))Pmem,P,(19.&40.)(6.(19.&8.))Pmd,$62.P,(63.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vfs,Vuid,Vhw,R3.R2.R1.)Pz,$37.P,(2>.(38.$5;.R1.)(3:.R1.$5<.))(5.(6.(19.&8.))A1.R5.(32.&40.R2.)(8.(19.&8.)(5=.R2.)))")
(* [comment removed for export] *).
  Proof. intros R mem md H. destruct (main_entry_A_lowshadow R mem md H) as (p & _ & HF). exact (me_img_shadow mem p HF). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Theorem me_img_shadow_zero_main : ltac2:(CDefT.buildp (gd_tbl_AsanMainEntryLemmas ()) "PP,P,$37.$3<.P,(5.$3<.(5?.R1.$60.)$61.)PR,(2<.&5.(19.&40.))Pmem,P,(19.&40.)(6.(19.&8.))Pmd,$62.P,(63.Vsp,Vbrk0,Vrdraw,Vargv,Venvp,Vfs,Vuid,Vhw,R3.R2.R1.)Pg,$37.P,(5.$3<.A1.R7.R1.$61.)P,(2>.(38.+10000.(5>.+8.R2.))(3:.(5>.+8.R2.)+65?000.))(5.(6.(19.&8.))A1.R6.(32.&40.(3;.+7???8000.R3.))(8.(19.&8.)(32.&8.=)))")
(* [comment removed for export] *).
  Proof. intros P HP R mem md H. destruct (main_entry_A_lowshadow R mem md H) as (p & _ & HF). exact (me_img_shadow_zero P HP mem p HF). Qed.
End FromMain.

(* [comment removed for export] *)
Goal map (fun z => bv_unsigned (img_shb z)) [0x7fffc9a4; 0x7fffc9a5; 0x7fffc9a6; 0x7fffa000; 0x800c3dff] = [0; 2; 249; 0; 0].
Proof. vm_compute. reflexivity. Qed.
