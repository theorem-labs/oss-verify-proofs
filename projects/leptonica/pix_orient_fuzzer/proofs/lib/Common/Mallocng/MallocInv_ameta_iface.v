(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_MallocInv_ameta_iface () := "C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C69OSSVerify5KrLib6Common8Mallocng:MallocTree5ms_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs3domC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs7a_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init5Logic2eq00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC4ELinuxProcessSemantics?LinuxProcessSem5State=vm_live_bytesk69OSSVerify5KrLib6Common8MallocngEMallocInv_ameta_iface4AMvm01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib6Common8Mallocng>MallocInv_defs6astate00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common8Mallocng:MallocTree6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01".
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition UsOK (A : astate) : Prop :=
  forall sc, 0 <= sc < 48 -> a_ctx A (KUsage sc) = usage_of A sc.

(* [comment removed for export] *)
Definition spare (A : astate) : Z :=
  a_ctx A KAmc + Z.of_nat (length (a_freelist A)).

Record II (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
          (A : astate) (s : mstate) : Prop := {
  ii_is : IS sp0 argv envp cb A s;
  ii_vm : VMok A (ms_vm s);
  ii_av : AvOK A;
  ii_us : UsOK A;
  ii_dd : deads A D
}.

Global Arguments ii_is {sp0 argv envp cb D A s} _.
Global Arguments ii_vm {sp0 argv envp cb D A s} _.
Global Arguments ii_av {sp0 argv envp cb D A s} _.
Global Arguments ii_us {sp0 argv envp cb D A s} _.
Global Arguments ii_dd {sp0 argv envp cb D A s} _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record AMvm (A A' : astate) (s s' : mstate) : Prop := {
  amv_maps : forall b sz, In (b, sz) (vm_maps (ms_vm s)) -> In (b, sz) (vm_maps (ms_vm s'));
  amv_acc : forall b sz, In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true -> region_free (vm_noaccess (ms_vm s')) b sz = true;
  amv_newdom : forall x b sz, dom A' x -> ~ dom A x -> In (b, sz) (vm_maps (ms_vm s)) ->
    region_free (vm_noaccess (ms_vm s)) b sz = true ->
    ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned sz);
  amv_budget : a_areas A = [] -> vm_live_bytes (ms_vm s') <= vm_live_bytes (ms_vm s) + 12288
}.

Lemma AMvm_refl : forall A s, AMvm A A s s.
Proof.
ltac2:(KReplay.run1 (kr_t_MallocInv_ameta_iface ()) ["WithLayout"] "h01Hh11bh22szh32H0h44__x1h51Ah62H1h72H2h82H3h97__arithh:4__ffh;8__varmaph<5__with=1sh>1xp;1p;2p;4p;3p;7p;8p-1g0000R0p4p710p8g000Gj1WTg000ej1PTg001Hj2DTg001hj4@Tg002Hj11Tg003Mj1:TP0j34Tg004Cj15Tg005=j36Tg0067j2>Tg007>j19Tg007Wj2?Tg008Aj2=Tg008]j2<Tg009:j2VTg009Vj2UTg00:1j1;Tg00:Qj1TTg00;\j18Tg00<<j33Tg00<Vj2OTg00=4j1NTg00=Rj1KTg00>=j2FTg00>`j1GTg00?Ej1HTg00?cj2ETg00@Fj3ITg00@ij4JTg00ATj7CTg00B8j2LTg00BZj2MTg00C4j2BTg00C`j3QTg00D?j4RTg00E1j1ATg00Emj8STg00G>j17Tf0R0#7#7p=0g00GcR1g00HCR2730p=2g00Hcg00Iof1R3P3P0P0g00K7R4#0#0#0#WR5#PR61D66R7P6P6P3P0C@f2R8#1R9#:34R:P0W0X26W1f3R;#1#5?683#2P0W3X0:X26X16g00K\R:f4R</>8f5R=/>;#9P6P6P;P8C@%1=#:547f6R7#1#5?6<;#21?5=R=/=71?5<,<=,V7'UR7P;P<O1W8%97eW7W6W3W0X26X16W>%;:%T3%8:33g00L:R6#8%;61O:3%N:%K:R6g00Lfg00MER7P7g00MeR7P:1F:4R<g00NE%G4#0#0#0#0#0#0#HR4,E:9I:<CJg00NlFC1L67P0P81M121B08#2dg00OL=Q:3CRb:b;b<X4:1<04,=0^4:P0%A9O1b9UGSW=W5o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_budget (A : astate) (s : mstate) : Prop :=
  0 < spare A \/
  (vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) /\
   (0 < a_ctx A KAac \/ (a_areas A = [] /\ exists a, grant_ok_na_vm (ms_vm s) a 8192 = true))).
(* [comment removed for export] *)

Definition alloc_meta_spec : Prop :=
  forall (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> gsame A A' -> AMvm A A' s s' ->
       spare A = 0 -> a_areas A' = a_areas A ->
       (W = WOk -> ~ am_budget A s) ->
       tsall W (K (Z_to_bv 64 0) s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (m : Z),
       II sp0 argv envp cb (m :: D) A' s' -> FR A s A' s' -> got_meta A D A' m -> AMvm A A' s s' ->
       ((0 < spare A /\ ms_vm s' = ms_vm s /\ a_areas A' = a_areas A /\ spare A' = spare A - 1)
        \/ (spare A = 0 /\ a_areas A' = a_areas A ++ [m - 24] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])) ->
       tsall W (K (Z_to_bv 64 m) s') P) ->
    tsall W ((x <- m_alloc_meta sp ;; K x) s) P.

End WithLayout.
