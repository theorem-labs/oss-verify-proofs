(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Export RMallocRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4list04Npos35stdpp9bitvectorbdefinitionsk12bvhc4conshc3nil37Corelib5Lists7ListDefn03map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~od2wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~t43mem37Corelib4Init5Logichhd3and46Stdlib6ZArith6BinInt1Zhj82lehj83powhhd2exhj82lthj83addhhd2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~hn65rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hrc4cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ig08bytes_at69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~ik65hceil69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~ioa7hsecret79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~it24u64shrc2C8ig03le879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ji18rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~jm8aRAUXV_CELL89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree4HCW2~~~~~~jr8arauxv_listjr88rauxv_okhc4prodhc3sndhc3fsthc6optionhhd2orn06Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kk53ivlkk55munchkk55wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~kpa6mstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ku26PState3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsli8dmachine_statehc4unitkpa4aptrkpa5striphc4Somehc2ttt48pans_memt48pupd_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~lqa6rimplTkpa4cptrkpa4free79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpecaMallocCtrl~~~~~~mg76hdr_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~ml35implMku24bptrku24ps_mku28raw_freeku25set_mig02wahhd3nothc4Noneli85wviewjr8crpres_exceptkk57outsidehc6lengthhj86of_natig05wr_athrcacells_sizekk53stkkpa5rkindkpa6region01Njm84RCTXk17Z_to_bvk1bbv_unsigned25stdpp9countablenldbN_countable35stdpp7numbers1Nnnd6eq_decod5lr_lokpa6r_basekpa6r_kindkpa5r_lenkpabround_up_pgkpa9s_regions25stdpp4basent96lookup25stdpp4gmapnuf4gmapnufbgmap_lookupt4afresh_addrjm8cref_reservedkpaas_reservedhc4boolhc4truekpadalloc_ceilingkpablive_rangeskpabranges_free3h5LinuxProcessSemantics5Riscv7Preludeona5bvmapkpa4optrku25ps_faku25ps_sood2pwod8ticks_okt46am_relhrc2C4kk53mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ou92MSou96ret_pcig07mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~pk17seg_romjm85rmrepjr89ralloc_fpkpa7RKGroupt4bbrk_link_pskpa1Mjm8h1ralloc_meta_entryjr89RAM_STACKjr88ram_postkpaaalloc_metahj83sub" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)


Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition rimplT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM rsegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

Lemma rimplT_ret {R} o (r : R) s Q ms : evt rsegs (Q r s) ms -> rimplT o (SRet r) s Q ms.
Proof. try hcb. try hsb. intros H. unfold rimplT. rewrite mrun_ret. cbn [membed]. apply implM_ret. exact H. Qed.

Lemma rimplT_peek {R} o p c h (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (pans_mem o p c h)) s Q ms -> rimplT o (SVis (EPeek p c h) k) s Q ms.
Proof. try hcb. try hsb. intros H. unfold rimplT. rewrite mrun_peek. exact H. Qed.

Lemma rimplT_undef {R} o w (k : Z -> Malloc.M R) s Q ms : rimplT o (SVis (EUndef w) k) s Q ms.
Proof. try hcb. try hsb.
  unfold rimplT. rewrite mrun_vis by exact I. cbn [membed ev_step].
  eapply (implM_bind rsegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.

(* [comment removed for export] *)
Lemma rimplT_vis {R} o e (k : Z -> Malloc.M R) s Q1 Q ms :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  implM rsegs (ev_step e) s Q1 ms ->
  (forall z s' ms', Q1 z s' ms' -> rimplT o (k z) s' Q ms') ->
  rimplT o (SVis e k) s Q ms.
Proof. try hcb. try hsb.
  intros He H K. unfold rimplT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
  eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.

Lemma rimplT_mono {R} o (t : Malloc.M R) s Q Q' ms :
  rimplT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> rimplT o t s Q' ms.
Proof. try hcb. try hsb. intros H HQ. unfold rimplT in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.

Lemma rimplT_evt {R} o (t : Malloc.M R) s Q P ms :
  evt rsegs P ms -> (forall ms', P ms' -> rimplT o t s Q ms') -> rimplT o t s Q ms.
Proof. try hcb. try hsb. intros H K. unfold rimplT in *. eapply implM_evt; eauto. Qed.

(* [comment removed for export] *)
Lemma rimpl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
  impl rsegs (at_node rsegs) (Vis n k) Q ms = evt rsegs (fun ms1 => at_node rsegs n ms1 /\ forall rsp, impl rsegs (at_node rsegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. try hcb. try hsb. reflexivity. Qed.

Lemma rimpl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
  impl rsegs (at_node rsegs) (ITree.bind _ t f1) Q1 ms ->
  (forall r ms', impl rsegs (at_node rsegs) (f1 r) Q1 ms' -> impl rsegs (at_node rsegs) (f2 r) Q2 ms') ->
  impl rsegs (at_node rsegs) (ITree.bind _ t f2) Q2 ms.
Proof. try hcb. try hsb.
  revert ms. induction t as [r|n k IH]; intros ms H K; cbn [ITree.bind] in *.
  - apply K. exact H.
  - rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold. eapply evt_mono; [exact H|].
    intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.

(* [comment removed for export] *)
Lemma rmembed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
  strel RR t1 t2 ->
  forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
  implM rsegs (membed t1) s Q1 ms ->
  (forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof. try hcb. try hsb.
  induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
  - cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
  - cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1| exact HQ].
Qed.

Lemma rimplT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : Malloc.M R1) (t2 : Malloc.M R2) s Q1 Q2 ms :
  strel RR (mrun o t1) t2 ->
  rimplT o t1 s Q1 ms ->
  (forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
  implM rsegs (membed t2) s Q2 ms.
Proof. try hcb. try hsb.
  intros Hs H HQ. unfold rimplT in H. eapply (rmembed_strel _ _ _ Hs); [exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.

(* [comment removed for export] *)
Lemma rimplM_membed_steq {R} (t1 t2 : Malloc.M R) s Q ms :
  steq t1 t2 -> implM rsegs (membed t1) s Q ms -> implM rsegs (membed t2) s Q ms.
Proof. try hcb. try hsb.
  intros Hs H. apply strel_eq_steq in Hs. eapply (rmembed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.


Lemma rimplM_membed_sbind {R S} (T : Malloc.M R) (F : R -> Malloc.M S) s Q1 Q ms :
  implM rsegs (membed T) s Q1 ms ->
  (forall x s' ms', Q1 x s' ms' -> implM rsegs (membed (F x)) s' Q ms') ->
  implM rsegs (membed (sbind T F)) s Q ms.
Proof. try hcb. try hsb.
  revert s ms. induction T as [x|e k IH]; intros s ms H K.
  - cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
  - cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
    eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
    + exact H1.
    + eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
Lemma rimplT_bind {R S} o (t : Malloc.M R) (f : R -> Malloc.M S) s Q1 Q ms :
  rimplT o t s Q1 ms ->
  (forall r s' ms', Q1 r s' ms' -> rimplT o (f r) s' Q ms') ->
  rimplT o (sbind t f) s Q ms.
Proof. try hcb. try hsb.
  unfold rimplT, mrun, prun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
  - cbn [sbind]. cbn [eruns membed] in H. unfold implM, mret in H. cbn in H.
    eapply implM_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
  - cbn [sbind eruns]. cbn [eruns] in H. unfold pupd_mem in *. destruct (psel pans_mem o e) as [a|].
    + eapply IH; [exact H|exact K].
    + cbn [membed]. cbn [membed] in H. unfold implM, mbind, ebind in H |- *.
      eapply rimpl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
      * exact H1.
      * eapply IH; [exact H1|exact K].
Qed.

(* [comment removed for export] *)
Lemma rimplT_from_evt {R} o (t : Malloc.M R) s Q ms :
  evt rsegs (fun ms' => rimplT o t s Q ms') ms -> rimplT o t s Q ms.
Proof. try hcb. try hsb. intros H. eapply rimplT_evt; [exact H|]. intros ms' H'; exact H'. Qed.

End HCW.

Ltac riprefixT := apply rimplT_from_evt.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rimplM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
      (s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
  (forall a ms', P a ms' -> evt rsegs (Q (f a) s) ms') ->
  implM rsegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof. try hcb. try hsb.
  intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
  cbn [ITree.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec rsp) as [a|]; cbn in *.
  - eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
  - exact Hk.
Qed.


Lemma rimplT_mmap_rw {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
  rimplT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' nd_i1; ndestruct nd_i1 as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

Lemma rimplT_mmap_none {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mmap_val a)) s Q ms') ->
  rimplT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' nd_i2; ndestruct nd_i2 as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

Lemma rimplT_mmap_fixed {R} o addr len (k : Z -> Malloc.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (fixed_val addr a)) s Q ms') ->
  rimplT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
  - cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
    eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' nd_i3; ndestruct nd_i3 as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

Lemma rimplT_munmap {R} o addr len (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
  rimplT o (SVis (EMunmap addr len) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' nd_i4; ndestruct nd_i4 as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
Lemma rimplT_mprotect {R} o addr len prot (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (range_val a)) s Q ms') ->
  rimplT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - (intros z s' ms' nd_i5; ndestruct nd_i5 as (-> & a & -> & HP)). exact (K a ms' HP).
Qed.

(* [comment removed for export] *)
Lemma rimplT_brk0 {R} o (k : Z -> Malloc.M R) s (P : Z -> machine_state -> Prop) Q ms :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
  (forall r ms', P r ms' -> rimplT o (k r) (set_brk_ps r s) Q ms') ->
  rimplT o (SVis (EBrk 0) k) s Q ms.
Proof. try hcb. try hsb.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
  - cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
    cbn [ITree.bind]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
    eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
  - intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.

(* [comment removed for export] *)
Lemma rimplT_brk {R} o req (k : Z -> Malloc.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
  req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
  (forall a ms', P a ms' ->
     rimplT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
             (match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
  rimplT o (SVis (EBrk req) k) s Q ms.
Proof. try hcb. try hsb.
  intros Hr H K.
  eapply (rimplT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
            z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
            s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
  - cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
    unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
    cbn [ITree.bind fst snd]. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
    eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
    destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
    destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
  - (intros z s' ms' nd_i6; ndestruct nd_i6 as (a & HP & -> & ->)). exact (K a ms' HP).
Qed.


Lemma rimplT_reach {R} o (t : Malloc.M R) : forall s Q ms,
  rimplT o t s Q ms -> rimplT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof. try hcb. try hsb.
  induction t as [r|e k IH]; intros s Q ms H.
  - unfold rimplT, implM in *. rewrite mrun_ret in *. cbn [membed] in *. unfold mret in *. cbn in *.
    eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply leaf_of_ret].
  - destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
    5:{ apply rimplT_peek. eapply rimplT_mono; [apply IH; unfold rimplT in H |- *; rewrite mrun_peek in H; exact H|].
        cbn. intros r s' ms' [HQ HL]. split; [exact HQ|]. apply leaf_of_peek. exact HL. }
    5:{ apply rimplT_undef. }
    all: unfold rimplT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
         unfold implM, mbind, ebind in H |- *;
         eapply rimpl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
         pose proof (IH z s' Q ms') as IH1; unfold rimplT, implM in IH1;
         eapply impl_epost_mono; [apply IH1; exact H1|];
         intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (leaf_of_vis o _ k z); [exact I| exact HL]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition rauxv_list : ltac2:(zQ "40!h9!j4!jb!le>2x3$0>2x4$0>2x5$0>3x16$0>2x6$0>3x11$0>3x12$0>3x23$0>3rnd$0@1$1@1$3@1$2#k0") := ltac2:(zQ "70!h9!m3!ma!o7!jb!sf!le\2x3$0\2x4$0\2x5$0\3x16$0\2x6$0\3x11$0\3x12$0\3x23$0\3rnd$0@4$3$0@1$6@1$4#k0$5@3$1$0+3@3$1$0^9@3$1$0+4@3$1$0^8@3$1$0+5@3$1$0^7@3$1$0+h0@3$1$0^6@3$1$0+6@3$1$0^5@3$1$0+b@3$1$0^4@3$1$0+c@3$1$0^3@3$1$0+h7@3$1$0^2@3$1$0+h9@3$1$0^1@3$1$0Z@3$1$0Z@1$2$0").

Definition rauxv_ok : ltac2:(zQ "20!h9!hh7>1m$1>1B$0P") := ltac2:(zQ "h70!hj1!h9!hl0!hl6!hld!hm3!hm9!hn0!hr3!sf!hv8!ija!m3!ma!hh7!io1!is7!jgc!jh4!jha!jlc!jqa!kg0\1m$e\1B$1@2$4$1\2av$1@2$4$1\2x3$1@2$4$1\2x4$1@2$4$1\2x5$1@2$4$1\3x16$1@2$4$1\2x6$1@2$4$1\3x11$1@2$4$1\3x12$1@2$4$1\3x23$1@2$4$1\3rnd$1@2$0@4$h4$8^c$h5@3$c$a@1$h2@1$9^a@1$d$a@2$0@4$b$8^c^a@1$h1@9$h6^9^8^7^6^5^4^3^2^1@2$0@4$b$8^c@2$6^1+8@1$h3@1$9@1$h0?4HSEC@2$0@2$2@1$f?5HCEIL^b@2$0@2$2^b^a@2$0@2$2@2$6^a+q0@2$3+2+k0@2$0@2$2^b@2$6^1+8@2$0@2$2@2$6^1+h0@2$3+2+k0@2$0@2$0@2$2Z^9@2$5^9@2$3+2+k0@2$0@2$0@2$2Z^8@2$5^8@2$3+2+k0@2$0@2$0@2$2Z^7@2$5^7@2$3+2+k0@2$0@2$0@2$2Z^6@2$5^6@2$3+2+k0@2$0@2$0@2$2Z^5@2$5^5@2$3+2+k0@2$0@2$0@2$2Z^4@2$5^4@2$3+2+k0@2$0@2$0@2$2Z^3@2$5^3@2$3+2+k0@2$0@2$0@2$2Z^2@2$5^2@2$3+2+k0@2$0@2$0@2$2Z^1@2$5^1@2$3+2+k0@2$0@3$7$1^9+hggk0@2$0@3$7$1^8+j8@3$7$1^7+a").

Lemma rauxv_ok_weaken : ltac2:(zQ "60!h9!kge!hl0!hj1!hh7!io1>1m$4>1B$0>2B'$0>0@2$1^3^2>0@2$3@2$2@1$5?5HCEIL^2@2$2^2^3@2$1^5^3").
Proof. try hcb. try hsb.
  (intros m B B' nd_i9 HB; ndestruct nd_i9 as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & H)).
  nexists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. repeat (split; [tauto|]). lia.
Qed.

Lemma rauxv_ok_frame : ltac2:(zQ "h40!h9!hl0!kha!ki1!jb!jqa!kge!le!ki7!j4!kid!hj1!kj6!kjc!hh7!ko1!ko8!kp1!hr3!hm9>1m$e>2m'>0@1$7@1$4#k0@1$a@1$7@1$4#8>1B$0>1W@1$9$f>0@2$6^4^2>0@3$h0^2^5^4>0@3$h1$h2^6^5>0@3$d@2$2$0$0\2iv@2$2$0$0@2$b@2$1@3$3$0$0^1^6@2$c@2$1@3$3$0$0^1$5@2$1@2$h3$5+8@3$8$0$0^1^4@2$6^7^6").
Proof. try hcb. try hsb.
  (intros m m' B W nd_i10 MU WM FW; ndestruct nd_i10 as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H)).
  nexists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rw_cells_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [_ ?]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
  - eapply bytes_at_transport; eauto. eapply Forall_disjoint_from; [exact FW|]. cbn. intros lo hi [? _]. lia.
Qed.

(* [comment removed for export] *)
Lemma rraw_free_bridge : ltac2:(zQ "h80!kt8!lhe!llf!ln0!hh7!ln7!lnf!lo8!ki7!lof!hn0!h9!lp4!lpf!lud!hr3!lv7!lvf!mk9!mp0!mp9!mq1!mq9!mr5>2st$0>1s$1>1p$h4>2pf$5>1o$4>2Q1>0$0>0$1>0$2P>1Q>1x$3>2x0$1>2x1$2P>2ms$2>0@3$a$0@1$6^8@1$h5^7>0@6$h2$4$c$d^9^6@3$8$h0$b^7>0@7$e?5HCEIL$0^6@2$h1^a@2$7$5^7^9^5^3>0>3st'$0>2s'$1>3ms'$2>0@3^9^3^2^1@3^9$9@2$h7@1$6^4^3^2@7$h3$1$f$3@2$h6?5HCEIL^a^b^6^5").
Proof. try hcb. try hsb.
  intros st s p pf o Q1 Q ms Hst Hh H HQ. unfold raw_free.
  eapply (implM_bind rsegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
  { apply implM_get. apply evt_done. repeat split; reflexivity. }
  (intros s0 s1 ms1 nd_i11; ndestruct nd_i11 as (-> & -> & ->)). cbv beta.
  eapply (implM_bind rsegs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
  { rewrite <- Hst. eapply (rimplT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
    - unfold mrun. apply free_control. exact Hh.
    - exact H.
    - intros o1 st' cs s' ms' HR H1. exists st'. split; [exact H1|]. unfold FREL in HR. exact HR. }
  (intros cs s' ms' nd_i12; ndestruct nd_i12 as (st' & H1 & <-)). cbv beta.
  apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rpres_except : ltac2:(zQ "20!hh7!h9>1C>0$1P>1m$0>2m'$0P") := ltac2:(zQ "f0!jb!le!mre!kid!hn0!ms4!msb!hj1!h9!mt2!hh7!hr3!hl0!hm3!hl6\1C>0$8P\1m$a\2m'$a>1a$8>0@2$7@2$cZ^1@2$d^1@2$e+2+k0>0@1$5@1^5^2@2$7@3$4@1$3@1$1@1$0#8@1^4@1$2^3@1^5@1$2^3>0@1$5@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^3@1$6@1$1@1$0#8@1$5@3$4@1$3@1$1@1$0#8@3$9$b^5@1$2^4@1$6@1$1@1$0#8").

Lemma rpres_except_refl : ltac2:(zQ "30!h9!hh7!mtb>1C>0$0P>1m$1@3$2^2^1^1").
Proof. intros C m. try hcb. try hsb. intros a _ _; auto. Qed.
Lemma rpres_except_trans : ltac2:(zQ "30!hh7!mtb!h9>1C>0$2P>2m1$0>2m2$0>2m3$0>0@3$1^4^3^2>0@3$1^5^3^2@3$1^6^5^3").
Proof. intros C m1 m2 m3. try hcb. try hsb. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma rpres_except_mono : ltac2:(zQ "30!h9!hh7!mtb>1C>0$0P>2C'>0$0P>1m$1>2m'$1>0@3$2^4^2^1>0>1a$0>0@1^6^1@1^6^2@3$2^5^4^3").
Proof. intros C C' m m'. try hcb. try hsb. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.

(* [comment removed for export] *)
Lemma rpres_except_of_munch : ltac2:(zQ "h01!jb!le!kid!h9!j4!hj1!ms4!ko1!ko8!mub!kp1!mtb!hr3!hl0!hm3!hl6&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1C>1x$3P>1W@1$4$7>1m~0>2m'~0>0@3$8^3^2^1>0@3$a$c^3^2>0>1a$3>0@2$5@2$dZ^1@2$e^1@2$f+2+k0>0@1$6@1^8^2@2$9^8^3@3$b^7^5^4").
Proof. intros C W m m'. try hcb. try hsb.
  intros MU WM HW a Ha Hc. split.
  - apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
  - apply WM.
Qed.

Lemma rpres_except_bytes_at : ltac2:(zQ "f0!h9!jb!hh7!ija!hr3!le!mv6!j4!hj1!ms4!mtb!hm9!hl0!hm3!mvf>1C>0$0P>1m$2>2m'$2>1A$0>2bs@1$7@1$5@1$1#8>0@3$a^5^4^3>0@4$3$4^5^3^2>0>1a$0>0@2$8@2$c^5^1@2$d^1@2$b^5@1$e@2$6@1$5@1$1#8^4@1$9@1^9^2@4$3$4^6^5^4").
Proof. intros C m m' A bs. try hcb. try hsb.
  (intros HP nd_i13 HR; ndestruct nd_i13 as (H0 & H1 & HB)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (HB i Hi). unfold mrd.
  destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.

Lemma rpres_except_wr_at : ltac2:(zQ "a0!h9!hh7!ng9!hr3!hj1!ms4!mtb!hm9!hl0!hm3>1C>0$0P>1m$1>2m'$1>1A$0>1n$0>0@3$6^5^4^3>0@4$2$3^5^3^2>0>1a$0>0@2$4@2$8^5^1@2$9^1@2$7^5^4@1$5@1^9^2@4$2$3^6^5^4").
Proof. intros C m m' A n. try hcb. try hsb.
  (intros HP nd_i14 HR; ndestruct nd_i14 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.

Lemma rpres_except_rw_cells : ltac2:(zQ "e0!h9!hh7!jlc!hr3!j4!hj1!ms4!hv8!nh2!mtb!hm9!hl0!hm3!mvf>1C>0$0P>1m$1>2m'$1>1A$0>2cs@1$4$7>0@3$9^5^4^3>0@4$2$3^5^3^2>0>1a$0>0@2$5@2$b^5^1@2$c^1@2$a^5@1$d@1$8^4@1$6@1^9^2@4$2$3^6^5^4").
Proof. intros C m m' A cs. try hcb. try hsb.
  intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply rpres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
  - eapply rpres_except_wr_at; eauto.
Qed.

Lemma rpres_except_stk : ltac2:(zQ "90!h9!hh7!ni0!hr3!hj1!ms4!mtb!hl0!hm3>1C>0$0P>1m$1>2m'$1>2lo$0>2hi$0>0@3$6^5^4^3>0@4$2$3^5^3^2>0>1a$0>0@2$4@2$7^5^1@2$8^1^4@1$5@1^9^2@4$2$3^6^5^4").
Proof. intros C m m' lo hi. try hcb. try hsb.
  (intros HP nd_i15 HR; ndestruct nd_i15 as (H0 & H1 & HW)). split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
  split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
Definition ralloc_fp : ltac2:(zQ "30!h9!kt8!ni7>1K>0$2P>3st1$1>2lo$0>2sp$0>1a$0P") := ltac2:(zQ "hd2!nj0!hj1!nja!hm9!jb!hl0!hm3!kj6!h9!hld!njd!nk5!nkf!nme!noe!lo8!kid!hn0!np8!kt8!nq0!nqa!nr4!ni7!nrd!nsc!nu5!nvb!og3&@2$c@1$4#k0@2$b@1$4#k0+hgurv8&@2$3~0-q4\1K>0$h7P\3st1$h3\2lo$8\2sp$8\1a$8@2$7@2$1@2$5^3^1@2$6^1^2@2$7@2$1@2$5~1^1@2$6^1@2$3~1+4@2$7@2$1@2$5$a^1@2$6^1@2$3$a+jq0@2$9$2\3rid$2@2$9$0\1r$0@2$1@3$h1@1$h0$0@6$ha$2$0@4$hb$2$e$d$0@4$hc$2$e$d$0^2@1$h9^6@2$f$0^1@2$1@1^7@1$h5^1@2$1@2$5@1$h2^1^3@2$6^3@2$3@1$h4^1@1$h8@1$h6^1").
  (* [comment removed for export] *)

Definition RAM_STACK : Z := 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rfresh_image : ltac2:(zQ "b0!h9!j4!kha!hn0!kj6!oh2!ohf!kt8!oif!hl0!hm3>2st$7>1a$0>0@2$5^2^1>0@3$3@1$1@2$2$0$0@1$8^3@1$6?5HCEIL@2$4@2$a^3+hggg0@2$9+hjhgg0^3").
Proof. intros st a. try hcb. try hsb.
  intros [_ FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; right; right; right; right; left; reflexivity)). lia.
Qed.

(* [comment removed for export] *)
Lemma rfresh_below : ltac2:(zQ "a0!h9!j4!kha!hn0!oh2!io1!ohf!kt8!oif!hm3>2st$7>1a$0>0@2$4^2^1>0@3$3@1$1@2$2$0$0@1$8^3@1$6?5HCEIL@2$9^3@1$5?5HCEIL").
Proof. intros st a. try hcb. try hsb.
  intros [C FR] RS. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)) as X.
  cbv delta [Decode.CEIL_BAND Malloc.alloc_ceiling Decode.alloc_ceiling] in X, C. hcb. lia.
Qed.

(* [comment removed for export] *)
Lemma rlive_below : ltac2:(zQ "f0!h9!hl0!hn0!hm9!ojd!j4!kha!ok4!io1!ohf!okb!olc!kt8!omb!oif>2st$c>1b$0>1n$0>0@3$2@1$5@2$6$0$0@1$e^3@1$9?5HCEIL>0@3$2$4@3$d@1$b^4^3^2$7>0@2$1Z^3>0@2$1@2$3^5^4$a@2$1@2$3^6^5@1$8?5HCEIL").
Proof. intros st b n. try hcb. try hsb.
  intros RS FR Hn Hc. unfold live_ranges in FR. rewrite RS in FR.
  pose proof (ranges_free_In _ _ _ _ _ FR ltac:(apply in_or_app; left; left; reflexivity)) as X.
  cbv delta [Malloc.alloc_ceiling CEIL_BAND] in X, Hc. hcb. lia.
Qed.

Definition ram_post : ltac2:(zQ "90!jb!le!kt8!lhe!h9!llf!oq0!hh7!oq9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2st$2>1s$3>2lo$4>1m$7>3st1$2>2mo$8>2s'$3>0$5P") := ltac2:(zQ "id1!jb!le!hld!hj1!hn0!h9!hr3!nkf!kt8!kid!llf!hv8!ni7!lhe!or1!mq1!ora!msb!m3!ma!kha!ln0!ms4!kj6!oq0!os3!os8!ot3!oh2!hh7!otc!ou2!ni0!pi6!pic!pj6!po0!jlc!pob!pp4!kge!mtb!pq1!oq9!hm9&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h8@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2st$8\1s$d\2lo$5\1m$hd\3st1$8\2mo$ib\2s'$d\3ms'$a@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$1@1$0#k0\5errv'@1$1@1$0#k0@2$3@3$4$a^h1@7$i1@hf$hf^ia^i9^i8^i7^h0^f^e^i6^i5@2$h9^h4^h3^d^c^b^a^9^8^7^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@1$i2^ia^h9@1$h1@1$1@1$0#k0^2@1$i4$6@2$3@2$i3$6^2@2$3@4$i0$6^2^h6@2$7@1$0#k0^i9@2$3@4$i5$6^2@2$ic@2$7@1$0#k0^i7-q4@3$h2$b@1$he^1@1$h3$b@2$3@2$i8^2@2$7@1$0#k0^i9@2$3@3$i9\1a$5@2$h7@5$i7\1k$c@1$h6@3$4$c^1$ia^h5^h7@2$7@1$0#k0^ia^1@2$hc^h9^1^h5^2@2$3@4$i6?5HCEIL?4HSEC^h4^2@2$3@1$ha^h4@2$3@3$4$8@1$f^h2@1$f^h7@2$3@3$4@2$h4$5$5@1$e^h2@1$e^h7@2$3@3$4$h5@1$h0^h2@1$h0^h7@3$hb^h8^h4^h3").

(* [comment removed for export] *)
Definition ralloc_meta_stmt : ltac2:(zQ "10!kt8>6am_pre>0$0PP") := ltac2:(zQ "i60!jb!le!hr3!kt8!nkf!lhe!llf!pqc!hh7!hv8!lud!pra!oq9!hl0!nk5!msb!m3!ma!hn0!h9!oq0!os8!io1!otc!ou2!ni0!pi6!pj6!po0!jlc!prf!pob!pt5!pu2!kge!pue!hm9!pvc\6am_pre>0$3P>1RT>1k>0$3>0$c@1$b^3>4bail@1$b^2>1o$8>1s$5>1Q>0^5>0$5>0$6P>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$8>2st$3>2lo$h3>4errv@1$1@1$0#k0>0@1^ic^3>0@4$hf?5HCEIL?4HSEC^4^5>0@1$h5^5>0@2$7^6^ia>0@2$i2^8@2$4@1$0#k0^i8>0@4$h9$2^9^7@2$4@1$0#k0^i9>0@2$d@1$h6?5HCEIL^8>0@2$d^9@2$i5@2$4@1$0#k0^ib$i0>0@4$hd$2^c@2$i4@2$4@1$0#k0^ia-q4@3$h0$9@1$h7^9@1$h1$9>0@2$hb$2^d>0@3$h2@1$1@1$0#k0^ic@2$e@1$0#k0+hgurv8>0>3st1$3>2mo$c>2s'$5>3ms'$6>0@ha$i1^j4^j3^j2^j1^id^ic^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h5^h4^h2^j6^h1^h3^4^3^2^1>0@2$7^5^3@7$a?5HCEIL^jc^j9@2^jb^6^5^4^j7^3@7$a?5HCEIL^j7^j4@4$i3^j7^f^j6^j5^j3^j2@7$ha@hf$h8^j1^j0^if^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2@2$e@1$0#k0$he^h1@1$f@1$1@1$0#k0^h0@1$hc$2").

End HCW2.

(* [comment removed for export] *)
