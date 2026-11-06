(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent Require Import F_syscalls MallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SecKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__CJ_Agent_MallocTree () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Lists.ListDef."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.F_syscalls."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocRep."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree.CEIL_WRAP_1."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Agent.MallocTree.CEIL_WRAP_2."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Cells."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Frame."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Mem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Lib.Step."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Malloc."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.MallocCtrl."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Monad."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Spec.Prog."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.base."; "stdpp.bitvector.definitions."; "stdpp.countable."; "stdpp.gmap."; "stdpp.numbers.N."], [["0A"; "0C"; "0C'"; "1Some"; "1bool"; "1fst"; "1length"; "1list"; "1option"; "1pair"; "1prod"; "1snd"; "1true"; "1tt"; "1unit"; "2and"]; ["2eq"; "2ex"; "2not"; "2or"; "3Forall"; "4N"; "4Z"; "5machine_state"; "0P"; "0P'"; "0Q"; "0Q1"; "0RUNp"; "6asegs"; "7lr_lo"; "9mem"]; ["9pans_mem"; ":fresh_addr"; ":pres_except"; ":ptr_rel"; ":ptrs_in"; "8implT"; "8mem"; "8pans_mem"; "8pupd_mem"; ";cell"; ";cells_size"; "<disjoint_from"; "<ivl"; "<munch"; "<outside"; "<stk"]; ["<wmono"; "=bytes_at"; "=wr_at"; ">rw_cells"; "?aptr"; "?cptr"; "?free"; "?live_ranges"; "?malloc"; "?mstate"; "?optr"; "?r_base"; "?r_kind"; "?r_len"; "?ranges_free"; "?region"]; ["?region_live_range"; "?rkind"; "?round_up_pg"; "?s_regions"; "?s_reserved"; "?strip"; "@hdr_ok"; "AimplM"; "BPState"; "Bbptr"; "Bfresh_off"; "Bps_m"; "Braw_free"; "Braw_malloc"; "Bset_m"; "CIn"]; ["Dadd"; "Dle"; "Dlt"; "Dof_nat"; "Dpow"; "0W"; "0a"; "0a'"; "0b"; "0bs"; "0c"; "0cs"; "0h"; "0hi"; "0k"; "0l"]; ["0lo"; "0m"; "0m'"; "0m1"; "0m2"; "0m3"; "0ms"; "0ms'"; "0n"; "0n'"; "0o"; "0p"; "0pf"; "0q"; "0r"; "0r'"]; ["0rid"; "0s"; "0s'"; "0st"; "0st'"; "Elookup"; "Fbv"; "GN_countable"; "Hgmap"; "Hgmap_lookup"; "Ieq_dec"; "0x"; "0x0"; "0x1"]]).
Section CEIL_WRAP_1.
Context {RUNp : RunP}.
Definition mem := word -> option byte.
Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
match mrd asegs o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.
Lemma pans_mem_range : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "E&O&QD'F'?&RAz&Q0r4r3r2r1%544321%8271&RB+X0%2241%=241pUJ?1pUF@1pVLB1pVFD1").
Proof.
intros. unfold pans_mem. destruct (mrd asegs o (wa c)) as [b|]; [|lia].
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.
Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
match e with EPeek _ _ _ => False | _ => True end ->
mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.
Definition implT {R} (o : mem) (t : Malloc.M R) (s : PState)
(Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
implM asegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.
Lemma implT_ret {R} o (r : R) s Q ms : evt asegs (Q r s) ms -> implT o (SRet r) s Q ms.
Proof. intros H. unfold implT. rewrite mrun_ret. cbn [membed]. apply implM_ret. exact H. Qed.
Lemma implT_peek {R} o p c h (k : Z -> Malloc.M R) s Q ms :
implT o (k (pans_mem o p c h)) s Q ms -> implT o (SVis (EPeek p c h) k) s Q ms.
Proof. intros H. unfold implT. rewrite mrun_peek. exact H. Qed.
Lemma implT_undef {R} o w (k : Z -> Malloc.M R) s Q ms : implT o (SVis (EUndef w) k) s Q ms.
Proof.
unfold implT. rewrite mrun_vis by exact I. cbn [membed ev_step].
eapply (implM_bind asegs _ _ _ (fun _ _ _ => False)); [apply implM_unr|]. intros ? ? ? [].
Qed.
Lemma implT_vis {R} o e (k : Z -> Malloc.M R) s Q1 Q ms :
match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
implM asegs (ev_step e) s Q1 ms ->
(forall z s' ms', Q1 z s' ms' -> implT o (k z) s' Q ms') ->
implT o (SVis e k) s Q ms.
Proof.
intros He H K. unfold implT. rewrite mrun_vis by (destruct e; auto). cbn [membed].
eapply implM_bind; [exact H|]. intros z s' ms' H1. apply (K z s' ms' H1).
Qed.
Lemma implT_mono {R} o (t : Malloc.M R) s Q Q' ms :
implT o t s Q ms -> (forall r s' ms', Q r s' ms' -> Q' r s' ms') -> implT o t s Q' ms.
Proof. intros H HQ. unfold implT in *. eapply implM_mono; [exact H|]. intros [o' r] s' ms'; cbn; auto. Qed.
Lemma implT_evt {R} o (t : Malloc.M R) s Q P ms :
evt asegs P ms -> (forall ms', P ms' -> implT o t s Q ms') -> implT o t s Q ms.
Proof. intros H K. unfold implT in *. eapply implM_evt; eauto. Qed.
Lemma impl_vis_unfold {R} n (k : resp -> itree node R) Q ms :
impl asegs (at_node asegs) (Vis n k) Q ms = evt asegs (fun ms1 => at_node asegs n ms1 /\ forall rsp, impl asegs (at_node asegs) (k rsp) Q (nret ms1 rsp)) ms.
Proof. reflexivity. Qed.
Lemma impl_bind_mono {A B C} (t : itree node A) (f1 : A -> itree node B) (f2 : A -> itree node C) Q1 Q2 ms :
impl asegs (at_node asegs) (ITree.bind _ t f1) Q1 ms ->
(forall r ms', impl asegs (at_node asegs) (f1 r) Q1 ms' -> impl asegs (at_node asegs) (f2 r) Q2 ms') ->
impl asegs (at_node asegs) (ITree.bind _ t f2) Q2 ms.
Proof.
revert ms. induction t as [r|n k IH]; intros ms H K; cbn [ITree.bind] in *.
- apply K. exact H.
- rewrite impl_vis_unfold in H. rewrite impl_vis_unfold. eapply evt_mono; [exact H|].
intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. eapply IH; eauto.
Qed.
Lemma membed_strel {R1 R2} (RR : R1 -> R2 -> Prop) (t1 : Malloc.M R1) (t2 : Malloc.M R2) :
strel RR t1 t2 ->
forall s (Q1 : R1 -> PState -> machine_state -> Prop) (Q2 : R2 -> PState -> machine_state -> Prop) ms,
implM asegs (membed t1) s Q1 ms ->
(forall r1 r2 s' ms', RR r1 r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM asegs (membed t2) s Q2 ms.
Proof.
induction 1 as [r1 r2 Hr | e k1 k2 Hk IH]; intros s Q1 Q2 ms H HQ.
- cbn [membed] in *. unfold implM, mret in *. cbn in *. eapply evt_mono; [exact H|]. intros ms' H1. eapply HQ; eauto.
- cbn [membed] in *. unfold implM, mbind in *. unfold ebind in *.
eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ exact H1.
+ eapply IH; [exact H1| exact HQ].
Qed.
Lemma implT_strel {R1 R2} (RR : mem * R1 -> R2 -> Prop) o (t1 : Malloc.M R1) (t2 : Malloc.M R2) s Q1 Q2 ms :
strel RR (mrun o t1) t2 ->
implT o t1 s Q1 ms ->
(forall o1 r1 r2 s' ms', RR (o1, r1) r2 -> Q1 r1 s' ms' -> Q2 r2 s' ms') ->
implM asegs (membed t2) s Q2 ms.
Proof.
intros Hs H HQ. unfold implT in H. eapply (membed_strel _ _ _ Hs); [exact H|]. intros [o1 r1] r2 s' ms'; cbn; eauto.
Qed.
Lemma implM_membed_steq {R} (t1 t2 : Malloc.M R) s Q ms :
steq t1 t2 -> implM asegs (membed t1) s Q ms -> implM asegs (membed t2) s Q ms.
Proof.
intros Hs H. apply strel_eq_steq in Hs. eapply (membed_strel eq t1 t2 Hs); [exact H|]. intros; subst; auto.
Qed.
Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.
Lemma implM_membed_sbind {R S} (T : Malloc.M R) (F : R -> Malloc.M S) s Q1 Q ms :
implM asegs (membed T) s Q1 ms ->
(forall x s' ms', Q1 x s' ms' -> implM asegs (membed (F x)) s' Q ms') ->
implM asegs (membed (sbind T F)) s Q ms.
Proof.
revert s ms. induction T as [x|e k IH]; intros s ms H K.
- cbn [sbind membed] in *. unfold implM, mret in H. cbn in H. eapply implM_evt; [exact H|]. intros ms' H1. exact (K x s ms' H1).
- cbn [sbind membed] in *. unfold implM, mbind, ebind in *.
eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
+ exact H1.
+ eapply IH; [exact H1|exact K].
Qed.
Lemma implT_bind {R S} o (t : Malloc.M R) (f : R -> Malloc.M S) s Q1 Q ms :
implT o t s Q1 ms ->
(forall r s' ms', Q1 r s' ms' -> implT o (f r) s' Q ms') ->
implT o (sbind t f) s Q ms.
Proof.
unfold implT, mrun, prun. revert s ms. induction t as [r|e k IH]; intros s ms H K.
- cbn [sbind]. cbn [eruns membed] in H. unfold implM, mret in H. cbn in H.
eapply implM_evt; [exact H|]. intros ms' H1. exact (K r s ms' H1).
- cbn [sbind eruns]. cbn [eruns] in H. unfold pupd_mem in *. destruct (psel pans_mem o e) as [a|].
+ eapply IH; [exact H|exact K].
+ cbn [membed]. cbn [membed] in H. unfold implM, mbind, ebind in H |- *.
eapply impl_bind_mono; [exact H|]. intros [|[z s']] ms' H1; cbn in *.
* exact H1.
* eapply IH; [exact H1|exact K].
Qed.
Lemma implT_from_evt {R} o (t : Malloc.M R) s Q ms :
evt asegs (fun ms' => implT o t s Q ms') ms -> implT o t s Q ms.
Proof. intros H. eapply implT_evt; [exact H|]. intros ms' H'; exact H'. Qed.
End CEIL_WRAP_1.
Ltac iprefixT := apply implT_from_evt.
Section CEIL_WRAP_2.
Context {RUNp : RunP}.
Lemma implM_msys_ret {A B} n (dec : resp -> option A) (f : A -> B) (P : A -> machine_state -> Prop)
(s : PState) (Q : B -> PState -> machine_state -> Prop) ms :
impl asegs (at_node asegs) (enode n dec) (epost P) ms ->
(forall a ms', P a ms' -> evt asegs (Q (f a) s) ms') ->
implM asegs (mbind (msys n dec) (fun a => mret (f a))) s Q ms.
Proof.
intros H K. unfold implM, mbind, msys, mret, ebind, enode in *.
cbn [ITree.bind]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec rsp) as [a|]; cbn in *.
- eapply evt_cut; [exact Hk|]. intros ms' HP. cbn in HP. apply K. exact HP.
- exact Hk.
Qed.
Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.
Lemma implT_mmap_rw {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl asegs (at_node asegs) (enode (NMmap 0 len 3 34) (dec_mmap len [])) (epost P) ms ->
(forall a ms', P a ms' -> implT o (k (mmap_val a)) s Q ms') ->
implT o (SVis (EMmap 0 len PROT_RW (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_RW MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.
Lemma implT_mmap_none {R} o len (k : Z -> Malloc.M R) s (P : mmap_ans -> machine_state -> Prop) Q ms :
impl asegs (at_node asegs) (enode (NMmap 0 len 0 34) (dec_mmap_none len [])) (epost P) ms ->
(forall a ms', P a ms' -> implT o (k (mmap_val a)) s Q ms') ->
implT o (SVis (EMmap 0 len PROT_NONE (MAP_PRIVATE + MAP_ANON)) k) s Q ms.
Proof.
intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mmap_val a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.
Lemma implT_mmap_fixed {R} o addr len (k : Z -> Malloc.M R) s (P : fixed_ans -> machine_state -> Prop) Q ms :
impl asegs (at_node asegs) (enode (NMmap addr len 0 50) (dec_mmap_fixed addr len)) (epost P) ms ->
(forall a ms', P a ms' -> implT o (k (fixed_val addr a)) s Q ms') ->
implT o (SVis (EMmap addr len PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) k) s Q ms.
Proof.
intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = fixed_val addr a /\ P a ms')); [exact I| |].
- cbn [ev_step PROT_NONE MAP_PRIVATE MAP_ANON MAP_FIXED Z.add negb Z.eqb Z.land MAP_FIXED_Z Pos.land].
eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.
Lemma implT_munmap {R} o addr len (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl asegs (at_node asegs) (enode (NMunmap addr len) (dec_munmap addr len)) (epost P) ms ->
(forall a ms', P a ms' -> implT o (k (range_val a)) s Q ms') ->
implT o (SVis (EMunmap addr len) k) s Q ms.
Proof.
intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
- cbn [ev_step]. eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.
Lemma implT_mprotect {R} o addr len prot (k : Z -> Malloc.M R) s (P : range_ans -> machine_state -> Prop) Q ms :
impl asegs (at_node asegs) (enode (NMprotect addr len prot) (dec_mprotect_rw addr len)) (epost P) ms ->
(forall a ms', P a ms' -> implT o (k (range_val a)) s Q ms') ->
implT o (SVis (EMprotect addr len prot) k) s Q ms.
Proof.
intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = range_val a /\ P a ms')); [exact I| |].
- cbn [ev_step]. eapply implM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
- intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.
Lemma implT_brk0 {R} o (k : Z -> Malloc.M R) s (P : Z -> machine_state -> Prop) Q ms :
impl asegs (at_node asegs) (enode (NBrk 0) dec_brk0) (epost P) ms ->
(forall r ms', P r ms' -> implT o (k r) (set_brk_ps r s) Q ms') ->
implT o (SVis (EBrk 0) k) s Q ms.
Proof.
intros H K. eapply (implT_vis o _ k s (fun z s' ms' => s' = set_brk_ps z s /\ P z ms')); [exact I| |].
- cbn [ev_step Z.eqb]. unfold implM, mbind, msys, mupd, mret, ebind, enode in *.
cbn [ITree.bind]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec_brk0 rsp) as [a|]; cbn in *; [|exact Hk].
eapply evt_mono; [exact Hk|]. intros ms' HP. cbn in HP |- *. auto.
- intros z s' ms' (-> & HP). exact (K z ms' HP).
Qed.
Lemma implT_brk {R} o req (k : Z -> Malloc.M R) s (P : brk_ans -> machine_state -> Prop) Q ms :
req <> 0 ->
impl asegs (at_node asegs) (enode (NBrk req) (dec_brk (ps_brk s) req)) (epost P) ms ->
(forall a ms', P a ms' ->
implT o (k (match a with BrkGrown => req | BrkSame => ps_brk s end))
(match a with BrkGrown => set_brk_ps req s | BrkSame => s end) Q ms') ->
implT o (SVis (EBrk req) k) s Q ms.
Proof.
intros Hr H K.
eapply (implT_vis o _ k s (fun z s' ms' => exists a, P a ms' /\
z = match a with BrkGrown => req | BrkSame => ps_brk s end /\
s' = match a with BrkGrown => set_brk_ps req s | BrkSame => s end)); [exact I| |].
- cbn [ev_step]. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr).
unfold implM, mbind, msys, mget, mupd, mret, ebind, enode in *.
cbn [ITree.bind fst snd]. rewrite impl_vis_unfold in H. rewrite impl_vis_unfold.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
destruct (dec_brk (ps_brk s) req rsp) as [a|]; cbn in *; [|exact Hk].
destruct a; cbn in *; (eapply evt_mono; [exact Hk|]); intros ms' HP; cbn in HP |- *; eexists; eauto.
- intros z s' ms' (a & HP & -> & ->). exact (K a ms' HP).
Qed.
Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
exists ans o', follow (mrun o t) ans = Some (o', r).
Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], o. reflexivity. Qed.
Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
intros He (ans & o' & H). exists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
destruct e; cbn [psel]; try exact H; destruct He.
Qed.
Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. intros (ans & o' & H). exists ans, o'. rewrite mrun_peek. exact H. Qed.
Lemma implT_reach {R} o (t : Malloc.M R) : forall s Q ms,
implT o t s Q ms -> implT o t s (fun r s' ms' => Q r s' ms' /\ leaf_of o t r) ms.
Proof.
induction t as [r|e k IH]; intros s Q ms H.
- unfold implT, implM in *. rewrite mrun_ret in *. cbn [membed] in *. unfold mret in *. cbn in *.
eapply evt_mono; [exact H|]. intros ms' HQ. split; [exact HQ| apply leaf_of_ret].
- destruct e as [addr|addr len prot flags|addr len|addr len prot|p c h|w].
5:{ apply implT_peek. eapply implT_mono; [apply IH; unfold implT in H |- *; rewrite mrun_peek in H; exact H|].
cbn. intros r s' ms' [HQ HL]. split; [exact HQ|]. apply leaf_of_peek. exact HL. }
5:{ apply implT_undef. }
all: unfold implT in H |- *; rewrite mrun_vis in H |- * by exact I; cbn [membed] in H |- *;
unfold implM, mbind, ebind in H |- *;
eapply impl_bind_mono; [exact H|]; intros [|[z s']] ms' H1; cbn in H1 |- *; [exact H1|];
pose proof (IH z s' Q ms') as IH1; unfold implT, implM in IH1;
eapply impl_epost_mono; [apply IH1; exact H1|];
intros [[o1 r] s2] ms2; cbn; intros [HQ HL]; split; [exact HQ| apply (leaf_of_vis o _ k z); [exact I| exact HL]].
Qed.
Definition ptr_rel (p : optr) (r : option bptr) : Prop :=
match p, r with
| None, None => True
| Some pf, Some b => fst pf = fst (fst b) /\ exists off, snd pf = snd (fst b) + UNIT * off
| _, _ => False
end.
Lemma raw_malloc_bridge : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "RG'QI'R8'F&Q6':&QJ%2261'G!p021p091p051'8&R9%211pWL87pWJ?1pWH31'@&R5r7%211&R;r6%211%73I41&Q5vLr5&QHr8%23418r4r2%877L63>21r:(9%14Q5Q095r3%43216&Q3%12=8(3r1%22O1%K3O=1&;&QE%231Q>?&R:r9%Q011&5%136QCDr@%63421%Q63QF81p0<1pUBQ=1r<&R>%Q:1O%221Q7%43O1Q3p061p0H1p0K1pVNQE1pV@QM1pW6R41pVHR11pW:R71&R7&M&R=%12Q@Q=%47R;3QN1JQ@Q<p061p0Q<1p0QF1pV>R91pQFR01pQHR71pVFR@1pVBRB1pW4RD1pW8RF1").
Proof.
intros st s n o Q1 Q ms Hst H HQ. unfold raw_malloc.
eapply (implM_bind asegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind asegs _ _ _ (fun r s' ms' => exists st' p, Q1 (st', p) s' ms' /\ MREL (o, (st', p)) r)).
{ rewrite <- Hst. eapply (implT_strel MREL o (malloc st n) (cmalloc (strip st) n) s Q1).
- unfold mrun. apply malloc_control. apply pans_mem_range.
- exact H.
- intros o1 [st' p] [cs c] s' ms' HR H1. exists st', p. split; [exact H1|].
unfold MREL in *. cbn in *. exact HR. }
intros [cs c] s' ms' (st' & p & H1 & HR). cbv beta iota.
eapply (implM_bind asegs _ _ _ (fun _ s2 ms2 => s2 = set_m cs s' /\ ms2 = ms')).
{ apply implM_upd. apply evt_done. split; reflexivity. }
intros [] s2 ms2 [-> ->]. apply implM_ret. apply evt_done.
unfold MREL in HR. cbn in HR. destruct HR as [Hs Hp]. subst cs.
eapply HQ; [exact H1| |].
- destruct p as [pf|], c as [c|]; cbn in Hp |- *; try exact Hp.
- intros b Hb. destruct c as [c|]; [|discriminate]. inversion Hb; subst. reflexivity.
Qed.
Definition auxv_list (x3 x4 x5 hw x6 x11 x12 x23 rnd : Z) : list word :=
map wz [3; x3; 4; x4; 5; x5; 16; hw; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].
Lemma Forall_disjoint_from : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q5':'F%2211!p021'7%114'Dr4r3%33821r7(9r2r1%34>>21%511'C&RA&R@r6r5%3221%521>%62;4%8221p0:1pULJ1pV2K1&Q;%139FEp031p0F1pVBQ01pU>Q11pU<M1pQBQ01").
Proof.
intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.
Lemma raw_free_bridge : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "R9'QI'R8&R9&QD&Q6'G!p021p071p091'>pWL65pWJ;1pWH31'@&R5r8%211&R;r7%211%73E41&R6&Q7&Q8r9r6&5&QE'F%3321;%96K87651&Q5vL&QFr:(3%12Q2B%4231r5r3%978Q9?3@21r2r1%C3421(=&R>r4%Q111%3219%I3518p071pV@Q?1pW6QD1pW:QF1&R7&M&R<%12IGr;%57QK4QB21Q2Ep071p0E1p0Q01p0Q;1pV>QL1pQFQE1pQHQJ1pVFR01pVJR21pVHR41pW4R61pW8R81").
Proof.
intros st s p pf o Q1 Q ms Hst Hh H HQ. unfold raw_free.
eapply (implM_bind asegs _ _ _ (fun a s1 ms1 => a = s /\ s1 = s /\ ms1 = ms)).
{ apply implM_get. apply evt_done. repeat split; reflexivity. }
intros s0 s1 ms1 (-> & -> & ->). cbv beta.
eapply (implM_bind asegs _ _ _ (fun cs s' ms' => exists st', Q1 st' s' ms' /\ strip st' = cs)).
{ rewrite <- Hst. eapply (implT_strel FREL o (free st (Some pf)) (cfree (strip st) (Some (fst p))) s Q1).
- unfold mrun. apply free_control. exact Hh.
- exact H.
- intros o1 st' cs s' ms' HR H1. exists st'. split; [exact H1|]. unfold FREL in HR. exact HR. }
intros cs s' ms' (st' & H1 & <-). cbv beta.
apply implM_upd. apply evt_done. eapply HQ. exact H1.
Qed.
Definition pres_except (C : Z -> Prop) (m m' : mem) : Prop :=
forall a, 0 <= a < 2^64 -> ~ C a ->
m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Lemma pres_except_refl : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree ":'F!p021&Q6&Q2r2r1%33211pV451p471").
Proof. intros C m. intros a _ _; auto. Qed.
Lemma pres_except_trans : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "C'F!p021&Q6&Q2r4r3r2%43321r5%63143r6%83136p031p061pV<<1pV:=1pV8>1p4@1").
Proof. intros C m1 m2 m3. intros H1 H2 a Ha Hc. destruct (H1 a Ha Hc) as [E1 W1]. destruct (H2 a Ha Hc) as [E2 W2]. split; [congruence|auto]. Qed.
Lemma pres_except_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "G'F!p021&Q6&Q2r4r2r1%43321r6%113%215p021pU>=1r5r3%<32;1p041p0:1pV6@1pV4A1p6C1p4D1").
Proof. intros C C' m m'. intros H HC a Ha Hc. apply H; [exact Ha|]. intros Hc'. apply Hc, HC, Hc'. Qed.
Lemma pres_except_of_munch : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "QF'F!pWH21'7&Q<%211'SFyR0%211'8y8%511%311p051&Q=r3r2r1%43321&Q@&M%23165'?&RAz%2218&RB&RD+2+R0%3221%52>1%:271&Br8%11C%311&Q>%124Gp031p081pU>Q91&Q2r7r5r4%43321p061p0K1p0O1pV6Q51pV4Q61pU<Q?1p4QC1").
Proof. intros C W m m'.
intros MU WM HW a Ha Hc. split.
- apply MU. rewrite wa_unsigned by lia. apply HW; assumption.
- apply WM.
Qed.
Lemma pres_except_bytes_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q?'F!p021&Q6'7'SFy8%211%411&Q2r5r4r3%43321&QA&Mr2%342751'?&RAr1%22;1&RB&R@&RC&6%12C?%311%52B1%7291%<291&Br9%11A%311p051pU>Q41r6%H4G1LKp031p0G1p0L1pUDQ21p2Q;1pV6Q91pV4Q:1p4Q<1").
Proof. intros C m m' A bs.
intros HP (H0 & H1 & HB) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia)) as [E _]. rewrite E. reflexivity.
Qed.
Lemma pres_except_wr_at : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q6'F!p021&Q6&Q2r5r4r3%43321&QB&Mr2%342751'?&RAr1%22;1&RB&R@%12>=%3251%8251&Br9%11=%311p051pU>K1r6%D4C1HGp031p0C1p0H1pVBQ11p2Q21pV6Q01pV4Q11p4Q31").
Proof. intros C m m' A n.
intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ W]. apply W, HW, Hi.
Qed.
Lemma pres_except_rw_cells : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q='F!p021&Q6'7'Q9%211&Q2r5r4r3%43321&QC&Mr2%342751'?&RAr1%22;1&RB&R@&RC&Q:%11?%311%52B1%7291%<291&Br9%11A%311p051pU>Q21r6%H4G1LKp031p0G1p0L1pUHQ21p2Q91pV6Q71pV4Q81p4Q:1").
Proof. intros C m m' A cs.
intros HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
- eapply pres_except_bytes_at; eauto. rewrite cells_bytes_length by assumption. exact HR.
- eapply pres_except_wr_at; eauto.
Qed.
Lemma pres_except_stk : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q4'F!p021&Q6&Q2r5r4r3%43321&Q?&Mr2%342751'?&RAr1%22;1&RB%123<%6231&Br9%11;%311p051pU>I1r6%B4A1FEp031p0A1p0F1pULO1pV2Q01pV6N1pV4O1p4Q11").
Proof. intros C m m' lo hi.
intros HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (HP i ltac:(lia) ltac:(apply HR; lia)) as [E W]. destruct (HW i Hi) as [W0 [b Hb]].
split; [apply W, W0|]. exists b. unfold mrd in *. rewrite E. exact Hb.
Qed.
Definition brk_link_ps (st : mstate) (s : PState) : Prop :=
match c_brk (ctx st) with
| BrkLive rid off => ps_brk s = conc st (rid, off)
| _ => True
end.
Definition optr_in (P : N -> Prop) (p : optr) : Prop :=
match p with Some q => P (fst q) | None => True end.
Definition ptrs_in (P : N -> Prop) (st : mstate) : Prop :=
let c := ctx st in
optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
/\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
/\ (forall sc, optr_in P (active st sc))
/\ match c_brk c with BrkLive rid _ => P rid | _ => True end
/\ (forall g, optr_in P (m_prev (get_meta_rec st g)) /\ optr_in P (m_next (get_meta_rec st g))
/\ optr_in P (m_mem (get_meta_rec st g)))
/\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
/\ (forall b gh, (s_groups st) !! b = Some gh -> P (fst b) /\ optr_in P (g_meta gh)).
Lemma ptrs_in_mono : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "D'E!p021'QIr4r1%211r2%411p031pVN:1&Q4%1285r3%32:1p031p061pW8>1pQD@1pQBA1").
Proof. intros P P' st.
intros HP (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
split; [intros g; destruct (H8 g) as (X1 & X2 & X3); auto|].
split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
amr_active : forall sc, active st1 sc = active st sc;
amr_usage : forall sc, usage st1 sc = usage st sc;
amr_bounces : forall i, bounces st1 i = bounces st i;
amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
amr_seq : c_seq (ctx st1) = c_seq (ctx st);
amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
amr_groups : s_groups st1 = s_groups st;
amr_slots : s_slots st1 = s_slots st;
amr_shadow : s_shadow st1 = s_shadow st;
amr_tick : s_tick st1 = s_tick st;
amr_reserved : s_reserved st1 = s_reserved st;
amr_metas : forall g, Some g <> mo ->
(m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
get_meta_rec st1 g = get_meta_rec st g;
amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
/\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
amr_ptrs : forall P : N -> Prop,
(forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
ptrs_in P st -> ptrs_in P st1;
amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.
Definition AM_STACK : Z := 128.
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
a < alloc_ceiling /\ ranges_free (live_ranges st) a 1 = true.
Lemma ranges_free_In : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q3'7':'F%2211%411'@'4&QNr5r4r3%43321(<%83721&R?(9r2%24??71r6%53@21'C&RA&R@%125?%321?%32@?%5218%7231p091p0@1pUNL1pUBM1pVBN1pU>O1pV0N1").
Proof. intros l a n b k.
intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma ranges_free_intro : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q3'7':'F%2211%411&R?(9r2r1%347721r5%63821'C&RA&R@r4%2261r3%5221%522<%721:%9231p0;1pUNE1pUBF1'@'4&QN%13=;E(<%53421p071pVBN1pU>O1pV0N1").
Proof. intros l a n.
intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.
Lemma ranges_free_sub : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q3'7':'F%2211%411'@'4&QNr5r4r3%43321(<%83721&RA%1275&R@%1287r6%321;%6231z%821=r9%A316@%D3C1=p041p071p0=1p0@1pVDL1pU@M1pVBN1pU>O1pV0N1").
Proof. intros l a n a' n'.
intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.
Lemma In_live_ranges : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "Q4'QI'E'QO'@'8%113&SE'SH&SJ&SG%349218&SI%14;43:r2&R3r3%211%;6@?7541(3r1%22B1%B3@41&R?':'F%2211&R0%11>&QGr4%211%93641p0;1pVNO1pW2Q11pW8Q31").
Proof. intros st rid r.
intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.
Lemma fresh_live_region : ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "QA'QI'F'E'QO&Q1r4r3%3221'@'8%117&SE'SH&SJ&SG%34=21<&SI%14?43>&R3r5%211%:6CB64?1(3r2%22E1%A3?41'C&RA&R@+1%22;1&N%11J%6231&QK%11M&R2&QM%11Q0%311%<251%>21F%@291p0B1p0Q51pVNQ:1pW2Q<1pU>Q>1pW8Q@1").
Proof. intros st a rid r.
intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.
Section SE.
Local Abbreviation SEC_T_fresh_addr_anti := (ltac2:(TCodec.tc2 tcn__CJ_Agent_MallocTree "R6'QI'F'@'7':%1244%311&R4r2%211r3%411%:3631'E'QO'8%112&SE'SH&SJ&SG%348217&SI%14:439&R3r6%211%:6>=64C1(3r1%22@1%M3?41'A'?r4r7%<11%D6HG@>31%Q43F18'R1&QL%11<%21Q0%Q93421&QK%11@%21Q4%Q=3Q>21&RA&QM%11Q8%21F%4221%D261%E2;1%F2A1qW0Q:1%I2Q;1p0K1pVNQ=1pW2Q?1&Q1%12LQD%22Q6Mp021p051p0QF1pU>R21pW:R41pW8R51")) (only parsing).
Variable st : ltac:(sec_ty2 constr:(SEC_T_fresh_addr_anti) 0%nat 0%nat).
Variable st' : ltac:(sec_ty2 constr:(SEC_T_fresh_addr_anti) 1%nat 0%nat).
Variable a : ltac:(sec_ty2 constr:(SEC_T_fresh_addr_anti) 2%nat 0%nat).
Lemma fresh_addr_anti : ltac:(sec_stmt2 constr:(SEC_T_fresh_addr_anti) 3%nat 0%nat).
Proof.
intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
- apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
- apply in_map_iff in HI. destruct HI as ([rid r] & E & HI). cbn [snd] in E.
apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
destruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
pose proof (In_live_ranges st' rid r' Hr') as HI'.
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold region_live_range in HI', E. rewrite K', B' in HI'.
destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.
End SE.
End CEIL_WRAP_2.
