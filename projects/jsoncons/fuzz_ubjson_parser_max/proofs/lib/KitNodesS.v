(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim Scfg ShapeAlg SpinAlg Nodes RefNodes.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__KitNodesS () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs."; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.KitNodesS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.RefNodes."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1Some"; "1bool"; "1false"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "1true"; "2eq"; "2not"; "3Z"; "4check_syscall"; "5CheckOk"; "5check_result"]; ["5errno_ret_in"; "6machine_state"; "6ms_svc_pending"; "7SNext"; "7advance_past_svc"; "7apply_effect"; "7mkCfg"; "7refusal_b"; "7spurious_refusal_cfg"; "7sstep_cfg"; "7sys_input"; "8Model"; "8SyscallEffect"; "8eff_ret"; "8event"; "8m_halted"]; ["8syscall_effect_accesses"; "9mmap_errnos"; ":alloc_enomem_sysno_b"; ":alloc_mm_sysno_b"; ":grant_ok_na_pin"; ";grant_ok"; "<grant_ok_na"; "=le"; "0a"; "0eff"; "0effS"; "0evS"; "0evs"; "0hint"; "0m"; "0m'"]; ["0mS"; "0model"; "0ms"; "0n"; "0r"; "0scfg"; "0segs"; ">bv"; ">bv_unsigned"; "0x8"]]).
Definition alloc_enomem_sysno_b (n : Z) : bool :=
match injected_arm n with Some _ => true | None => false end.
Definition alloc_mm_sysno_b (n : Z) : bool := (n =? 222)%Z || (n =? 226)%Z.
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
&& (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
&& region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).
Lemma grant_ok_na_pin_eq : ltac2:(TCodec.tc2 tcn__KitNodesS "D'QGyR0%211'K'<':'2&Q4r3r2r1%43321&Q6r4%241654%:3941pS8<1pRB?1pRN?1pRLA1").
Proof. reflexivity. Qed.
Lemma grant_ok_na_pin_of_grant_ok : ltac2:(TCodec.tc2 tcn__KitNodesS "G'QGyR0%211'K'<':'2&Q5r4r3r2r1%544321(9%93821&Q4%13876%<3;14p041pS8?1pRBB1pRNB1pRLD1").
Proof. intros hint m a n H. rewrite (grant_ok_na_pin_eq hint). apply grant_ok_grant_ok_na. exact H. Qed.
Lemma grant_na_pin_not_errno : ltac2:(TCodec.tc2 tcn__KitNodesS "L'K'QGyR0%211'<&Q7zr1%3221':'2&Q4r4r3r2%43321(9%83721&@&Q1%2218(3%=3<21p061p0@1pS8E1pRBG1pRNK1").
Proof.
intros m a n Hn Hg. unfold grant_ok_na_pin in Hg.
apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.
Section Shim.
Context {fx : PropExec.FPState}.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Lemma not_unforced_na : ltac2:(TCodec.tc2 tcn__KitNodesS "O'A'K'QGyR0%211'L':'2&Q2&QHr2%2281%411(3%83721&;&HvQE&JvQFr5r3%43321r4%84721>%:11p0<1pRDF1pSDH1pS4L1pS6N1").
Proof.
intros ms model x8 eff Hal. unfold alloc_enomem_sysno_b in Hal.
destruct (injected_arm (bv_unsigned x8)) eqn:E; [discriminate|].
intros (Hoff & _ & _). unfold injected_family_off in Hoff. cbn [in_sysno sys_input] in Hoff. rewrite E in Hoff. discriminate.
Qed.
Lemma alloc_nonrefusal_step : ltac2:(TCodec.tc2 tcn__KitNodesS "Q1'A'K'QGyR0%211'L':'2&G&JvQFr4r2%43321r3&Mr1%211%:3541(3%>3=21&;&HvQEr5%@3?1;%4431?>%611p081pRDH1pSDJ1pS4N1pS6Q01").
Proof. intros. apply not_spurious_nonrefusal. assumption. Qed.
Lemma sstep_cfg_of_check_noacc : ltac2:(TCodec.tc2 tcn__KitNodesS "R@'A'K'QGyR0%211'L'4'N%211':'7%117&Or5%211(0%11<%83631&Br7%211(1%12B9%>3<31'?&=&JvQFr8r6%43321%631B<(>r4r3%3221%K3<51&;&HvQEr9%?3>1F%4431>=%611%Q01?%Q43Q21M'8'5%22Q<1%Q;11&Q0%11G(6%115%Q=3531'I(Fr<r;%3221(C&D&E%126G%311%921Q5%611%<5Q8L8Q@1p0>1p0H1p0K1p0Q31p0QA1p0QH1pRJR21pS0R:1pRDR71pSDR91pS4R=1pS6R?1").
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hacc.
apply (sstep_cfg_syscall segs scfg ms model x8 eff m' m' evs Hh Hsvc).
- apply check_syscall_ok_iff. exact Hc.
- exact Hns.
- exact Hh'.
- rewrite Hacc. apply materialize_model_accesses_nil.
Qed.
Lemma node_chk_ev_gen : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnf Hinv Hnu Hnh Hlazy. split.
- intros i. apply (sstep_cfg_of_check segs scfg ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
- intros e st Hss.
destruct (sstep_cfg_svc_inv segs scfg ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
| (eff & Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
+ rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
+ exfalso. exact (Hnu eff Hc).
Qed.
Lemma node_chk_ev_gen_noacc : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
(forall m, materialize_model_accesses m [] = Some m) ->
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall i, ~ spurious_refusal_cfg scfg (sys_input segs ms x8) model (effs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
~ spurious_refusal_cfg scfg (sys_input segs ms x8) model eff ->
exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev -> m_halted m' = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
node_ok segs scfg (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs mat_nil Hh Hsvc Hok Hnf Hinv Hnu Hnh Hacc. split.
- intros i. apply (sstep_cfg_of_check_noacc ms model x8); auto. exact (Hnh _ _ _ (Hok i)).
- intros e st Hss.
destruct (sstep_cfg_svc_inv segs scfg ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(Hnsp & Hh2 & [(m'' & -> & Hmat & ->) | (-> & Hmat & ->)]) | (code & Hh2 & -> & ->)])
| (eff & Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
rewrite (Hacc i), mat_nil in Hmat. injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hc Hnsp) as (i & -> & -> & ->).
rewrite (Hacc i), mat_nil in Hmat. discriminate.
+ rewrite (Hnh _ _ _ Hc) in Hh2. discriminate.
+ exfalso. exact (Hnu eff Hc).
Qed.
Lemma refusal_b_mmap_sys : ltac2:(TCodec.tc2 tcn__KitNodesS "N'A'QGyR0%211'K':'<&QHr3%2271+VN%63521'2&G&JvQFr5r4%43321r2%732<1&@&Q1%2214%C3<41p0>1pS:G1pS4G1pSDI1pS6M1").
Proof.
intros ms x8 model r Hno. unfold refusal_b. cbn [in_sysno sys_input]. rewrite Hno. reflexivity.
Qed.
Section Alloc.
Hypothesis Halloc : sc_alloc scfg = false.
Lemma alloc_refusal_unforced : ltac2:(TCodec.tc2 tcn__KitNodesS "QN'A'K'QGyR0%211'L'4'N%211':'2&Q3&QHr5%22;1%411(9%83721'?&=&JvQFr8r6%43321r4r7%83321(>r3r2%3221%G3>51&Gr9%?3>19&M%11H%533@1(3%O3N21r:%F3E1D%71A%;32:1%Q43Q31M&HvQEr;%M3L1?%44319Lp061p0<1p0E1p0Q51pRHQ?1pS2QG1pRFQD1pRDQE1pSDQG1pS4QK1pS6QM1").
Proof.
intros ms model x8 eff effS mS evS Hal HcS HnS Hr.
apply (spurious_intro scfg _ model eff effS mS evS); [| exact Hr | apply check_syscall_ok_iff; exact HcS | exact HnS].
unfold alloc_mm_sysno_b in Hal. apply orb_prop in Hal as [E | E]; apply Z.eqb_eq in E.
- apply (injected_family_off_222 segs scfg ms x8 E Halloc).
- apply (injected_family_off_226 segs scfg ms x8 E Halloc).
Qed.
End Alloc.
End Shim.
