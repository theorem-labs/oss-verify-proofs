(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16 YK0n YK0i YK11 YK14 YK0h.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Section a.
Context {fx : FPState}.
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
intros A l H. unfold len_word. apply Z_to_bv_small.
unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.
Lemma len_word_firstn_nat : forall n (bs : list byte),
(n <= length bs)%nat ->
len_word (firstn n bs) = nat_to_word n.
Proof.
intros n bs Hn. unfold len_word, nat_to_word.
rewrite firstn_length_le by exact Hn. reflexivity.
Qed.
Lemma u_len_word_firstn : forall n (bs : list byte),
(n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof.
intros n bs Hn Hlen.
rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
unfold two_pow_64; lia).
rewrite firstn_length_le by exact Hn. reflexivity.
Qed.
Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
(n <= length bs)%nat ->
v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
unfold v_add. apply bv_eq.
rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.
Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
(n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof.
intros p n bs Hn Hlen. unfold v_add.
rewrite u_len_word_firstn by assumption. reflexivity.
Qed.
Lemma word_add_nat_Z : forall (p : word) (k : nat),
(Z.of_nat k < 2^64)%Z ->
p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
intros p k Hk. apply bv_eq.
rewrite bv_add_unsigned. unfold nat_to_word.
rewrite Z_to_bv_small
by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma v_sub_len_firstn : forall n (bs : list byte),
(n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof.
intros n bs Hn Hlen. apply bv_eq.
rewrite v_sub_small
by (rewrite u_len_word_firstn by assumption;
rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
rewrite u_len_word_firstn by assumption.
rewrite !len_word_unsigned
by (unfold two_pow_64; rewrite ?length_skipn; lia).
rewrite length_skipn. lia.
Qed.
Section d.
Variable segs : list Segment.
Variable fd ch : word.
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 64%Z ->
ms_gpr ms 0 = fd ->
ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k) ->
to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
(1 <= length rest)%nat ->
to_wall ms rest k ->
to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wall_tail ms' rest k ->
to_wall_tail ms rest k.
Scheme to_wall_min := Minimality for to_wall Sort Prop
with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.
Lemma msteps_to_wall_tail : forall ms ms' rest k,
msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
intros ms ms' rest k H; induction H; [auto|].
intro Hw. eapply twt_step; eauto.
Qed.
Lemma to_wall_tail_nil_msteps : forall ms k,
to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
intros ms k H.
remember ([] : list byte) as rest eqn:Hrest.
induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
- exists ms. split; [apply mst_refl | exact Hk].
- subst rest. cbn in Hnb. lia.
- destruct (IH Hrest) as (ms'' & Hm & Hk).
exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.
Hypothesis Hfd32 : fd32 fd = fd.
Lemma sstep_to_wall_inv : forall ms rest k model evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
buf_modeled rest ->
to_wall ms rest k ->
sstep segs (mkCfg ms model) evs st ->
exists n, (1 <= n)%nat /\ (n <= length rest)%nat /\
evs = map (WriteEv ch) (firstn n rest) /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model) /\
to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
(skipn n rest) k.
Proof.
intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
revert Hbm.
destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont]. intro Hbm.
destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
exists n. repeat split; try assumption.
apply (Hcont n Hn1 Hn2).
Qed.
Lemma to_wall_no_error_sstep : forall ms rest k model evs,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
buf_modeled rest ->
to_wall ms rest k ->
~ sstep segs (mkCfg ms model) evs SError.
Proof.
intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
as (n & _ & _ & _ & Hst & _).
discriminate Hst.
Qed.
Lemma to_wall_star_admits_mut : forall model tr_k,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms rest k, to_wall ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
/\ (forall ms rest k, to_wall_tail ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c).
Proof.
intros model tr_k Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm Hk.
destruct (IH (length rest) Hnb (Nat.le_refl _)
(buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
exists c.
replace (map (WriteEv ch) rest ++ tr_k)
with (map (WriteEv ch) (firstn (length rest) rest)
++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
by (rewrite firstn_all, skipn_all; reflexivity).
eapply star_step; [| exact Hstar].
rewrite <- (apply_effect_copyins_no_write ms
(len_word (firstn (length rest) rest))
[(ms_gpr ms 1, length rest)]).
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv ch) (firstn (length rest) rest)));
[exact Hh | exact Hsvc | | exact Hh |].
eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
-
intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
-
intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
destruct (IH Hbm Hk) as [c Hstar].
exists c.
replace (map (WriteEv ch) rest ++ tr_k)
with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
eapply star_step; [| exact Hstar].
apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_wall_star_admits : forall ms rest k,
to_wall ms rest k ->
buf_modeled rest ->
forall model tr_k,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.
Lemma to_wall_tail_star_admits : forall ms rest k,
to_wall_tail ms rest k ->
buf_modeled rest ->
forall model tr_k,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.
Lemma to_wall_star_only_mut : forall model T,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms rest k, to_wall ms rest k ->
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))
/\ (forall ms rest k, to_wall_tail ms rest k ->
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T)).
Proof.
intros model T Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))
(fun ms rest k =>
buf_modeled rest ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK tr c Hstar.
inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
{ apply is_prefix_nil. }
destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
Hh Hlazy Hfdc Hsvc Hno Hg Hr Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
subst evs. inversion Hc2; subst c2.
pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
rewrite <- (firstn_skipn n rest) at 2.
rewrite map_app, <- app_assoc.
apply is_prefix_app_mono. exact Hp.
-
intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
-
intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
{ apply is_prefix_nil. }
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
as [Hevs Hc2].
subst evs. inversion Hc2; subst c2. cbn [app].
exact (IH Hbm HK tr2 c Hstar2).
Qed.
Lemma to_wall_star_only : forall ms rest k,
to_wall ms rest k ->
buf_modeled rest ->
forall model T,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (map (WriteEv ch) rest ++ T).
Proof.
intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.
Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
bv_unsigned (getr regs 17) = 64%Z ->
reg_get regs 10 = fd ->
ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None;
ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
(reg_get regs 11) (reg_get regs 12) = Some rest ->
(1 <= length rest)%nat ->
(forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
(v_addi pc 4) mem rom)
(skipn n rest) k) ->
to_wall {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
ms_svc_pending := Some (getr regs 17); ms_resv := None;
ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
rest k.
Proof.
intros k rest regs pc mem rom H17 H10 Hr Hnb Hcont.
assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
eapply twl_write.
- cbn [ms_svc_pending]. reflexivity.
- exact H17.
- unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
- unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
- exact Hnb.
- intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.
Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
(ms : machine_state) : Prop :=
match bufs with
| [] => to_wexit segs ms [] code
| buf :: rest =>
(1 <= length buf)%nat /\
to_wall_tail ms buf (to_wallexit rest code)
end.
Lemma to_wall_k_ex_mut :
(forall ms rest k, to_wall ms rest k -> exists ms', k ms')
/\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof.
apply (to_wall_mutind
(fun ms rest k => exists ms', k ms')
(fun ms rest k => exists ms', k ms')).
- intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH.
exact (IH (length rest) Hnb (Nat.le_refl _)).
- intros ms k Hk. exists ms. exact Hk.
- intros ms rest k Hnb Hw IH. exact IH.
- intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.
Lemma to_wall_tail_k_ex : forall ms rest k,
to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.
Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
to_wallexit bufs code ms ->
Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
exact (IH code ms' Hk).
Qed.
Lemma twe_step : forall ms ms' bufs code,
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hsvc Hstep Hw.
destruct bufs as [|buf rest].
- eapply tw_step; eauto.
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply twt_step; eauto.
Qed.
Lemma msteps_to_wallexit : forall ms ms' bufs code,
msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
- exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
- destruct Hw as [Hnb Hw]. split; [exact Hnb|].
eapply msteps_to_wall_tail; eauto.
Qed.
Lemma to_wall_exec_mut : forall model (Q : post),
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
(forall ms rest k, to_wall ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
/\ (forall ms rest k, to_wall_tail ms rest k ->
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o)).
Proof.
intros model Q Hh Hlazy Hfdc.
apply (to_wall_mutind
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
(fun ms rest k =>
buf_modeled rest ->
(forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
-
intros ms x8 rest k Hsvc Hno Hg Hr Hnb Hcont IH Hbm HK.
assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
apply exec_step; [exact Hh | | |].
+
eexists; eexists.
apply (sstep_syscall segs ms model x8
(with_copyins [(ms_gpr ms 1, length rest)]
(mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
(map (WriteEv ch) (firstn (length rest) rest)));
[exact Hh | exact Hsvc | | exact Hh |].
* eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
* rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
+ intros evs Hss.
destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
as (n & _ & _ & _ & Habs & _).
discriminate Habs.
+ intros evs c' Hss.
destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
as (n & Hn1 & Hn2 & -> & Hc' & _).
injection Hc' as ->.
eapply exec_conseq;
[exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
-
intros ms k Hk Hbm HK.
eapply exec_conseq; [exact (HK ms Hk) |].
intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
-
intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
-
intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_wexit segs ms bufs code ->
bufs = [] ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
intros ms bufs code model Hh Hlazy Hte.
induction Hte as
[ms x8 Hsvc Hx8
| ms x8 buf bufs code Hsvc Hno Hg Hr Hnb Hcont IH
| ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
- apply (exec_step_only segs _ _
[ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
(mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
+ replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
(m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
by (cbn; reflexivity).
apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
(with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
(bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
* exact Hh.
* exact Hsvc.
* apply (exit_dispatch_ok (sys_input segs ms x8) model).
rewrite in_sysno_sys_input. exact Hx8.
* cbn. reflexivity.
* apply m_killed_with_halted.
+ intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
+ apply exec_halt.
* cbn. rewrite m_halted_with_halted. discriminate.
* cbn beta. rewrite app_nil_r. split; [reflexivity |].
cbn [exits_with cfg_model]. split;
[ rewrite m_halted_with_halted; reflexivity
| apply m_killed_with_halted ].
- apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
+ apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
+ intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
+ eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.
Lemma to_wexit_nil_exec : forall ms code model,
m_halted model = None ->
m_vm_lazy model = [] ->
to_wexit segs ms [] code ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
intros ms code model Hh Hlazy Hte.
exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.
Lemma to_wallexit_exec : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
OmniRun.exec segs (mkCfg ms model)
(fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
/\ exits_with code tr o).
Proof.
induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
- cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
- destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
eapply exec_conseq;
[exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma to_wallexit_star_admits : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
exists c, star segs (mkCfg ms model)
(wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
exists c'. exact Hstar.
Qed.
Lemma to_wallexit_no_other_exit : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
forall code', code' <> code ->
~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
rewrite Hx in Hx'. injection Hx' as Hx'.
exact (Hne (eq_sym Hx')).
Qed.
Lemma to_wallexit_trace_unique : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
as (tr & o & Hm & Heq & _).
pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.
Lemma to_wallexit_not_silent : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.
Lemma to_wallexit_star_only : forall bufs code ms model,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
forall tr c, star segs (mkCfg ms model) tr c ->
is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof.
intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
destruct (exec_realizes _ _ _
(exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
as (tr' & o & _ & HQ).
cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.
Lemma to_wallexit_no_error : forall ms model bufs code,
m_halted model = None ->
m_vm_lazy model = [] ->
fdchan fd ch model ->
bufs_modeled bufs ->
to_wallexit bufs code ms ->
~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
End d.
Abbreviation wexit1 segs ms bufs code :=
(to_wallexit segs (Z_to_bv 64 1) bufs code ms).
Lemma wevents_ch_fd1 : forall bufs,
wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
[reflexivity | rewrite IH; reflexivity].
Qed.
Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
forall segs pc ph sp brk0 mb rnd lim inp bufs code,
fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
bufs_modeled bufs ->
to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
/\ exits_with code tr o).
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
cbn [omni_run]. unfold init_config.
exact (to_wallexit_exec segs fd ch Hfd32 bufs code _
(init_model (segments_reserved segs) brk0 mb sp lim inp)
eq_refl eq_refl Hfdc Hbm Hw).
Qed.
Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
forall segs pc ph sp brk0 mb rnd lim inp bufs code,
fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
bufs_modeled bufs ->
to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
apply exec_obs_iff.
eapply exec_conseq;
[exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.
Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
forall segs pc ph sp brk0 mb rnd lim inp bufs code,
fdchan fd ch (init_model (segments_reserved segs) brk0 mb sp lim inp) ->
bufs_modeled bufs ->
to_wallexit segs fd bufs code (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
eapply exec_conseq;
[exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.
Lemma wall_omni_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
to_wallexit source_segs (Z_to_bv 64 1) bufs code
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_wallexit target_segs (Z_to_bv 64 1) bufs code
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
bufs_modeled bufs ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
Hsource Htarget Hbm.
assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved source_segs) rbrk rmb rsp source_alloc_limit inp))
by (split; reflexivity).
assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved target_segs) abrk amb asp target_alloc_limit inp))
by (split; reflexivity).
split.
{ cbn [img_segments].
eapply coexec_conseq;
[apply exec_coexec;
exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
intros tr o (_ & Hx).
exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
reflexivity.
- apply bh_errors_iff. cbn.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.
Lemma wall_strong_equiv :
forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
to_wallexit source_segs (Z_to_bv 64 1) bufs code
(init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_wallexit target_segs (Z_to_bv 64 1) bufs code
(init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
bufs_modeled bufs ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
bufs code inp Hsource Htarget Hbm.
assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved source_segs) rbrk rmb rsp rlim inp))
by (split; reflexivity).
assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
(init_model (segments_reserved target_segs) abrk amb asp alim inp))
by (split; reflexivity).
split.
{ apply no_error_run_modeled.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
HfdS Hbm Hsource). }
right. split.
- intro tr. cbn.
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
HfdS Hbm Hsource tr).
rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd alim inp bufs code
HfdT Hbm Htarget tr).
reflexivity.
- cbn.
apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
target_segs apc aph asp abrk amb arnd alim inp bufs code
HfdT Hbm Htarget).
Qed.
End a.
