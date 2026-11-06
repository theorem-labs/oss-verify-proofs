(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1r3 X1og X1oh X1oi X1pe X1r9 X1os X1or X1oo X1ns.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Lemma vis_flat_L {A} B n (k : resp -> itree node (exc A)) mo (Q : A -> Model -> Prop) (R : A -> Model -> Prop) :
(forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
nroomE B n mo ->
etwfU (Vis n k) mo Q ->
(forall rsp mo' evs a, nstep n mo rsp mo' evs -> k rsp = Ret (Ok a) -> Q a mo' -> R a mo' /\ step_live B mo') ->
etwl B (Vis n k) mo (fun a mo' => Q a mo' /\ R a mo').
Proof.
intros Hf Hr H HR. cbn in H |- *. destruct H as [_ Hk]. split; [exact Hr|]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst I). specialize (Hf rsp).
destruct (k rsp) as [[|a]|n' k'] eqn:Ek; cbn in Hk |- *; [destruct Hk| | destruct Hf].
destruct (HR rsp mo' evs a Hst Ek Hk) as [HRa HB]. auto.
Qed.

Definition BOUND (L : mled) (e : ev) (B : Z) : Prop := BOUNDB L e B /\ RQ L e B.

Lemma BOUND_intro L e B : BOUNDB L e B -> RQ L e B -> BOUND L e B. Proof. intros H1 H2. split; assumption. Qed.

Lemma RQ_other L e B : (forall a len prot, e <> EMmap a len prot MAPF) -> RQ L e B.
Proof. intros H. destruct e; cbn; auto. intros -> ->. exfalso. exact (H 0 len prot eq_refl). Qed.

Lemma errno_none_below : forall r : word, bv_unsigned r < 2^64 - 4095 -> errno_of r = None.
Proof. intros r H. unfold errno_of. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned r)); [lia| reflexivity]. Qed.

Lemma anon_no_enomem B L pbrk mo len prot :
KL L pbrk mo -> LI L mo -> 0 < len < LEN_MAX -> (prot = PROT_NONE \/ prot = PROT_RW) -> B <= LBUDGET ->
nroom B (NMmap 0 len prot MAPF) mo -> no_enomem (NMmap 0 len prot MAPF) mo.
Proof.
intros HK HL Hlen Hp HB Hr. cbn [no_enomem]. intros _ rsp mo' evs Hst.
pose proof (ld_ceil_lt _ _ _ HK) as Hcl. pose proof (proj1 (kl_ceil _ _ _ HK)) as Htop.
pose proof (mmap_len_ge len ltac:(lia)) as Hml. unfold LEN_MAX in Hlen.
assert (Hq : mem_quiet mo) by (apply mem_quiet_of; [exact (kl_minv _ _ _ HK)| exact (LI_nomat _ _ HL)]).
assert (Hlim : B <= vm_limit (m_vmmaps mo)) by (pose proof (proj2 (LI_sbk _ _ HL)) as V; unfold LBUDGET, BMAX in *; lia).
destruct Hp as [-> | ->].
- destruct (nstep_dec_mmap_none (ld_ceil L) len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite Htop; lia) ltac:(constructor) Hst)
as (_ & _ & x & Hd & Hx).
destruct x as [e|a].
+ exfalso. destruct Hx as (_ & _ & Hforced). rewrite (nroom_reserve_not_refusable B len mo Hr) in Hforced. discriminate Hforced.
+ destruct Hx as (Hok & _). apply mmap_addr_ok_true in Hok as ((_ & Ha0 & Hac) & _).
rewrite (X1ns.dec_mmap_none_MmOk _ _ _ _ _ Hd) in Hac, Ha0. apply errno_none_below. lia.
- destruct (nstep_dec_mmap (ld_ceil L) len [] mo rsp mo' evs ltac:(lia) ltac:(lia) ltac:(rewrite Htop; lia) ltac:(constructor) Hst)
as (_ & _ & x & Hd & Hx).
destruct x as [e|a].
+ exfalso. destruct Hx as (_ & _ & Hforced). rewrite (nroom_grant_not_refusable B len mo Hq Hlim Hr) in Hforced. discriminate Hforced.
+ destruct Hx as (Hok & _). apply mmap_addr_ok_true in Hok as ((_ & Ha0 & Hac) & _).
rewrite (X1ns.dec_mmap_MmOk _ _ _ _ _ Hd) in Hac, Ha0. apply errno_none_below. lia.
Qed.

Lemma eff_ret_ecore : forall rsp, eff_ret rsp = eff_ret (ecore rsp).
Proof. intros [r ws zs us cs ci]. reflexivity. Qed.

Lemma mprotect_no_enomem B L pbrk mo b l k :
KL L pbrk mo -> LI L mo -> In (b, l, k) (ld_metas L) -> (2 + k) * PGSZ <= round_up_pg l ->
B <= LBUDGET -> BOUNDB L (EMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) B ->
no_enomem (NMprotect (b + (1 + k) * PGSZ) PGSZ PROT_RW) mo.
Proof.
intros HK HL Hin Hk HB HBd. cbn [no_enomem]. intros rsp mo' evs Hst.
pose proof (ld_ceil_lt _ _ _ HK) as Hcl.
pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _). unfold LEN_MAX in A1.
rewrite round_up_pg_eq in Hk. fold (mmap_len l) in Hk.
assert (Hq : mem_quiet mo) by (apply mem_quiet_of; [exact (kl_minv _ _ _ HK)| exact (LI_nomat _ _ HL)]).
assert (Hlive : live_bytes (vm_maps (m_vmmaps mo)) <= vm_limit (m_vmmaps mo)).
{ pose proof (proj2 (LI_sbk _ _ HL)) as V. pose proof (LI_elim _ _ HL) as E. unfold vm_live_bytes in E.
pose proof (HBd (TWO64 - ENOMEM) eq_refl) as Hpre. change (event_post L _ (TWO64 - ENOMEM)) with L in Hpre.
unfold LBUDGET, BMAX in *. lia. }
destruct (nstep_dec_mprotect (b + (1 + k) * PGSZ) PGSZ mo rsp mo' evs ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(vm_compute; reflexivity) Hst)
as (_ & _ & x & Hd & Hx).
destruct x as [e|[|]].
- exfalso. destruct Hx as (_ & _ & Hf).
assert (Hal : (b + (1 + k) * PGSZ) mod 4096 = 0).
{ unfold PGSZ in *. rewrite Z.add_mod by lia. rewrite A3. rewrite Z.mod_mul by lia. reflexivity. }
destruct (Hf Hal ltac:(pose proof (mmap_len_ge PGSZ ltac:(unfold PGSZ; lia)); unfold PGSZ in *; lia)) as [_ Hforced].
rewrite (mprotect_not_refusable_of_live mo _ _ Hq Hlive) in Hforced. discriminate Hforced.
- rewrite eff_ret_ecore. pose proof (dec_mprotect_Some _ _ _ _ Hd) as E. cbn beta iota in E. rewrite E. reflexivity.
- rewrite eff_ret_ecore. pose proof (dec_mprotect_Some _ _ _ _ Hd) as E. cbn beta iota in E. rewrite E. reflexivity.
Qed.

Ltac flat_shape W :=
unfold mbind, msys, mret, mget, mupd, enode, ebind in W |- *; cbn [X1bs.bind fst snd] in W |- *.

Theorem ev_step_L B L e G s0 : B <= LBUDGET -> frame_ok G -> event_pre L e ->
mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo /\ BOUND L e B) (ev_step (ld_ceil L) e)
(fun z s mo => ev_step_post L e G s0 z s mo /\ LI (event_post L e z) mo).
Proof.
intros HBL HG Hpre s mo (-> & HK & HLI & HGs & HB).
assert (HBM : B <= BMAX) by (unfold LBUDGET, BMAX in *; lia).
pose proof (ev_step_spec (ok:=ok_all) L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
assert (FIN : forall z mo' (s' : PState), answer_ok L e z = true -> LI (event_post L e z) mo' -> ev_step_post L e G s0 z s' mo' -> step_live B mo').
{ intros z mo' s' Ha HL' (_ & HK' & _). split.
- apply LI_elim in HL'. unfold vm_live_bytes in HL'. pose proof (proj1 HB z Ha). lia.
- apply mem_quiet_of; [exact (kl_minv _ _ _ HK')| exact (LI_nomat _ _ HL')]. }
destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
-
unfold ev_step in W |- *.
destruct (Z.eqb_spec req 0) as [->|NZ].
+ flat_shape W. eapply vis_flat_L; [| apply nroomE_I; exact I| exact W|].
{ intros rsp. destruct (dec_brk0 rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_brk0 rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate]. assert (Ez : z = x) by congruence. subst x.
destruct Hpre as [[_ Hph]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]].
2:{ exfalso. pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as (Ecur & _). pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia. }
2:{ exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia. }
pose proof (li_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLI Hph Hst) as HL'.
change (event_post L (EBrk 0) z) with (set_brkph (BPQueried z) L). split; [exact HL'| exact (FIN z mo' _ Hans HL' (conj Hans HP))].
+ flat_shape W. eapply vis_flat_L; [| apply nroomE_I; exact I| exact W|].
{ intros rsp. destruct (dec_brk (ps_brk s0) req rsp) as [[|]|]; reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_brk (ps_brk s0) req rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
assert (Ez : z = match x with BrkGrown => req | BrkSame => ps_brk s0 end) by (destruct x; cbn in Ek; congruence).
destruct Hpre as [[E _]|Hpre]; [exfalso; exact (NZ E)|].
pose proof (li_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLI Hpre Hst Hd) as HL'. rewrite <- Ez in HL'.
split; [exact HL'| exact (FIN z mo' _ Hans HL' (conj Hans HP))].
-
unfold ev_step in W |- *.
destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
+ change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in *. cbn iota in W |- *.
destruct Hprot as [-> | ->].
* change (PROT_NONE =? 0) with true in *. cbn iota in W |- *. flat_shape W.
pose proof (nroom_of_ledger B L (ps_brk s0) mo len PROT_NONE HK HLI Hlen (or_introl eq_refl) HBM (proj1 HB) (proj2 HB)) as HRM.
eapply vis_flat_L; [| exact (conj HRM (anon_no_enomem B L (ps_brk s0) mo len PROT_NONE HK HLI Hlen (or_introl eq_refl) HBL HRM))| exact W|].
{ intros rsp. destruct (dec_mmap_none (ld_ceil L) len [] rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_mmap_none (ld_ceil L) len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
pose proof (li_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
split; [exact HL'| exact (FIN _ mo' _ Hans HL' (conj Hans HP))].
* change (PROT_RW =? 0) with false in *. cbn iota in W |- *. flat_shape W.
pose proof (nroom_of_ledger B L (ps_brk s0) mo len PROT_RW HK HLI Hlen (or_intror eq_refl) HBM (proj1 HB) (proj2 HB)) as HRM.
eapply vis_flat_L; [| exact (conj HRM (anon_no_enomem B L (ps_brk s0) mo len PROT_RW HK HLI Hlen (or_intror eq_refl) HBL HRM))| exact W|].
{ intros rsp. destruct (dec_mmap (ld_ceil L) len [] rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_mmap (ld_ceil L) len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
pose proof (li_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
split; [exact HL'| exact (FIN _ mo' _ Hans HL' (conj Hans HP))].
+ change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbn iota in W |- *. flat_shape W.
eapply vis_flat_L; [| (split; [cbn [nroom]; intros _ Hf; exfalso; cbv in Hf; discriminate Hf| cbn [no_enomem]; intros Hf; exfalso; cbv in Hf; discriminate Hf])| exact W|].
{ intros rsp. destruct (dec_mmap_fixed (round_up_pg cur) PGSZ rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
pose proof (li_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLI Hph Hst) as HL'.
split; [exact HL'| exact (FIN _ mo' _ Hans HL' (conj Hans HP))].
-
unfold ev_step in W |- *. destruct Hpre as (Hq & l0 & Hin & Hlen). flat_shape W. eapply vis_flat_L; [| apply nroomE_I; exact I| exact W|].
{ intros rsp. destruct (dec_munmap addr len rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
pose proof (li_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLI Hin Hlen Hst) as HL'.
split; [exact HL'| exact (FIN _ mo' _ Hans HL' (conj Hans HP))].
-
unfold ev_step in W |- *. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). flat_shape W.
eapply vis_flat_L; [| split; [exact I| exact (mprotect_no_enomem B L (ps_brk s0) mo b l k HK HLI Hin Hk HBL (proj1 HB))]| exact W|].
{ intros rsp. destruct (dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
pose proof (li_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLI Hin Hk Hst) as HL'.
split; [exact HL'| exact (FIN _ mo' _ Hans HL' (conj Hans HP))].
Qed.

Fixpoint qtree {R} (B : Z) (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
match t with
| SRet r => Post L r
| SVis e k => event_pre L e /\ BOUND L e B /\ forall z, answer_ok L e z = true -> qtree B (event_post L e z) (k z) Post
end.

Lemma qtree_mono {R} B L (t : stree ev Z R) (P P' : mled -> R -> Prop) :
qtree B L t P -> (forall L' r, P L' r -> P' L' r) -> qtree B L t P'.
Proof.
revert L. induction t as [r|e k IH]; intros L H HP; cbn in *; [apply HP; exact H|].
destruct H as (He & HB & Hk). split; [exact He|]. split; [exact HB|]. intros z Hz. apply IH; [apply Hk; exact Hz| exact HP].
Qed.

Lemma qtree_ctree_ok {R} B L (t : stree ev Z R) P : qtree B L t P -> ctree_ok L t P.
Proof.
revert L. induction t as [r|e k IH]; intros L H; cbn in *; [exact H|].
destruct H as (He & HB & Hk). split; [exact He|]. intros z Hz. apply IH. apply Hk. exact Hz.
Qed.

Theorem membedL {R} B (t : stree ev Z R) : B <= LBUDGET -> forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0 c,
frame_ok G -> qtree B L t Post -> ld_ceil L = c ->
mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ G s mo) (membed c t)
(fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ G s mo
/\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
intros HBM. induction t as [r|e k IH]; intros Post G L s0 c HG Hq Hc.
- cbn [membed]. apply mspecL_ret. intros s mo (-> & HK & HL & HGs). exists L. split; [constructor|]. cbn in Hq. split; [exact Hq|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. auto.
- cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HB & Hk). subst c.
eapply mspecL_bind.
{ eapply mspecL_pre; [apply (ev_step_L B L e G s0 HBM HG Hpre)|]. intros s mo (-> & HK & HL & HGs). split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs| exact HB]. }
intros z. apply mspecL_pointwise. intros s1 mo1 [(Hans & HK1 & HG1 & Hm & Hfa & Hso) HL1].
eapply mspecL_conseq; [apply (IH z Post G (event_post L e z) s1 (ld_ceil L) HG (Hk z Hans) (event_post_ld_ceil L e z))| |].
+ intros s mo [-> ->]. auto.
+ intros r s mo (L' & Hp & HP & HK & HL' & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HG'|]. repeat split; congruence.
Qed.
