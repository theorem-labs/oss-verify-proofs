(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YA06.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15 YK18 YK0y YK1b YK00 YK01 YK13 YP0n YK04 YK05 YA0i YA0n YA05 YK0g.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Lemma madvise_next_vmmaps : forall md a n, m_vmmaps (madvise_dontneed_next md a n) = m_vmmaps md.
Proof. reflexivity. Qed.
Lemma madvise_next_lazy : forall md a n, m_vm_lazy (madvise_dontneed_next md a n) = m_vm_lazy md.
Proof. reflexivity. Qed.
Lemma madvise_next_materialized : forall md a n,
m_vm_materialized (madvise_dontneed_next md a n)
= List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized md).
Proof. reflexivity. Qed.
Lemma madvise_next_halted : forall md a n, m_halted (madvise_dontneed_next md a n) = m_halted md.
Proof. reflexivity. Qed.
Lemma madvise_next_eager : forall md a n, eager_used (madvise_dontneed_next md a n) = eager_used md.
Proof. reflexivity. Qed.
Lemma madvise_same_mat : forall md a n, same_but_materialized md (madvise_dontneed_next md a n).
Proof. reflexivity. Qed.
Lemma madvise_next_wvb : forall md0 mat a n,
madvise_dontneed_next (with_vm_backing (m_vm_lazy md0) mat md0) a n
= with_vm_backing (m_vm_lazy md0) (List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) mat) md0.
Proof. intros [fd [maps lazy mt] io fs proc lim tm] mat a n. reflexivity. Qed.
Lemma madvise_MInv : forall A md a n, MInv A md -> MInv A (madvise_dontneed_next md a n).
Proof.
intros A md a n [N1 N2 N3 N4 N5]. unfold madvise_dontneed_next. apply MInv_wvb.
- apply NoDup_filter. exact N1.
- intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
- intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
- intros p Hp. apply filter_In in Hp as [Hp _]. exact (N4 p Hp).
- exact N5.
Qed.
Lemma region_free_forall : forall l (lo n : word),
region_free l lo n = true <->
(forall q, In q l -> bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned lo \/ bv_unsigned lo + bv_unsigned n <= bv_unsigned (fst q)).
Proof.
induction l as [|[a sz] l IH]; intros lo n; cbn [region_free].
- split; [intros _ q [] | reflexivity].
- rewrite Bool.andb_true_iff, IH. unfold iv_overlap. split.
+ intros [H1 H2] q [<-|Hq]; [|exact (H2 q Hq)]. cbn [fst snd].
apply Bool.negb_true_iff, Bool.andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
+ intros H. split; [|intros q Hq; apply H; right; exact Hq].
specialize (H (a, sz) (or_introl eq_refl)). cbn [fst snd] in H.
apply Bool.negb_true_iff, Bool.andb_false_iff. destruct H as [H|H]; [left | right]; apply Z.ltb_ge; lia.
Qed.
Lemma region_free_sub : forall l (lo n lo' n' : word),
region_free l lo n = true ->
bv_unsigned lo <= bv_unsigned lo' -> bv_unsigned lo' + bv_unsigned n' <= bv_unsigned lo + bv_unsigned n ->
region_free l lo' n' = true.
Proof.
intros l lo n lo' n' H H1 H2. apply region_free_forall. intros q Hq.
destruct (proj1 (region_free_forall l lo n) H q Hq); lia.
Qed.
Lemma iv_subtract_inside : forall (a sz : word) lo hi q,
bv_unsigned a + bv_unsigned sz <= 2 ^ 64 -> In q (iv_subtract a sz lo hi) ->
bv_unsigned a <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned a + bv_unsigned sz.
Proof.
intros a sz lo hi q Hwf Hin. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.
Lemma region_free_subtract : forall l lo hi (b n : word),
(forall q, In q l -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64) ->
region_free l b n = true -> region_free (maps_subtract l lo hi) b n = true.
Proof.
intros l lo hi b n Hwf H. apply region_free_forall. intros q Hq.
assert (X : exists r, In r l /\ bv_unsigned (fst r) <= bv_unsigned (fst q) /\ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst r) + bv_unsigned (snd r)).
{ clear H. induction l as [|[a sz] l IH]; [destruct Hq|]. cbn [maps_subtract] in Hq. apply in_app_iff in Hq as [Hq|Hq].
- exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_inside a sz lo hi q (Hwf (a, sz) (or_introl eq_refl)) Hq).
- destruct (IH (fun r Hr => Hwf r (or_intror Hr)) Hq) as (r & Hr & X). exists r. split; [right; exact Hr | exact X]. }
destruct X as (r & Hr & X1 & X2). destruct (proj1 (region_free_forall l b n) H r Hr); lia.
Qed.
Lemma iv_subtract_pos : forall (a sz : word) lo hi q,
0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2 ^ 64 -> In q (iv_subtract a sz lo hi) -> 0 < bv_unsigned (snd q).
Proof.
intros a sz lo hi q Hpos Hwf Hin. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
- destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.
Lemma maps_subtract_pos : forall l lo hi,
(forall q, In q l -> bv_unsigned (fst q) + bv_unsigned (snd q) <= 2 ^ 64) ->
Forall (fun iv => 0 < bv_unsigned (snd iv)) l -> Forall (fun iv => 0 < bv_unsigned (snd iv)) (maps_subtract l lo hi).
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hwf HP; [constructor|].
apply Forall_cons_iff in HP as [P1 HPl]. cbn [fst snd] in P1. cbn [maps_subtract]. apply Forall_app. split.
- apply Forall_forall. intros q Hq. exact (iv_subtract_pos a sz lo hi q P1 (Hwf (a, sz) (or_introl eq_refl)) Hq).
- apply IH; [intros q Hq; apply Hwf; right; exact Hq | exact HPl].
Qed.
Lemma region_free_of_uncovered : forall l (lo n : word),
(forall q, In q l -> 0 < bv_unsigned (snd q)) -> 0 < bv_unsigned n ->
(forall x, bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n -> covered l x = false) ->
region_free l lo n = true.
Proof.
intros l lo n Hpos Hn Hcov. apply region_free_forall. intros q Hq. specialize (Hpos q Hq).
destruct (Z_le_gt_dec (bv_unsigned (fst q) + bv_unsigned (snd q)) (bv_unsigned lo)) as [|G1]; [left; assumption|].
destruct (Z_le_gt_dec (bv_unsigned lo + bv_unsigned n) (bv_unsigned (fst q))) as [|G2]; [right; assumption|]. exfalso.
set (x := Z.max (bv_unsigned lo) (bv_unsigned (fst q))).
assert (Hx : bv_unsigned lo <= x < bv_unsigned lo + bv_unsigned n) by (subst x; lia).
specialize (Hcov x Hx). assert (Hc : covered l x = true); [|congruence].
clear Hcov. induction l as [|p l IH]; [destruct Hq|]. cbn [covered]. apply Bool.orb_true_iff.
destruct Hq as [->|Hq]; [left | right; exact (IH Hq)].
unfold in_iv, B, S. apply Bool.andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; subst x; lia.
Qed.
Lemma madvise_gate_intro : forall (h : VmMaps) (e : word * word) (a n : word),
In e (vm_maps h) -> bv_unsigned (fst e) <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
region_free (vm_reserved h) a n = true -> region_free (vm_noaccess h) a n = true ->
madvise_dontneed_ok h a n = true.
Proof.
intros h e a n He H1 H2 HR HN. unfold madvise_dontneed_ok. rewrite HR, HN, Bool.andb_true_r. cbn [andb].
unfold map_contains. apply existsb_exists. exists e. split; [exact He|]. apply Bool.andb_true_iff. split; apply Z.leb_le; assumption.
Qed.
Section c. Context {fx : YK11.FPState}.
Section K.
Variable segs : list Segment.
Lemma madvise_check : forall ms x8 model eff,
bv_unsigned x8 = 233%Z ->
check_syscall (sys_input segs ms x8) eff model = check_madvise (ms_gpr ms 0) (ms_gpr ms 1) (int32 (ms_gpr ms 2)) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.
Definition madvise_args_ok (ms : machine_state) (model : Model) : Prop :=
(bv_unsigned (ms_gpr ms 0) mod page_size = 0)%Z /\
bv_unsigned (int32 (ms_gpr ms 2)) = MADV_DONTNEED /\
ms_gpr ms 1 <> Z_to_bv 64 0 /\
(bv_unsigned (ms_gpr ms 0) + page_round_up_Z (bv_unsigned (ms_gpr ms 1)) < two_pow_64)%Z /\
madvise_dontneed_ok (m_vmmaps model) (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) = true.
Lemma madvise_check_modeled : forall ms model eff,
madvise_args_ok ms model ->
check_madvise (ms_gpr ms 0) (ms_gpr ms 1) (int32 (ms_gpr ms 2)) eff model
= match eff with
| mkEffectU r [] zs [] [] [] =>
if w_is0 r && listNN_eqb zs [(ms_gpr ms 0, page_round_up (ms_gpr ms 1))]
then CheckOk (madvise_dontneed_next model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1))) []
else CheckReject
| _ => CheckReject
end.
Proof.
intros ms model eff (Hal & Hadv & Hlen & Hnw & Hgate).
unfold check_madvise.
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
unfold madvise_dontneed_b. rewrite (proj2 (Z.eqb_eq _ _) Hadv). cbn [negb].
unfold w_is0 at 1. rewrite (bv_eqb_neq _ _ Hlen).
rewrite (proj2 (Z.leb_gt _ _) Hnw). cbv zeta.
unfold page_round_up in Hgate. rewrite Hgate. reflexivity.
Qed.
Theorem madvise_node : forall regs (pc : word) mem rom md (a : word) (len : Z),
m_halted md = None ->
getr regs 17 = Z_to_bv 64 233 ->
getr regs 10 = a -> bv_unsigned a mod page_size = 0 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len ->
getr regs 12 = Z_to_bv 64 4 ->
bv_unsigned a + page_round_up_Z len < 2 ^ 64 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
madvise_dontneed_ok (m_vmmaps md) a n = true ->
node_ok segs (mkCfg (pend_at regs pc mem rom) md) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill a n mem) rom) (madvise_dontneed_next md a n)).
Proof.
intros regs pc mem rom md a len Hh H17 H10 Hal H11 Hlen H12 Hnw n Hgate.
assert (Hlen' : len < two_pow_64).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold two_pow_64 in *. lia. }
assert (Hno : bv_unsigned (getr regs 17) = 233) by (rewrite H17; apply u64_lit; lia).
pose proof (pend_gpr0 regs pc mem rom) as H0. pose proof (pend_gpr1 regs pc mem rom) as G1. pose proof (pend_gpr2 regs pc mem rom) as G2.
rewrite H10 in H0. rewrite H11 in G1. rewrite H12 in G2.
assert (ZF : advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU (Z_to_bv 64 0) [] [(a, n)] [] [] []))
= mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill a n mem) rom).
{ rewrite adv_pend. cbn [eff_ret]. rewrite effmem_zeros. unfold zfill. rewrite (apply_zeros_one mem a n). reflexivity. }
set (ms := pend_at regs pc mem rom) in *.
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ rewrite G1. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = n) by (unfold page_round_up; rewrite Hu1; reflexivity).
assert (Hargs : madvise_args_ok ms md).
{ unfold madvise_args_ok. rewrite H0, G2, Hu1, Hpr. split; [exact Hal|]. split; [reflexivity|]. split; [|split; [unfold two_pow_64; exact Hnw | exact Hgate]].
rewrite G1. intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite u64_lit in Hz by (unfold two_pow_64 in Hlen'; lia).
change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hz. lia. }
pose proof (fun eff => eq_trans (madvise_check ms (getr regs 17) md eff Hno) (madvise_check_modeled ms md eff Hargs)) as Hchk. rewrite H0, Hpr in Hchk.
rewrite <- ZF.
apply (node_det_noacc segs ms md (getr regs 17) (mkEffectU (Z_to_bv 64 0) [] [(a, n)] [] [] []) (madvise_dontneed_next md a n) []);
[exact Hh | reflexivity | | | rewrite madvise_next_halted; exact Hh | reflexivity].
- intros eff m' evs. split.
+ intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb zs [(a, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst zs. cbn [andb] in Hck. injection Hck as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
+ intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r && listNN_eqb zs _)%bool; discriminate.
Qed.
Theorem madvise_AI : forall (Hh : word -> bool) A md a n, AI segs Hh A md -> AI segs Hh A (madvise_dontneed_next md a n).
Proof.
intros Hh A md a n HAI. apply (AI_same segs Hh A md); [exact HAI | apply madvise_same_mat |].
apply madvise_MInv. exact (AI_MInv segs Hh A md HAI).
Qed.
Theorem SRr_madvise : forall (W : world segs) regs (pc : word) mem rom md (a : word) (len : Z) (Q : world segs -> config -> Prop),
getr regs 17 = Z_to_bv 64 233 ->
getr regs 10 = a -> bv_unsigned a mod page_size = 0 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len ->
getr regs 12 = Z_to_bv 64 4 ->
bv_unsigned a + page_round_up_Z len < 2 ^ 64 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
madvise_dontneed_ok (m_vmmaps md) a n = true ->
SRr segs W (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill a n mem) rom) (madvise_dontneed_next md a n)) Q ->
SRr segs W (mkCfg (pend_at regs pc mem rom) md) Q.
Proof.
intros W regs pc mem rom md a len Q H17 H10 Hal H11 Hlen H12 Hnw n Hgate HK.
apply SRr_use_AI. intros HAI. cbn [cfg_model] in HAI.
apply (SRr_node segs W _ unit (fun _ => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill a n mem) rom) (madvise_dontneed_next md a n)) tt Q).
- exact (madvise_node regs pc mem rom md a len (AI_halted segs _ _ _ HAI) H17 H10 Hal H11 Hlen H12 Hnw Hgate).
- intros [] HA. cbn [cfg_model] in *. apply madvise_AI. exact HA.
- intros []. exact HK.
Qed.
End K.
End c.
