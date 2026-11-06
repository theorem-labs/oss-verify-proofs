(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YFfn.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/YFfn.v (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK16 YK0n YK11 YK0h YK0i YK14 YK1c YK0v YK02 YK0p YK15 YK18 YK0y YK1b YK00 YK01 YK13 YP0n YK04 YK05 YA0i YA0n YA05 YA09 YK0g YA08 YG0b.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0f YG0n YG0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section K.
Variable segs : list Segment.
Theorem munmap_node : forall regs (pc : word) mem rom md (a : word) (len : Z),
m_halted md = None ->
getr regs 17 = Z_to_bv 64 215 ->
getr regs 10 = a -> bv_unsigned a mod page_size = 0 ->
getr regs 11 = Z_to_bv 64 len -> 0 < len ->
bv_unsigned a + page_round_up_Z len <= TASK_SIZE ->
map_has (vm_maps (m_vmmaps md)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
let n := Z_to_bv 64 (page_round_up_Z len) in
node_ok segs (mkCfg (pend_at regs pc mem rom) md) unit (fun _ => [])
(fun _ => mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom) (munmap_model a n md)).
Proof.
intros regs pc mem rom md a len Hh H17 H10 Hal H11 Hlen Hnw Hhas n.
assert (Hlen' : len < two_pow_64).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
assert (Hno : bv_unsigned (getr regs 17) = 215) by (rewrite H17; apply u64_lit; lia).
pose proof (pend_gpr0 regs pc mem rom) as H0. pose proof (pend_gpr1 regs pc mem rom) as G1. rewrite H10 in H0. rewrite H11 in G1.
assert (UF : advance_past_svc (apply_effect (pend_at regs pc mem rom) (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] [])) = mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (unfill a n mem) rom).
{ rewrite adv_pend. cbn [eff_ret]. rewrite effmem_unmaps. f_equal. apply FunctionalExtensionality.functional_extensionality. intros x.
unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd]. rewrite Bool.orb_false_r. reflexivity. }
set (ms := pend_at regs pc mem rom) in *.
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ rewrite G1. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = n) by (unfold page_round_up; rewrite Hu1; reflexivity).
assert (Hargs : munmap_args_ok ms md).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intros Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz. change (bv_unsigned (Z_to_bv 64 0)) with 0 in Hz. lia. }
pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) md eff Hno) (munmap_check_modeled ms md eff Hargs)) as Hchk. rewrite H0, Hpr in Hchk.
rewrite <- UF.
apply (node_det_noacc segs ms md (getr regs 17) (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []) (munmap_model a n md) []);
[exact Hh | reflexivity | | | rewrite munmap_model_halted; exact Hh | reflexivity].
- intros eff m' evs. split.
+ intros Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb us [(a, n)]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
+ intros (-> & -> & ->). rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
Qed.
Lemma same_io_munmap : forall a n md, same_io md (munmap_model a n md).
Proof. intros a n md. unfold munmap_model, with_mmap_destroyed, vm_forget_range. eapply same_io_trans; [apply same_io_with_vmmaps | apply same_io_with_vm_backing]. Qed.
Lemma munmap_lazy : forall a n md, m_vm_lazy (munmap_model a n md) = maps_subtract (m_vm_lazy md) (bv_unsigned a) (bv_unsigned a + bv_unsigned n).
Proof. intros. unfold munmap_model, with_mmap_destroyed, vm_forget_range. rewrite m_vm_lazy_with_vm_backing. rewrite with_vmmaps_lazy'. reflexivity. Qed.
Lemma munmap_materialized : forall a n md, m_vm_materialized (munmap_model a n md) =
List.filter (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized md).
Proof. intros. unfold munmap_model, with_mmap_destroyed, vm_forget_range. rewrite m_vm_materialized_with_vm_backing. reflexivity. Qed.
Lemma munmap_limit : forall a n md, vm_limit (m_vmmaps (munmap_model a n md)) = vm_limit (m_vmmaps md).
Proof. intros. unfold munmap_model, with_mmap_destroyed, vm_forget_range. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps. reflexivity. Qed.
Theorem munmap_AI : forall (Hh : word -> bool) A md (e : word * word) l1 l2,
AI segs Hh A md -> amwf md -> vm_maps (m_vmmaps md) = l1 ++ e :: l2 ->
bv_unsigned (fst e) mod page_size = 0 -> bv_unsigned (fst e) + bv_unsigned (snd e) < 2 ^ 64 ->
AI segs Hh A (munmap_model (fst e) (snd e) md).
Proof.
intros Hh A md e l1 l2 HAI MW EM Hal Hhi. set (md' := munmap_model (fst e) (snd e) md).
destruct (eager_used_munmap e md l1 l2 MW EM) as [EG _]. fold md' in EG. pose proof (esec_nonneg (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) [(bv_unsigned (fst e), bv_unsigned (snd e))]) as EN.
destruct MW as [(W1 & W2 & W3 & _) _].
assert (Wl : YK0g.ivs_wf (m_vm_lazy md)) by (intros q Hq; exact (W3 q Hq)).
pose proof (bv_unsigned_in_range 64 (fst e)) as Ra. pose proof (bv_unsigned_in_range 64 (snd e)) as Rn. unfold bv_modulus in Ra, Rn.
destruct HAI as (H1 & H2 & H3 & H4 & H5).
split; [exact H1|]. split; [exact H2|]. split; [|split].
-
intros w Hp Hw. apply (H3 w); [|exact Hw]. subst md'. rewrite munmap_lazy in Hp.
exact (page_in_subtract_back (m_vm_lazy md) (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) (page_base w) ltac:(lia) ltac:(lia) Wl Hp).
-
destruct H4 as [N1 N2 N3 N4 N5]. subst md'. constructor; rewrite ?munmap_materialized, ?munmap_lazy, ?munmap_limit.
+ apply NoDup_filter. exact N1.
+ intros p Hp. apply filter_In in Hp as [Hp _]. exact (N2 p Hp).
+ intros p Hp. apply filter_In in Hp as [Hp _]. exact (N3 p Hp).
+ intros p Hp. apply filter_In in Hp as [Hp Ho]. unfold page_outside_range in Ho. apply Bool.negb_true_iff in Ho.
apply page_in_subtract_keep; [lia | lia | lia | exact Wl | | exact (N4 p Hp)].
pose proof (N2 p Hp) as AL. unfold page_size in *.
apply Bool.andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho; left | apply Z.ltb_ge in Ho; right; lia].
apply Z.mod_divide in Hal as [qa Hqa]; [|lia]. apply Z.mod_divide in AL as [qp Hqp]; [|lia]. rewrite Hqa, Hqp in *. nia.
+ lia.
- subst md'. rewrite munmap_model_halted. exact H5.
Qed.
Lemma pairwise_remove_mid : forall {X} (R : X -> X -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) -> pairwise R (l1 ++ l2).
Proof.
intros X R l1 x l2. induction l1 as [|y t IH]; cbn [app pairwise].
- intros [_ P]. exact P.
- intros [F P]. split; [| exact (IH P)]. apply Forall_forall. intros z Hz. apply (proj1 (Forall_forall _ _) F z).
apply in_app_iff in Hz as [Hz|Hz]; apply in_app_iff; [left | right; right]; exact Hz.
Qed.
Theorem munmap_amwf : forall md (e : word * word) l1 l2,
amwf md -> vm_maps (m_vmmaps md) = l1 ++ e :: l2 -> amwf (munmap_model (fst e) (snd e) md).
Proof.
intros md e l1 l2 MW EM. destruct (eager_used_munmap e md l1 l2 MW EM) as [_ VM']. destruct MW as [(W1 & W2 & W3 & PW & ISP) NE].
pose proof (bv_unsigned_in_range 64 (snd e)) as Rn. unfold bv_modulus in Rn.
assert (SUB : forall q, In q (l1 ++ l2) -> In q (vm_maps (m_vmmaps md))).
{ intros q Hq. rewrite EM. apply in_app_iff in Hq as [Hq|Hq]; apply in_app_iff; [left | right; right]; exact Hq. }
split; [split; [|split; [|split; [|split; [|exact ISP]]]]|]; rewrite ?VM', ?munmap_lazy.
- intros q Hq. exact (W1 q (SUB q Hq)).
- intros q Hq. unfold munmap_model, with_mmap_destroyed, vm_forget_range in Hq. rewrite m_vmmaps_with_vm_backing, m_vmmaps_with_vmmaps in Hq. cbn [vm_noaccess] in Hq.
exact (YK0g.maps_subtract_wf (vm_noaccess (m_vmmaps md)) (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) (fun q Hq => W2 q Hq) ltac:(lia) q Hq).
- intros q Hq. exact (YK0g.maps_subtract_wf (m_vm_lazy md) (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) (fun q Hq => W3 q Hq) ltac:(lia) q Hq).
- rewrite EM in PW. exact (pairwise_remove_mid _ l1 e l2 PW).
- intros q Hq. exact (NE q (SUB q Hq)).
Qed.
Definition zz_eqb (x y : Z * Z) : bool := (fst x =? fst y) && (snd x =? snd y).
Lemma zz_eqb_eq : forall x y, zz_eqb x y = true <-> x = y.
Proof.
intros [a b] [c d]. unfold zz_eqb. cbn [fst snd]. rewrite Bool.andb_true_iff, !Z.eqb_eq. split; [intros [-> ->]; reflexivity | intros H; injection H as -> ->; auto].
Qed.
Definition A_drop (iv : Z * Z) (A : list (Z * Z)) : list (Z * Z) := List.filter (fun x => negb (zz_eqb x iv)) A.
Lemma A_drop_In : forall iv A x, In x (A_drop iv A) <-> In x A /\ x <> iv.
Proof.
intros iv A x. unfold A_drop. rewrite filter_In. rewrite Bool.negb_true_iff. split; intros [H1 H2]; (split; [exact H1|]).
- intros ->. rewrite (proj2 (zz_eqb_eq iv iv) eq_refl) in H2. discriminate.
- destruct (zz_eqb x iv) eqn:E; [|reflexivity]. apply zz_eqb_eq in E. exfalso. exact (H2 E).
Qed.
Lemma A_drop_wf : forall iv A, A_wf A -> A_wf (A_drop iv A).
Proof. intros iv A H. unfold A_drop. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hx _]. exact (proj1 (Forall_forall _ _) H x Hx). Qed.
Lemma A_bytes_refund : forall iv A, A_wf A -> In iv A -> A_bytes (A_drop iv A) <= A_bytes A - (snd iv - fst iv).
Proof.
intros iv A WF Hin. induction A as [|x A IH]; [destruct Hin|]. apply Forall_cons_iff in WF as [[Wx _] WF].
unfold A_drop. cbn [List.filter A_bytes]. fold (A_drop iv A). destruct (zz_eqb x iv) eqn:E; cbn [negb A_bytes].
- apply zz_eqb_eq in E. subst x.
assert (GE : A_bytes (A_drop iv A) <= A_bytes A).
{ clear IH Hin. induction A as [|y A IH2]; [cbn; lia|]. apply Forall_cons_iff in WF as [[Wy _] WF]. unfold A_drop. cbn [List.filter A_bytes]. fold (A_drop iv A).
destruct (zz_eqb y iv); cbn [negb A_bytes]; specialize (IH2 WF); lia. }
lia.
- destruct Hin as [->|Hin]; [rewrite (proj2 (zz_eqb_eq iv iv) eq_refl) in E; discriminate|]. specialize (IH WF Hin). lia.
Qed.
Definition wrefund (W : world segs) (iv : Z * Z) : world segs :=
mkW segs (w_H W) (A_drop iv (w_A W)) (w_Hoff W) (A_drop_wf iv (w_A W) (w_Awf W)).
Lemma wrefund_wle : forall W iv, wle W (wrefund W iv).
Proof. intros W iv. unfold wle, wrefund. cbn [w_H]. intros a Ha. exact Ha. Qed.
Lemma wrefund_H : forall W iv, w_H (wrefund W iv) = w_H W. Proof. reflexivity. Qed.
Lemma wrefund_A : forall W iv, w_A (wrefund W iv) = A_drop iv (w_A W). Proof. reflexivity. Qed.
Theorem AI_refund : forall (W : world segs) md (e : word * word) l1 l2,
AI segs (w_H W) (w_A W) md -> amwf md -> vm_maps (m_vmmaps md) = l1 ++ e :: l2 ->
bv_unsigned (fst e) mod page_size = 0 -> bv_unsigned (fst e) + bv_unsigned (snd e) < 2 ^ 64 ->
let iv := (bv_unsigned (fst e), bv_unsigned (fst e) + bv_unsigned (snd e)) in
AI segs (w_H (wrefund W iv)) (w_A (wrefund W iv)) (munmap_model (fst e) (snd e) md).
Proof.
intros W md e l1 l2 HAI MW EM Hal Hhi iv. pose proof (munmap_AI (w_H W) (w_A W) md e l1 l2 HAI MW EM Hal Hhi) as AI1.
rewrite wrefund_H, wrefund_A. set (md' := munmap_model (fst e) (snd e) md) in *.
pose proof (bv_unsigned_in_range 64 (fst e)) as Ra. pose proof (bv_unsigned_in_range 64 (snd e)) as Rn. unfold bv_modulus in Ra, Rn.
assert (NL : forall p : word, page_in_ranges p (m_vm_lazy md') = true -> ~ (fst iv <= bv_unsigned p /\ bv_unsigned p + page_size <= snd iv)).
{ intros p Hp [B1 B2]. subst md' iv. cbn [fst snd] in B1, B2. rewrite munmap_lazy in Hp.
rewrite (page_in_subtract_false (m_vm_lazy md) (bv_unsigned (fst e)) (bv_unsigned (fst e) + bv_unsigned (snd e)) p ltac:(lia) ltac:(lia) B1 B2) in Hp. discriminate. }
assert (NM : forall p : word, In p (m_vm_materialized md') -> ~ (fst iv <= bv_unsigned p /\ bv_unsigned p + page_size <= snd iv)).
{ intros p Hp [B1 B2]. subst md' iv. cbn [fst snd] in B1, B2. rewrite munmap_materialized in Hp. apply filter_In in Hp as [_ Ho].
unfold page_outside_range in Ho. apply Bool.negb_true_iff in Ho. apply Bool.andb_false_iff in Ho as [Ho|Ho]; [apply Z.leb_gt in Ho | apply Z.ltb_ge in Ho]; unfold page_size in *; lia. }
assert (KEEP : forall p : word, ~ (fst iv <= bv_unsigned p /\ bv_unsigned p + page_size <= snd iv) ->
page_allowedb (w_A W) p = true -> page_allowedb (A_drop iv (w_A W)) p = true).
{ intros p Hn Hp. unfold page_allowedb in *. apply existsb_exists in Hp as (x & Hx & Hb). apply existsb_exists. exists x. split; [|exact Hb].
apply A_drop_In. split; [exact Hx|]. intros ->. apply Hn. apply Bool.andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. lia. }
destruct AI1 as (H1 & H2 & H3 & H4 & H5).
apply (AI_reset_A segs (w_H W) (w_A W) (A_drop iv (w_A W)) md' (conj H1 (conj H2 (conj H3 (conj H4 H5)))) (A_drop_wf iv _ H2)).
- intros w Hp Hw. apply KEEP; [exact (NL _ Hp) | exact (H3 w Hp Hw)].
- intros p Hp. apply KEEP; [exact (NM p Hp) | exact (minv_allowed _ _ H4 p Hp)].
- pose proof (minv_budget _ _ H4) as BU. assert (A_bytes (A_drop iv (w_A W)) <= A_bytes (w_A W)); [|lia].
clear - H2. induction (w_A W) as [|y A IH]; [cbn; lia|]. apply Forall_cons_iff in H2 as [[Wy _] WF]. unfold A_drop. cbn [List.filter A_bytes]. fold (A_drop iv A).
destruct (zz_eqb y iv); cbn [negb A_bytes]; specialize (IH WF); lia.
Qed.
Theorem AI_refund_gen : forall (W : world segs) md (iv : Z * Z),
AI segs (w_H W) (w_A W) md ->
(forall p : word, page_in_ranges p (m_vm_lazy md) = true -> ~ (fst iv <= bv_unsigned p /\ bv_unsigned p + page_size <= snd iv)) ->
AI segs (w_H (wrefund W iv)) (w_A (wrefund W iv)) md.
Proof.
intros W md iv HAI NL. rewrite wrefund_H, wrefund_A.
assert (KEEP : forall p : word, ~ (fst iv <= bv_unsigned p /\ bv_unsigned p + page_size <= snd iv) ->
page_allowedb (w_A W) p = true -> page_allowedb (A_drop iv (w_A W)) p = true).
{ intros p Hn Hp. unfold page_allowedb in *. apply existsb_exists in Hp as (x & Hx & Hb). apply existsb_exists. exists x. split; [|exact Hb].
apply A_drop_In. split; [exact Hx|]. intros ->. apply Hn. apply Bool.andb_true_iff in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2. lia. }
destruct HAI as (H1 & H2 & H3 & H4 & H5).
apply (AI_reset_A segs (w_H W) (w_A W) (A_drop iv (w_A W)) md (conj H1 (conj H2 (conj H3 (conj H4 H5)))) (A_drop_wf iv _ H2)).
- intros w Hp Hw. apply KEEP; [exact (NL _ Hp) | exact (H3 w Hp Hw)].
- intros p Hp. apply KEEP; [exact (NL p (minv_lazy _ _ H4 p Hp)) | exact (minv_allowed _ _ H4 p Hp)].
- pose proof (minv_budget _ _ H4) as BU. assert (A_bytes (A_drop iv (w_A W)) <= A_bytes (w_A W)); [|lia].
clear - H2. induction (w_A W) as [|y A IH]; [cbn; lia|]. apply Forall_cons_iff in H2 as [[Wy _] WF]. unfold A_drop. cbn [List.filter A_bytes]. fold (A_drop iv A).
destruct (zz_eqb y iv); cbn [negb A_bytes]; specialize (IH WF); lia.
Qed.
Lemma munmap_lazy_out : forall a n md (p : word),
YK0g.ivs_wf (m_vm_lazy md) -> bv_unsigned a + bv_unsigned n < 2 ^ 64 ->
page_in_ranges p (m_vm_lazy (munmap_model a n md)) = true ->
~ (bv_unsigned a <= bv_unsigned p /\ bv_unsigned p + page_size <= bv_unsigned a + bv_unsigned n).
Proof.
intros a n md p Wl Hhi Hp [B1 B2]. rewrite munmap_lazy in Hp.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 n) as Rn. unfold bv_modulus in Ra, Rn.
rewrite (page_in_subtract_false (m_vm_lazy md) (bv_unsigned a) (bv_unsigned a + bv_unsigned n) p ltac:(lia) ltac:(lia) B1 B2) in Hp. discriminate.
Qed.
Lemma map_has_In : forall (l : list (word * word)) a n, In (a, n) l -> map_has l a n = true.
Proof.
intros l a n Hin. unfold map_has. apply existsb_exists. exists (a, n). split; [exact Hin|]. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.
End K.
End f.
