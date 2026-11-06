(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Record lvp := mkLVP { lv_base : list (Z * Z); lv_excl : list (Z * Z); lv_bands : list (Z * Z); lv_shoff : Z }.

Definition zin (z : Z) (iv : Z * Z) : bool := (fst iv <=? z) && (z <? snd iv).
Definition in_zivs (z : Z) (l : list (Z * Z)) : bool := existsb (zin z) l.
Definition wiv2z (iv : word * word) : Z * Z :=
(bv_unsigned (fst iv), bv_unsigned (fst iv) + bv_unsigned (snd iv)).
Definition in_wivs (z : Z) (l : list (word * word)) : bool :=
existsb (fun iv => zin z (wiv2z iv)) l.
Definition nonempty (iv : Z * Z) : bool := fst iv <? snd iv.
Definition zoverlap (a b : Z * Z) : bool := (fst a <? snd a) && (fst b <? snd b) && (fst a <? snd b) && (fst b <? snd a).

Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.

Fixpoint zpages (lo : Z) (n : nat) : list word :=
match n with
| O => []
| S k => Z_to_bv 64 lo :: zpages (lo + 4096) k
end.

Definition pages_in (iv : Z * Z) : list word :=
let lo := pageup (fst iv) in
let hi := pagedown (snd iv) in
zpages lo (Z.to_nat ((hi - lo) / 4096)).

Definition pages_meeting (iv : Z * Z) : list word :=
pages_in (pagedown (fst iv), pageup (snd iv)).

Fixpoint zbytes (lo : Z) (k : nat) : list word :=
match k with O => [] | S k' => Z_to_bv 64 lo :: zbytes (lo + 1) k' end.
Definition bytes_of (iv : Z * Z) : list word := zbytes (fst iv) (Z.to_nat (snd iv - fst iv)).

Section LV.
Variable L : lvp.

Definition aligned (p : word) : bool := (bv_unsigned p mod 4096 =? 0).

Definition excl_entry (e : word * word) : bool := existsb (zoverlap (wiv2z e)) (lv_excl L).

Definition appvis (mo : Model) : list (Z * Z) :=
lv_base L ++ map wiv2z (List.filter (fun e => negb (excl_entry e)) (vm_maps (m_vmmaps mo))).

Definition shz (z : Z) : Z := lv_shoff L + z / 8.
Definition sh_iv (iv : Z * Z) : Z * Z := (shz (fst iv), shz (snd iv - 1) + 1).
Definition shivs (mo : Model) : list (Z * Z) := map sh_iv (List.filter nonempty (appvis mo)).

Definition allowed_byte (mo : Model) (z : Z) : bool := in_zivs z (appvis mo) || in_zivs z (shivs mo).

Definition hidden (mo : Model) (a : word) : bool := negb (allowed_byte mo (bv_unsigned a)).

Definition in_bands (a : word) : bool := in_zivs (bv_unsigned a) (lv_bands L).
Definition jsome (mo : Model) (m : word -> option byte) : Prop :=
forall x : word, in_bands x = true -> hidden mo x = true -> m x <> None.

Definition view (mo : Model) (m : word -> option byte) : word -> option byte :=
mrestrict (hidden mo) m.
Definition msview (mo : Model) (ms : machine_state) : machine_state :=
restrict (hidden mo) ms.

Definition page_meets (p : word) (iv : Z * Z) : bool :=
(fst iv <? snd iv) && (fst iv <? bv_unsigned p + 4096) && (bv_unsigned p <? snd iv).

Definition G (mo : Model) (p : word) : bool :=
aligned p && (existsb (page_meets p) (appvis mo) || existsb (page_meets p) (shivs mo)).

Lemma msview_mem : forall mo ms, ms_mem (msview mo ms) = view mo (ms_mem ms).
Proof. reflexivity. Qed.

Lemma msview_svc : forall mo ms, ms_svc_pending (msview mo ms) = ms_svc_pending ms.
Proof. reflexivity. Qed.

Lemma view_visible : forall mo m a, hidden mo a = false -> view mo m a = m a.
Proof. intros mo m a H. unfold view, mrestrict. rewrite H. reflexivity. Qed.

Lemma view_hidden : forall mo m a, hidden mo a = true -> view mo m a = None.
Proof. intros mo m a H. unfold view, mrestrict. rewrite H. reflexivity. Qed.

Lemma page_base_unsigned : forall a : word,
bv_unsigned (page_base a) = bv_unsigned a / 4096 * 4096.
Proof.
intros a. unfold page_base, page_base_of, page_size. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with (2^64) in *.
apply bv_wrap_small. change (bv_modulus 64) with (2^64). lia.
Qed.

Lemma page_base_aligned : forall a : word, aligned (page_base a) = true.
Proof.
intros a. unfold aligned. rewrite page_base_unsigned. apply Z.eqb_eq. apply Z_mod_mult.
Qed.

Lemma page_base_range : forall a : word,
bv_unsigned (page_base a) <= bv_unsigned a < bv_unsigned (page_base a) + 4096.
Proof.
intros a. rewrite page_base_unsigned. pose proof (Z.div_mod (bv_unsigned a) 4096 ltac:(lia)).
pose proof (Z.mod_pos_bound (bv_unsigned a) 4096 ltac:(lia)). lia.
Qed.

Definition weq_dec : forall x y : word, {x = y} + {x <> y} := @bv_eq_dec 64.

Definition cand (mo : Model) : list word :=
flat_map pages_meeting (List.filter nonempty (appvis mo)) ++ flat_map pages_meeting (shivs mo).

Definition allowed (mo : Model) : list word := nodup weq_dec (List.filter (G mo) (cand mo)).

Definition unmat (mo : Model) : list word :=
List.filter (fun p => negb (page_mem p (m_vm_materialized mo))) (allowed mo).

Definition Rsv (mo : Model) : Z := 4096 * Z.of_nat (length (unmat mo)).

Definition Phi (mo : Model) : Z := vm_backing_used mo + Rsv mo.

Definition cand_bytes (mo : Model) : Z := 4096 * Z.of_nat (length (cand mo)).

Definition msim (mo mo' : Model) : Prop :=
mo' = with_vm_backing (m_vm_lazy mo) (m_vm_materialized mo') mo.

Definition drift (mo mo' : Model) : Prop :=
exists P : list word,
List.NoDup P /\
(forall p, In p P -> G mo p = true /\ page_mem p (m_vm_materialized mo) = false) /\
mo' = with_vm_backing (m_vm_lazy mo) (P ++ m_vm_materialized mo) mo.

Definition vmeq (mo mo' : Model) : Prop :=
m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo.

Definition mapseq (mo mo' : Model) : Prop := vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo).

Lemma appvis_maps : forall mo mo', mapseq mo mo' -> appvis mo' = appvis mo.
Proof. intros mo mo' Hm. unfold appvis. rewrite Hm. reflexivity. Qed.
Lemma hidden_maps : forall mo mo', mapseq mo mo' -> forall a, hidden mo' a = hidden mo a.
Proof. intros mo mo' Hm a. unfold hidden, allowed_byte, shivs. rewrite (appvis_maps _ _ Hm). reflexivity. Qed.

Lemma G_maps : forall mo mo', mapseq mo mo' -> forall p, G mo' p = G mo p.
Proof. intros mo mo' Hm p. unfold G, shivs. rewrite (appvis_maps _ _ Hm). reflexivity. Qed.

Lemma appvis_ext : forall mo mo', vmeq mo mo' -> appvis mo' = appvis mo.
Proof. intros mo mo' [Hv _]. unfold appvis. rewrite Hv. reflexivity. Qed.
Lemma shivs_ext : forall mo mo', vmeq mo mo' -> shivs mo' = shivs mo.
Proof. intros mo mo' H. unfold shivs. rewrite (appvis_ext _ _ H). reflexivity. Qed.
Lemma allowed_byte_ext : forall mo mo', vmeq mo mo' -> forall z, allowed_byte mo' z = allowed_byte mo z.
Proof. intros mo mo' H z. unfold allowed_byte. rewrite (appvis_ext _ _ H), (shivs_ext _ _ H). reflexivity. Qed.
Lemma G_ext : forall mo mo', vmeq mo mo' -> forall p, G mo' p = G mo p.
Proof. intros mo mo' H p. unfold G. rewrite (appvis_ext _ _ H), (shivs_ext _ _ H). reflexivity. Qed.
Lemma hidden_ext : forall mo mo', vmeq mo mo' -> forall a, hidden mo' a = hidden mo a.
Proof. intros mo mo' H a. unfold hidden. rewrite (allowed_byte_ext _ _ H). reflexivity. Qed.
Lemma hidden_ext_fun : forall mo mo', vmeq mo mo' -> hidden mo' = hidden mo.
Proof. intros mo mo' H. apply FunctionalExtensionality.functional_extensionality. apply hidden_ext, H. Qed.

Lemma jsome_stable : forall mo mo' m m',
vmeq mo mo' -> (forall a, hidden mo a = true -> m' a = m a) -> jsome mo m -> jsome mo' m'.
Proof.
intros mo mo' m m' Hv Hm HJ x Hb Hh. rewrite (hidden_ext mo mo' Hv) in Hh. rewrite (Hm x Hh). exact (HJ x Hb Hh).
Qed.

Lemma jsome_mono : forall mo mo' m m',
(forall x, in_bands x = true -> hidden mo' x = true -> hidden mo x = true /\ (m x <> None -> m' x <> None)) ->
jsome mo m -> jsome mo' m'.
Proof. intros mo mo' m m' H HJ x Hb Hh. destruct (H x Hb Hh) as [Hh0 Hm]. apply Hm. exact (HJ x Hb Hh0). Qed.

Lemma msview_ext : forall mo mo', vmeq mo mo' -> forall ms, msview mo' ms = msview mo ms.
Proof. intros mo mo' H ms. unfold msview. rewrite (hidden_ext_fun _ _ H). reflexivity. Qed.
Lemma cand_ext : forall mo mo', vmeq mo mo' -> cand mo' = cand mo.
Proof. intros mo mo' H. unfold cand. rewrite (appvis_ext _ _ H), (shivs_ext _ _ H). reflexivity. Qed.
Lemma allowed_ext : forall mo mo', vmeq mo mo' -> allowed mo' = allowed mo.
Proof.
intros mo mo' H. unfold allowed. rewrite (cand_ext _ _ H). f_equal. apply filter_ext. intros p. apply G_ext, H.
Qed.
Lemma unmat_ext : forall mo mo', vmeq mo mo' -> m_vm_materialized mo' = m_vm_materialized mo -> unmat mo' = unmat mo.
Proof. intros mo mo' H Hm. unfold unmat. rewrite (allowed_ext _ _ H), Hm. reflexivity. Qed.
Lemma Rsv_ext : forall mo mo', vmeq mo mo' -> m_vm_materialized mo' = m_vm_materialized mo -> Rsv mo' = Rsv mo.
Proof. intros mo mo' H Hm. unfold Rsv. rewrite (unmat_ext _ _ H Hm). reflexivity. Qed.
Lemma vm_backing_used_ext : forall mo mo', vmeq mo mo' -> m_vm_materialized mo' = m_vm_materialized mo ->
vm_backing_used mo' = vm_backing_used mo.
Proof. intros mo mo' [Hv Hl] Hm. unfold vm_backing_used. rewrite Hv, Hl, Hm. reflexivity. Qed.
Lemma Phi_ext : forall mo mo', vmeq mo mo' -> m_vm_materialized mo' = m_vm_materialized mo -> Phi mo' = Phi mo.
Proof. intros mo mo' H Hm. unfold Phi. rewrite (vm_backing_used_ext _ _ H Hm), (Rsv_ext _ _ H Hm). reflexivity. Qed.

Lemma wvb_frame : forall l X m,
m_fd (with_vm_backing l X m) = m_fd m /\ m_vmmaps (with_vm_backing l X m) = m_vmmaps m /\
m_vm_lazy (with_vm_backing l X m) = l /\ m_vm_materialized (with_vm_backing l X m) = X /\
m_io (with_vm_backing l X m) = m_io m /\ m_fsys (with_vm_backing l X m) = m_fsys m /\
m_proc (with_vm_backing l X m) = m_proc m /\ m_lim (with_vm_backing l X m) = m_lim m /\
m_time (with_vm_backing l X m) = m_time m.
Proof. intros l X []; repeat split; reflexivity. Qed.

Lemma wvb_wvb : forall l X l' X' m,
with_vm_backing l X (with_vm_backing l' X' m) = with_vm_backing l X m.
Proof. intros l X l' X' []; reflexivity. Qed.

Lemma wvb_id : forall m, with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma msim_refl : forall mo, msim mo mo.
Proof. intros mo. unfold msim. symmetry. apply wvb_id. Qed.

Lemma msim_frame : forall mo mo', msim mo mo' ->
vmeq mo mo' /\ m_fd mo' = m_fd mo /\ m_io mo' = m_io mo /\ m_fsys mo' = m_fsys mo /\
m_proc mo' = m_proc mo /\ m_lim mo' = m_lim mo /\ m_time mo' = m_time mo.
Proof.
intros mo mo' ->. unfold vmeq. destruct mo as [fd [maps lazy mat] io fs proc lim tm]; repeat split; reflexivity.
Qed.

Lemma msim_sym : forall mo mo', msim mo mo' -> msim mo' mo.
Proof.
intros mo mo' H. unfold msim in *. rewrite H at 2. rewrite wvb_wvb.
rewrite H. destruct mo as [fd [maps lazy mat] io fs proc lim tm]. reflexivity.
Qed.

Lemma msim_trans : forall a b c, msim a b -> msim b c -> msim a c.
Proof.
intros a b c Hab Hbc. unfold msim in *. rewrite Hbc, Hab. rewrite wvb_wvb.
destruct a as [fd [maps lazy mat] io fs proc lim tm]; reflexivity.
Qed.

Lemma msim_facts : forall mo mo', msim mo mo' ->
m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo /\ m_tid mo' = m_tid mo /\
m_stdin mo' = m_stdin mo /\ m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo /\
(forall p, G mo' p = G mo p) /\ (forall a, hidden mo' a = hidden mo a) /\
allowed mo' = allowed mo /\ cand mo' = cand mo /\ (forall ms, msview mo' ms = msview mo ms).
Proof.
intros mo mo' H. pose proof (msim_frame _ _ H) as (Hv & Hfd & Hio & Hfs & Hpr & Hli & _).
unfold m_fds, m_fs, m_halted, m_tid, m_stdin. rewrite Hfd, Hio, Hfs, Hpr.
repeat split; try reflexivity; try apply Hv.
- apply G_ext, Hv. - apply hidden_ext, Hv. - apply allowed_ext, Hv. - apply cand_ext, Hv. - apply msview_ext, Hv.
Qed.

Lemma drift_msim : forall mo mo', drift mo mo' -> msim mo mo'.
Proof.
intros mo mo' (P & _ & _ & ->). unfold msim. destruct (wvb_frame (m_vm_lazy mo) (P ++ m_vm_materialized mo) mo) as (_ & _ & _ & -> & _).
reflexivity.
Qed.

Lemma drift_refl : forall mo, drift mo mo.
Proof.
intros mo. exists []. split; [constructor|]. split; [intros p []|]. cbn [app]. symmetry. apply wvb_id.
Qed.

Lemma pagedown_le : forall x, pagedown x <= x /\ x < pagedown x + 4096 /\ pagedown x mod 4096 = 0.
Proof.
intros x. unfold pagedown. pose proof (Z.div_mod x 4096 ltac:(lia)). pose proof (Z.mod_pos_bound x 4096 ltac:(lia)).
split; [lia|]. split; [lia|]. apply Z_mod_mult.
Qed.

Lemma pageup_ge : forall x, x <= pageup x /\ pageup x < x + 4096 /\ pageup x mod 4096 = 0.
Proof.
intros x. unfold pageup. pose proof (Z.div_mod (x + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)).
split; [lia|]. split; [lia|]. apply Z_mod_mult.
Qed.

Lemma mod0_multiple : forall a, a mod 4096 = 0 -> exists q, a = 4096 * q.
Proof. intros a H. exists (a / 4096). pose proof (Z.div_mod a 4096 ltac:(lia)). lia. Qed.

Lemma pageup_least : forall x y, x <= y -> y mod 4096 = 0 -> pageup x <= y.
Proof.
intros x y Hxy Hy. destruct (mod0_multiple y Hy) as [q ->].
pose proof (pageup_ge x) as (A & B & C). destruct (mod0_multiple _ C) as [q' E]. rewrite E in *. nia.
Qed.

Lemma pagedown_greatest : forall x y, y <= x -> y mod 4096 = 0 -> y <= pagedown x.
Proof.
intros x y Hxy Hy. destruct (mod0_multiple y Hy) as [q ->].
pose proof (pagedown_le x) as (A & B & C). destruct (mod0_multiple _ C) as [q' E]. rewrite E in *. nia.
Qed.

Lemma pageup_of_aligned : forall x, x mod 4096 = 0 -> pageup x = x.
Proof. intros x H. pose proof (pageup_ge x) as (A & _). pose proof (pageup_least x x ltac:(lia) H). lia. Qed.

Lemma pagedown_of_aligned : forall x, x mod 4096 = 0 -> pagedown x = x.
Proof. intros x H. pose proof (pagedown_le x) as (A & _). pose proof (pagedown_greatest x x ltac:(lia) H). lia. Qed.

Lemma zpages_In : forall n lo p,
In p (zpages lo n) <-> exists i, (i < n)%nat /\ p = Z_to_bv 64 (lo + 4096 * Z.of_nat i).
Proof.
induction n as [|n IH]; intros lo p; cbn [zpages].
- split; [intros []| intros (i & Hi & _); lia].
- split.
+ intros [<-|H].
* exists 0%nat. split; [lia|]. f_equal. lia.
* apply IH in H as (i & Hi & ->). exists (S i). split; [lia|]. f_equal. lia.
+ intros (i & Hi & ->). destruct i as [|i].
* left. f_equal. lia.
* right. apply IH. exists i. split; [lia|]. f_equal. lia.
Qed.

Lemma pages_in_In : forall (p : word) lo hi,
aligned p = true -> lo <= bv_unsigned p -> bv_unsigned p + 4096 <= hi -> In p (pages_in (lo, hi)).
Proof.
intros p lo hi Hal Hlo Hhi. unfold aligned in Hal. apply Z.eqb_eq in Hal.
unfold pages_in. cbn [fst snd].
pose proof (pageup_least lo (bv_unsigned p) Hlo Hal) as H1.
assert (H2 : bv_unsigned p + 4096 <= pagedown hi).
{ apply pagedown_greatest; [exact Hhi|]. rewrite Z.add_mod, Hal by lia. reflexivity. }
pose proof (pageup_ge lo) as (_ & _ & Hupm). pose proof (pagedown_le hi) as (_ & _ & Hdnm).
destruct (mod0_multiple _ Hupm) as [qu Equ]. destruct (mod0_multiple _ Hdnm) as [qd Eqd].
destruct (mod0_multiple _ Hal) as [qp Eqp].
apply zpages_In. exists (Z.to_nat (qp - qu)). split.
- rewrite Equ, Eqd. replace ((4096 * qd - 4096 * qu) / 4096) with (qd - qu).
2:{ symmetry. replace (4096 * qd - 4096 * qu) with ((qd - qu) * 4096) by lia. apply Z.div_mul. lia. }
apply Z2Nat.inj_lt; lia.
- rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range 64 p) as Hr. change (bv_modulus 64) with (2^64) in Hr.
rewrite bv_wrap_small; [lia|]. change (bv_modulus 64) with (2^64). lia.
Qed.

Lemma pages_meeting_In : forall (p : word) lo hi,
aligned p = true -> lo < bv_unsigned p + 4096 -> bv_unsigned p < hi -> In p (pages_meeting (lo, hi)).
Proof.
intros p lo hi Hal Hlo Hhi. unfold pages_meeting. cbn [fst snd]. apply pages_in_In; [exact Hal| |].
- unfold aligned in Hal. apply Z.eqb_eq in Hal.
pose proof (pagedown_le lo) as (A & B & C). destruct (mod0_multiple _ C) as [q Eq]. destruct (mod0_multiple _ Hal) as [qp Eqp]. nia.
- unfold aligned in Hal. apply Z.eqb_eq in Hal.
pose proof (pageup_ge hi) as (A & B & C). destruct (mod0_multiple _ C) as [q Eq]. destruct (mod0_multiple _ Hal) as [qp Eqp]. nia.
Qed.

Lemma length_zpages : forall n lo, length (zpages lo n) = n.
Proof. induction n; intros lo; cbn; [reflexivity| now rewrite IHn]. Qed.

Lemma G_cand : forall mo p, G mo p = true -> In p (cand mo).
Proof.
intros mo p HG. unfold G in HG. apply andb_prop in HG as [Hal Hor]. unfold cand. apply in_or_app.
apply orb_prop in Hor as [Hm|Hm]; [left|right]; apply existsb_exists in Hm as (iv & Hin & Hpm);
unfold page_meets in Hpm; apply andb_prop in Hpm as [Hpm H3]; apply andb_prop in Hpm as [H1 H2];
apply Z.ltb_lt in H1; apply Z.ltb_lt in H2; apply Z.ltb_lt in H3; apply in_flat_map; exists iv.
- split; [apply filter_In; split; [exact Hin| unfold nonempty; apply Z.ltb_lt; exact H1]|].
destruct iv as [lo hi]. apply pages_meeting_In; assumption.
- split; [exact Hin|]. destruct iv as [lo hi]. apply pages_meeting_In; assumption.
Qed.

Lemma allowed_In : forall mo p, In p (allowed mo) <-> G mo p = true.
Proof.
intros mo p. unfold allowed. rewrite nodup_In, filter_In. split; [tauto|]. intros H. split; [apply G_cand; exact H| exact H].
Qed.

Lemma allowed_NoDup : forall mo, List.NoDup (allowed mo).
Proof. intros mo. unfold allowed. apply NoDup_nodup. Qed.

Lemma unmat_NoDup : forall mo, List.NoDup (unmat mo).
Proof. intros mo. unfold unmat. apply NoDup_filter. apply allowed_NoDup. Qed.

Lemma page_mem_In : forall p l, page_mem p l = true <-> In p l.
Proof.
intros p l. unfold page_mem. rewrite existsb_exists. split.
- intros (q & Hin & E). unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq in E. subst. exact Hin.
- intros H. exists p. split; [exact H|]. unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma page_mem_false : forall p l, page_mem p l = false <-> ~ In p l.
Proof.
intros p l. rewrite <- page_mem_In. destruct (page_mem p l); split; intros; try congruence; auto.
Qed.

Lemma unmat_In : forall mo p, In p (unmat mo) <-> G mo p = true /\ ~ In p (m_vm_materialized mo).
Proof.
intros mo p. unfold unmat. rewrite filter_In, allowed_In, <- page_mem_false.
destruct (page_mem p _); cbn; split; intros [A B]; split; auto; congruence.
Qed.

Lemma zin_page_meets : forall (a : word) iv,
zin (bv_unsigned a) iv = true -> page_meets (page_base a) iv = true.
Proof.
intros a iv Hz. unfold zin in Hz. apply andb_prop in Hz as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (page_base_range a) as [P1 P2]. unfold page_meets.
apply andb_true_intro; split; [apply andb_true_intro; split|]; apply Z.ltb_lt; lia.
Qed.

Lemma visible_G : forall mo a, hidden mo a = false -> G mo (page_base a) = true.
Proof.
intros mo a Hh. unfold hidden in Hh. apply negb_false_iff in Hh. unfold allowed_byte in Hh. unfold G.
rewrite page_base_aligned. cbn [andb].
apply orb_prop in Hh as [H|H]; unfold in_zivs in H; apply existsb_exists in H as (iv & Hin & Hz);
apply orb_true_iff; [left|right]; apply existsb_exists; exists iv; split; [exact Hin| apply zin_page_meets; exact Hz| exact Hin| apply zin_page_meets; exact Hz].
Qed.

Lemma length_filter_remove1 : forall (A : list word) (q : word) (f : word -> bool),
List.NoDup A -> In q A -> f q = true ->
length (List.filter f A) = S (length (List.filter (fun x => negb (bv_eqb x q) && f x) A)).
Proof.
induction A as [|a A IH]; intros q f Hnd Hin Hf; [destruct Hin|].
inversion Hnd as [|a' A' Hnin Hnd']; subst. cbn [List.filter].
destruct Hin as [->|Hin].
- rewrite Hf. unfold bv_eqb at 1. rewrite Z.eqb_refl. cbn [negb andb length]. f_equal. f_equal.
apply filter_ext_in. intros x Hx. unfold bv_eqb.
destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned q)) as [E|E]; [|reflexivity].
exfalso. apply bv_eq in E. subst. exact (Hnin Hx).
- assert (Hne : bv_eqb a q = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros E. apply bv_eq in E. subst. exact (Hnin Hin). }
rewrite Hne. cbn [negb andb]. destruct (f a); cbn [length]; rewrite (IH q f Hnd' Hin Hf); reflexivity.
Qed.

Lemma length_filter_remove : forall (P A : list word) (f : word -> bool),
List.NoDup A -> List.NoDup P -> (forall p, In p P -> In p A /\ f p = true) ->
(length (List.filter (fun x => negb (page_mem x P) && f x) A) + length P)%nat = length (List.filter f A).
Proof.
induction P as [|q P IH]; intros A f HA HP Hsub.
- cbn. rewrite Nat.add_0_r. f_equal.
- inversion HP as [|q' P' Hq HP']; subst.
destruct (Hsub q (or_introl eq_refl)) as [HqA Hfq].
rewrite (length_filter_remove1 A q f HA HqA Hfq).
rewrite <- (IH A (fun x => negb (bv_eqb x q) && f x) HA HP').
2:{ intros p Hp. destruct (Hsub p (or_intror Hp)) as [HpA Hfp]. split; [exact HpA|]. rewrite Hfp.
unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned p) (bv_unsigned q)) as [E|E]; [|reflexivity].
exfalso. apply bv_eq in E. subst. exact (Hq Hp). }
cbn [length]. rewrite Nat.add_succ_r. f_equal.
replace (List.filter (fun x : word => negb (page_mem x (q :: P)) && f x) A)
with (List.filter (fun x : word => negb (page_mem x P) && (negb (bv_eqb x q) && f x)) A); [reflexivity|].
apply filter_ext. intros x. unfold page_mem. cbn [existsb].
destruct (bv_eqb x q); destruct (existsb (bv_eqb x) P); destruct (f x); reflexivity.
Qed.

Lemma drift_vmeq : forall mo mo', drift mo mo' -> vmeq mo mo'.
Proof. intros mo mo' H. apply msim_frame. apply drift_msim. exact H. Qed.

Lemma drift_frame : forall mo mo', drift mo mo' ->
m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo /\ m_halted mo' = m_halted mo /\ m_tid mo' = m_tid mo /\
m_stdin mo' = m_stdin mo /\ m_vmmaps mo' = m_vmmaps mo /\ m_vm_lazy mo' = m_vm_lazy mo /\
(forall p, G mo' p = G mo p) /\ (forall a, hidden mo' a = hidden mo a) /\
allowed mo' = allowed mo /\ cand mo' = cand mo /\ (forall ms, msview mo' ms = msview mo ms).
Proof. intros mo mo' H. apply msim_facts. apply drift_msim. exact H. Qed.

Lemma drift_trans : forall a b c, drift a b -> drift b c -> drift a c.
Proof.
intros a b c Hab Hbc.
pose proof (drift_frame _ _ Hab) as (_ & _ & _ & _ & _ & Hvm & Hlz & HG & _).
destruct Hab as (P1 & Hnd1 & HP1 & Eb). destruct Hbc as (P2 & Hnd2 & HP2 & Ec).
assert (Hmatb : m_vm_materialized b = P1 ++ m_vm_materialized a) by (rewrite Eb; apply wvb_frame).
exists (P2 ++ P1). split; [|split].
- apply NoDup_app; [exact Hnd2| exact Hnd1|]. intros p Hp2 Hp1.
destruct (HP2 p Hp2) as [_ Hm]. rewrite Hmatb in Hm. apply page_mem_false in Hm. apply Hm. apply in_or_app. left. exact Hp1.
- intros p Hp. apply in_app_or in Hp as [Hp|Hp].
+ destruct (HP2 p Hp) as [HGp Hm]. rewrite HG in HGp. split; [exact HGp|].
rewrite Hmatb in Hm. apply page_mem_false in Hm. apply page_mem_false. intros Hin. apply Hm. apply in_or_app. right. exact Hin.
+ apply HP1. exact Hp.
- rewrite Ec, Hlz, Hmatb, Eb, wvb_wvb, app_assoc. reflexivity.
Qed.

Lemma vm_backing_used_wvb : forall mo X,
vm_backing_used (with_vm_backing (m_vm_lazy mo) X mo) =
vm_backing_used mo + (Z.of_nat (length X) - Z.of_nat (length (m_vm_materialized mo))) * page_size.
Proof.
intros mo X. unfold vm_backing_used.
destruct (wvb_frame (m_vm_lazy mo) X mo) as (_ & -> & -> & -> & _). lia.
Qed.

Lemma drift_Phi : forall mo mo', drift mo mo' -> Phi mo' = Phi mo.
Proof.
intros mo mo' Hd. pose proof (drift_frame _ _ Hd) as (_ & _ & _ & _ & _ & Hvm & Hlz & HG & _ & Hal & _).
destruct Hd as (P & Hnd & HP & E).
unfold Phi, Rsv, unmat. rewrite Hal.
assert (Hmat : m_vm_materialized mo' = P ++ m_vm_materialized mo) by (rewrite E; apply wvb_frame).
rewrite Hmat. rewrite E at 1. rewrite vm_backing_used_wvb, length_app, Nat2Z.inj_add.
pose proof (length_filter_remove P (allowed mo) (fun p => negb (page_mem p (m_vm_materialized mo)))
(allowed_NoDup mo) Hnd) as Hlen.
assert (Hsub : forall p, In p P -> In p (allowed mo) /\ negb (page_mem p (m_vm_materialized mo)) = true).
{ intros p Hp. destruct (HP p Hp) as [HGp Hm]. split; [apply allowed_In; exact HGp| rewrite Hm; reflexivity]. }
specialize (Hlen Hsub).
replace (List.filter (fun p => negb (page_mem p (P ++ m_vm_materialized mo))) (allowed mo))
with (List.filter (fun x => negb (page_mem x P) && negb (page_mem x (m_vm_materialized mo))) (allowed mo)).
2:{ apply filter_ext. intros x. unfold page_mem. rewrite existsb_app. symmetry. apply negb_orb. }
unfold page_size. lia.
Qed.

Definition zero8 : byte := Z_to_bv 8 0.

Definition lv_ceiling : Z := sp_window_hi - stack_max_size.

Definition lv_inv (mo : Model) : Prop := Phi mo <= vm_limit (m_vmmaps mo).

Definition bands_excl : Prop :=
forall b, In b (lv_bands L) -> exists e, In e (lv_excl L) /\ fst e <= fst b /\ snd b <= snd e.
Definition bands_cover : Prop :=
forall y, 0 <= y < lv_ceiling -> in_zivs y (lv_excl L) = false -> in_zivs (shz y) (lv_bands L) = true.

Definition segs_in_base (segs : list Segment) : Prop :=
forall seg, In seg segs -> exists iv, In iv (lv_base L) /\
fst iv <= Z.of_N (seg_base seg) /\ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= snd iv.

Lemma lv_inv_drift : forall mo mo', lv_inv mo -> drift mo mo' -> lv_inv mo'.
Proof.
intros mo mo' HP Hd. pose proof (drift_frame _ _ Hd) as (_ & _ & _ & _ & _ & Hvm & _).
unfold lv_inv. rewrite (drift_Phi _ _ Hd), Hvm. exact HP.
Qed.

Lemma hidden_off_segments : forall segs mo, segs_in_base segs -> H_off_segments segs (hidden mo).
Proof.
intros segs mo Hs a Ha. unfold hidden, allowed_byte in Ha. apply negb_true_iff in Ha. apply orb_false_iff in Ha as [Ha _].
destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity]. exfalso.
apply find_segment_some_spec in E as (Hseg & S1 & S2).
destruct (Hs seg Hseg) as (iv & Hin & B1 & B2).
assert (Ht : in_zivs (bv_unsigned a) (appvis mo) = true).
{ unfold in_zivs, appvis. rewrite existsb_app. apply orb_true_iff. left. apply existsb_exists. exists iv. split; [exact Hin|].
unfold zin. apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
rewrite Ht in Ha. discriminate.
Qed.

Section Transport.
Variable segs : list Segment.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base segs.

Lemma step_view : forall mo ms msr',
RiscvSemantics.step segs (msview mo ms) = MachineOk msr' ->
exists rep,
RiscvSemantics.step_accesses segs ms = MachineOk rep /\
access_value _ rep = unrestrict (hidden mo) (ms_mem ms) msr' /\
ranges_avoid (hidden mo) (accessed_ranges _ rep) /\
hclean (hidden mo) msr' /\
msview mo (unrestrict (hidden mo) (ms_mem ms) msr') = msr'.
Proof.
intros mo ms msr' Hs. exact (step_restrict_sound segs (hidden mo) (hidden_off_segments segs mo Hsegs) Hwx ms msr' Hs).
Qed.

Lemma new_pages_G : forall mo ranges,
ranges_avoid (hidden mo) ranges ->
let new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) ranges in
List.NoDup new
/\ (forall p, In p new -> G mo p = true /\ page_mem p (m_vm_materialized mo) = false).
Proof.
intros mo ranges Hav new.
split.
- unfold new, newly_materialized_pages. apply NoDup_filter. apply accesses_pages_nodup. constructor.
- intros p Hin. unfold new, newly_materialized_pages in Hin.
apply filter_In in Hin as [Hin Hf]. apply andb_prop in Hf as [Hl Hm].
split; [| destruct (page_mem p _); [discriminate| reflexivity]].
destruct (accesses_pages_in ranges [] p Hin) as [[] | (a & n & k & Hr & Hk & Ep)].
pose proof (Hav a n Hr k Hk) as Hw. rewrite <- page_base_woff in Ep. rewrite Ep. apply visible_G. exact Hw.
Qed.

Lemma account_view : forall mo ranges,
lv_inv mo ->
ranges_avoid (hidden mo) ranges ->
exists mo', materialize_model_accesses mo ranges = Some mo' /\ drift mo mo'.
Proof.
intros mo ranges HP Hav.
destruct (new_pages_G mo ranges Hav) as [Hnd Hnew].
unfold materialize_model_accesses, materialize_accesses.
set (new := newly_materialized_pages (m_vm_lazy mo) (m_vm_materialized mo) ranges) in *.
destruct new as [|p0 new'] eqn:En.
- exists mo. rewrite wvb_id. split; [reflexivity| apply drift_refl].
- assert (Hlen : (length (p0 :: new') <= length (unmat mo))%nat).
{ apply NoDup_incl_length; [exact Hnd|]. intros p Hp. apply unmat_In.
destruct (Hnew p Hp) as [HG Hm]. split; [exact HG| apply page_mem_false; exact Hm]. }
replace (vm_backing_used mo + Z.of_nat (length (p0 :: new')) * page_size <=? vm_limit (m_vmmaps mo)) with true.
2:{ symmetry. apply Z.leb_le. unfold lv_inv, Phi, Rsv in HP. unfold page_size. lia. }
eexists. split; [reflexivity|]. exists (p0 :: new'). split; [exact Hnd|]. split; [exact Hnew| reflexivity].
Qed.

Lemma mstep_view : forall mo ms msr',
lv_inv mo -> m_halted mo = None ->
mstep segs (msview mo ms) msr' ->
exists ms' mo',
mi_account_step segs ms mo = MachineOk (ms', mo') /\
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) [] (SNext (mkCfg ms' mo')) /\
(forall evs X, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X -> evs = [] /\ X = SNext (mkCfg ms' mo')) /\
msview mo' ms' = msr' /\ drift mo mo' /\
(forall a, hidden mo a = true -> ms_mem ms' a = ms_mem ms a) /\
ms_svc_pending ms = None.
Proof.
intros mo ms msr' HI Hh [Hsvc Hs]. rewrite msview_svc in Hsvc.
destruct (step_view mo ms msr' Hs) as (rep & Hsa & Hv & Hav & Hcl & Hview).
destruct (account_view mo (accessed_ranges _ rep) HI Hav) as (mo' & Hmat & Hd).
set (ms' := unrestrict (hidden mo) (ms_mem ms) msr').
assert (Hacc : mi_account_step segs ms mo = MachineOk (ms', mo')).
{ unfold mi_account_step. rewrite Hsa, Hmat, Hv. reflexivity. }
exists ms', mo'. split; [exact Hacc|]. split; [|split; [|split; [|split; [exact Hd|split; [|exact Hsvc]]]]].
- apply sstep_cfg_instr; assumption.
- intros evs X Hss. exact (sstep_instr_det segs ms mo ms' mo' evs X Hsvc Hacc (sstep_cfg_sub segs _ _ _ _ Hss)).
- pose proof (drift_frame _ _ Hd) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hms). rewrite Hms. exact Hview.
- intros a Ha. unfold ms'. cbn [ms_mem unrestrict]. unfold munrestrict. rewrite Ha. reflexivity.
Qed.

Definition silent_closed (P : config -> Prop) : Prop :=
forall ms mo ms' mo', node_ok segs (mkCfg ms mo) unit (fun _ => []) (fun _ => mkCfg ms' mo') ->
drift mo mo' -> lv_inv mo -> m_halted mo = None ->
(forall a, hidden mo a = true -> ms_mem ms' a = ms_mem ms a) ->
P (mkCfg ms' mo') -> P (mkCfg ms mo).

Lemma msteps_view : forall (P : config -> Prop), silent_closed P ->
forall msr0 msr', msteps segs msr0 msr' ->
forall mo ms, msr0 = msview mo ms ->
lv_inv mo -> m_halted mo = None ->
(forall ms' mo', msview mo' ms' = msr' -> drift mo mo' -> lv_inv mo' -> m_halted mo' = None ->
(forall a, hidden mo a = true -> ms_mem ms' a = ms_mem ms a) ->
P (mkCfg ms' mo')) ->
P (mkCfg ms mo).
Proof.
intros P HP msr0 msr' Hms. induction Hms as [msr | msr msr1 msr2 H1 H2 IH]; intros mo ms -> HI Hh Hk.
- apply (Hk ms mo eq_refl (drift_refl mo) HI Hh). intros; reflexivity.
- destruct (mstep_view mo ms msr1 HI Hh H1) as (ms1 & mo1 & Hacc & Hss & Hdet & Hv1 & Hd1 & Hhid1 & Hsvc).
apply (HP ms mo ms1 mo1); [| exact Hd1 | exact HI | exact Hh | exact Hhid1 |].
+ split; [intros []; exact Hss|]. intros e st Hst. exists tt. exact (Hdet e st Hst).
+ pose proof (drift_frame _ _ Hd1) as (_ & _ & Hh1 & _ & _ & _ & _ & _ & Hhid & _).
apply (IH mo1 ms1 (eq_sym Hv1) (lv_inv_drift _ _ HI Hd1) ltac:(rewrite Hh1; exact Hh)).
intros ms' mo' Hv' Hd' HI' Hh' Hk'. apply (Hk ms' mo' Hv' (drift_trans _ _ _ Hd1 Hd') HI' Hh').
intros a Ha. rewrite (Hk' a) by (rewrite Hhid; exact Ha). apply Hhid1. exact Ha.
Qed.

End Transport.

Lemma length_nodup_le : forall (l : list word), (length (nodup weq_dec l) <= length l)%nat.
Proof.
intros l. apply NoDup_incl_length; [apply NoDup_nodup|]. intros x Hx. apply nodup_In in Hx. exact Hx.
Qed.

Lemma length_filter_le : forall {A} (f : A -> bool) (l : list A), (length (List.filter f l) <= length l)%nat.
Proof. intros A f l. induction l as [|x l IH]; cbn; [lia|]. destruct (f x); cbn; lia. Qed.

Lemma Rsv_le_cand : forall mo, Rsv mo <= cand_bytes mo.
Proof.
intros mo. unfold Rsv, cand_bytes, unmat, allowed.
pose proof (length_filter_le (fun p => negb (page_mem p (m_vm_materialized mo))) (nodup weq_dec (List.filter (G mo) (cand mo)))).
pose proof (length_nodup_le (List.filter (G mo) (cand mo))).
pose proof (length_filter_le (G mo) (cand mo)). lia.
Qed.

Lemma Phi_le_cand : forall mo, Phi mo <= vm_backing_used mo + cand_bytes mo.
Proof. intros mo. unfold Phi. pose proof (Rsv_le_cand mo). lia. Qed.

Lemma Rsv_nonneg : forall mo, 0 <= Rsv mo.
Proof. intros mo. unfold Rsv. lia. Qed.

Lemma length_pages_in : forall lo hi,
Z.of_nat (length (pages_in (lo, hi))) = Z.max 0 ((pagedown hi - pageup lo) / 4096).
Proof.
intros lo hi. unfold pages_in. cbn [fst snd]. rewrite length_zpages.
destruct (Z.le_gt_cases 0 ((pagedown hi - pageup lo) / 4096)).
- rewrite Z2Nat.id by lia. lia.
- rewrite Z2Nat.nonpos by lia. lia.
Qed.

Section ViewMem.
Variable segs : list Segment.
Hypothesis Hsegs : segs_in_base segs.

Lemma mrd_view : forall mo m a b,
mrd segs (view mo m) a = Some b -> mrd segs m a = Some b /\ hidden mo a = false.
Proof.
intros mo m a b H. unfold mrd, view, mrestrict in *.
destruct (hidden mo a) eqn:Hh.
- exfalso. unfold seg_rom in H. pose proof (hidden_off_segments segs mo Hsegs a Hh) as Hoff.
unfold memory_read in H. cbn [Z.of_N] in H. rewrite Hoff in H. discriminate.
- auto.
Qed.

Lemma bytes_at_view : forall mo m a bs,
bytes_at segs (view mo m) a bs ->
bytes_at segs m a bs /\ (forall i, (i < length bs)%nat -> hidden mo (wa (a + Z.of_nat i)) = false).
Proof.
intros mo m a bs (Ha & Hl & H). split.
- split; [exact Ha|]. split; [exact Hl|]. intros i Hi.
destruct (nth_error bs i) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
specialize (H i Hi). rewrite E in H. apply (mrd_view mo m _ b) in H as [H _]. exact H.
- intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
specialize (H i Hi). rewrite E in H. apply (mrd_view mo m _ b) in H as [_ H]. exact H.
Qed.

Lemma wview_view : forall mo m a,
wview segs (view mo m) a <> None -> wview segs m a <> None /\ hidden mo a = false.
Proof.
intros mo m a H. unfold view in H.
rewrite (wview_restrict segs (hidden mo) (hidden_off_segments segs mo Hsegs)) in H.
destruct (hidden mo a); [exfalso; apply H; reflexivity|]. auto.
Qed.

Lemma wr_at_view : forall mo m a n,
wr_at segs (view mo m) a n ->
wr_at segs m a n /\ (forall i, 0 <= i < n -> hidden mo (wa (a + i)) = false).
Proof.
intros mo m a n (Ha & Hn & H). split.
- split; [exact Ha|]. split; [exact Hn|]. intros i Hi. apply (wview_view mo m _). apply H. exact Hi.
- intros i Hi. apply (wview_view mo m _). apply H. exact Hi.
Qed.

End ViewMem.

Lemma range_avoids_of_bytes : forall mo a (n : nat),
0 <= a -> (forall i, 0 <= i < Z.of_nat n -> hidden mo (wa (a + i)) = false) ->
range_avoids (hidden mo) (wa a) n.
Proof.
intros mo a n Ha H k Hk. unfold woff.
replace (Z_to_bv 64 (bv_unsigned (wa a) + Z.of_nat k)) with (wa (a + Z.of_nat k)).
+ apply H. lia.
+ unfold wa. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma msim_with_vmmaps : forall h mo mo', msim mo mo' -> msim (with_vmmaps h mo) (with_vmmaps h mo').
Proof. intros h mo mo' ->. destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma msim_with_fds : forall f mo mo', msim mo mo' -> msim (with_fds f mo) (with_fds f mo').
Proof. intros f mo mo' ->. destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma msim_with_halted : forall c mo mo', msim mo mo' -> msim (with_halted c mo) (with_halted c mo').
Proof. intros c mo mo' ->. destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma msim_wvb : forall l X X' mo mo', msim mo mo' -> msim (with_vm_backing l X mo) (with_vm_backing l X' mo').
Proof. intros l X X' mo mo' ->. destruct mo as [fd [maps lazy mat] io fs proc lim tm]; reflexivity. Qed.

Lemma msim_vm_forget_range : forall lo hi mo mo', msim mo mo' -> msim (vm_forget_range lo hi mo) (vm_forget_range lo hi mo').
Proof.
intros lo hi mo mo' H. unfold vm_forget_range.
pose proof (msim_facts _ _ H) as (_ & _ & _ & _ & _ & _ & -> & _). apply msim_wvb. exact H.
Qed.

Lemma msim_vm_add_lazy : forall a n mo mo', msim mo mo' -> msim (vm_add_lazy a n mo) (vm_add_lazy a n mo').
Proof.
intros a n mo mo' H. unfold vm_add_lazy.
pose proof (msim_facts _ _ H) as (_ & _ & _ & _ & _ & _ & -> & _). apply msim_wvb. exact H.
Qed.

Lemma materialize_nil : forall mo, materialize_model_accesses mo [] = Some mo.
Proof. exact materialize_model_accesses_nil. Qed.

End LV.
