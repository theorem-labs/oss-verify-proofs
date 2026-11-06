(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qqcs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qqcs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition is_spinA (n : node) : bool := match n with NSetTid => true | _ => false end.

Definition PROT_RW : Z := 3.
Definition FL_ANON : Z := 34.
Definition FL_FIXED : Z := 50.
Definition FL_FIXED_NR : Z := 16434.

Inductive mkind := KAnon | KFixed | KRemap | KNone.

Definition mmap_kind (addr prot flags : Z) : mkind :=
if negb (prot =? PROT_RW) then KNone
else if (flags =? FL_ANON) && (addr =? 0) then KAnon
else if flags =? FL_FIXED then KFixed
else if flags =? FL_FIXED_NR then KRemap
else KNone.

Definition grant_ceilA : Z := sp_window_hi - stack_max_size.

Definition rlen (len : Z) : Z := page_round_up_Z len.
Definition rlenw (len : Z) : word := Z_to_bv 64 (rlen len).

Definition anon_place_ok (mo : Model) (a : word) (n : Z) : bool :=
(bv_unsigned a mod page_size =? 0) && (0 <? bv_unsigned a) && (bv_unsigned a + n <=? alloc_top (m_vmmaps mo))
&& region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 n).

Definition fixed_contained (mo : Model) (a n : word) : bool :=
region_free (vm_reserved (m_vmmaps mo)) a n && map_contains (vm_maps (m_vmmaps mo)) a n.
Definition fixed_free (mo : Model) (a n : word) : bool :=
region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n.

Section WithL.
Variable L : lvp.

Definition shadow_iv (a n : word) : Z * Z := sh_iv L (wiv2z (a, n)).

Definition reveal (mo : Model) (a n : word) : list word :=
List.filter (hidden L mo) (bytes_of (shadow_iv a n)).
Definition wunit (ws : list (word * list byte)) : bool :=
forallb (fun w => (length (snd w) =? 1)%nat) ws.

Definition conceal (mo' : Model) (a n : word) : list (word * word) :=
map (fun x => (x, Z_to_bv 64 1)) (List.filter (hidden L mo') (bytes_of (shadow_iv a n))).

Definition sh_some (a n : word) (m : word -> option byte) : Prop :=
forall x, In x (bytes_of (shadow_iv a n)) -> m x <> None.

Definition rsp_err : resp := efferr ENOMEM.
Definition rsp_grant (a n : word) (ws : list (word * list byte)) : resp := mkEffectU a ws [(a, n)] [] [] [].
Definition rsp_remap (a n : word) : resp := mkEffectU a [] [(a, n)] [] [] [].
Definition rsp_munmap (mo' : Model) (a n : word) : resp := mkEffectU (Z_to_bv 64 0) [] [] ((a, n) :: conceal mo' a n) [] [].

Definition rvarA (n : node) (r r' : resp) : Prop :=
r = r' \/
match n with
| NMmap _ _ _ _ =>
eff_ret r' = eff_ret r /\ eff_zeros r' = eff_zeros r /\ eff_unmaps r' = eff_unmaps r /\
eff_copies r' = eff_copies r /\ eff_copyins r' = eff_copyins r /\
map fst (eff_writes r') = map fst (eff_writes r) /\ wunit (eff_writes r) = true /\ wunit (eff_writes r') = true
| _ => False
end.

Lemma rvarA_refl : forall n r, rvarA n r r.
Proof. intros; left; reflexivity. Qed.

Definition at_nodeA (segs : list Segment) (n : node) (ms : machine_state) : Prop :=
match n with
| NSetTid => ms_svc_pending ms = None /\
RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms [])
| NBrk _ | NMprotect _ _ _ => False
| NMunmap addr len => at_node segs n ms /\ sh_some (Z_to_bv 64 addr) (rlenw len) (ms_mem ms)
| _ => at_node segs n ms
end.

Definition nstep_raw (n : node) (mo : Model) (rsp : resp) (mo' : Model) (evs : list event) : Prop :=
match n with
| NWritev _ _ | NOpen _ | NRead _ _ _ | NClose _ | NIoctl _ _ =>
exists mo2, nstep n mo rsp mo2 evs /\ drift L mo2 mo'
| NExit _ | NSetTid | NBrk _ | NMprotect _ _ _ => False
| NMmap addr len prot flags =>
let n := rlenw len in
evs = [] /\
match mmap_kind addr prot flags with

| KAnon =>
exists a ws, anon_place_ok mo a (rlen len) = true /\ map fst ws = reveal mo a n /\ wunit ws = true /\
mo' = grant_model mo a n /\ rsp = rsp_grant a n ws
| KFixed =>
let a := Z_to_bv 64 addr in
if fixed_contained mo a n then
mo' = commit_model mo a n /\ rsp = rsp_grant a n []
else if fixed_free mo a n then
exists ws, map fst ws = reveal mo a n /\ wunit ws = true /\ mo' = grant_model mo a n /\ rsp = rsp_grant a n ws
else False
| KRemap =>
let a := Z_to_bv 64 addr in
mo' = remap_model mo a n /\ rsp = rsp_remap a n
| KNone => False
end
| NMunmap addr len =>
let a := Z_to_bv 64 addr in let n := rlenw len in
evs = [] /\ mo' = munmap_model mo a n /\ rsp = rsp_munmap mo' a n
end.

Definition nexit_raw (n : node) (mo : Model) (code : word) (mo' : Model) : Prop :=
match n with
| NExit _ => nexit n mo code mo'
| _ => False
end.

Definition fdinv (mo : Model) : Prop :=
fd_lookup (m_fds mo) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) /\
(forall k c, fd_lookup (m_fds mo) k = Some (FdChannel c) -> bv_unsigned k < 3) /\
(forall k p off, fd_lookup (m_fds mo) k = Some (FdFile p off) -> fs_lookup (m_fs mo) p <> None) /\
(forall k e, fd_lookup (m_fds mo) k = Some e ->
match e with FdChannel _ | FdFile _ _ | FdDir => True | _ => False end).

Definition maps_below_top (h : VmMaps) : Prop :=
alloc_top h <= grant_ceilA /\
forall e, In e (vm_maps h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top h.
Definition vminvA (mo : Model) : Prop := model_ivs_wf mo /\ excl_inside L mo /\ maps_below_top (m_vmmaps mo).

Definition xinvA (mo : Model) : Prop := fdinv mo /\ vminvA mo.

Definition sh_cost (n : Z) : Z := 4096 * (n / 32768 + 2).
Definition sh_cost_at (a n : Z) : Z := 4096 * Z.of_nat (length (pages_meeting (sh_iv L (a, a + n)))).

Definition cost_anon (len : Z) : Z := 2 * rlen len + sh_cost (rlen len).
Definition cost_fixed (addr len : Z) : Z := 2 * rlen len + sh_cost_at addr (rlen len).

Definition cost_commit (mo : Model) (addr len : Z) : Z :=
overlap_sum (vm_maps (m_vmmaps mo)) addr (addr + rlen len).

Definition fixed_gates (addr len : Z) : Prop :=
0 < len /\ len <= 2^40 /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + rlen len <= grant_ceilA.
Definition fixed_top (mo : Model) (addr len : Z) : Prop := addr + rlen len <= alloc_top (m_vmmaps mo).

Definition range_vis (mo : Model) (a n : word) : Prop :=
forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> hidden L mo x = false.

Definition nsafeA (n : node) (mo : Model) : Prop :=
let h := m_vmmaps mo in
match n with
| NMmap addr len prot flags =>
let a := Z_to_bv 64 addr in let nw := rlenw len in
match mmap_kind addr prot flags with
| KAnon => 0 < len /\ len <= 2^40 /\ excl_mapped L mo /\ Phi L mo + cost_anon len <= vm_limit h
/\ vm_gap_available h (rlen len) = true
| KFixed =>
fixed_gates addr len /\ fixed_top mo addr len /\
((fixed_contained mo a nw = true /\ range_vis mo a nw /\ Phi L mo + cost_commit mo addr len <= vm_limit h)
\/ (fixed_contained mo a nw = false /\ fixed_free mo a nw = true /\ excl_entry L (a, nw) = false /\
Phi L mo + cost_fixed addr len <= vm_limit h))
| KRemap =>
fixed_gates addr len /\ fixed_top mo addr len /\ fixed_contained mo a nw = true /\ range_vis mo a nw
| KNone => False
end
| NMunmap addr len =>
let a := Z_to_bv 64 addr in let nw := rlenw len in
0 < len /\ len <= 2^40 /\ addr mod 4096 = 0 /\ 0 <= addr /\ addr + rlen len <= TASK_SIZE /\
map_has (vm_maps h) a nw = true /\
(forall e, In e (vm_maps h) -> fst e = a -> snd e = nw) /\
region_free (map_remove (vm_maps h) a) a nw = true /\ excl_entry L (a, nw) = false
| NBrk _ | NMprotect _ _ _ => False
| _ => True
end.

Definition costA (n : node) (mo : Model) (rsp : resp) : Z :=
match n with
| NMmap addr len prot flags =>
if errno_ret_in mmap_errnos (eff_ret rsp) then 0 else
match mmap_kind addr prot flags with
| KAnon => cost_anon len
| KFixed => if fixed_contained mo (Z_to_bv 64 addr) (rlenw len) then cost_commit mo addr len else cost_fixed addr len
| _ => 0
end
| _ => 0
end.

End WithL.

Lemma apply_writes_restrict : forall H ws m,
ranges_avoid H (write_accesses ws) ->
apply_writes (mrestrict H m) ws = mrestrict H (apply_writes m ws).
Proof.
induction ws as [|[a bs] ws IH]; intros m Hav; [reflexivity|].
cbn [apply_writes write_accesses] in *.
rewrite (write_to_mem_restrict H bs m a) by (apply Hav; left; reflexivity).
apply IH. intros a' n' Hin. apply Hav. right. exact Hin.
Qed.

Lemma apply_writes_hidden : forall H ws m x,
ranges_avoid H (write_accesses ws) -> H x = true -> apply_writes m ws x = m x.
Proof.
induction ws as [|[a bs] ws IH]; intros m x Hav Hx; [reflexivity|].
cbn [apply_writes write_accesses] in *.
rewrite IH; [| intros a' n' Hin; apply Hav; right; exact Hin | exact Hx].
apply (write_to_mem_hidden H bs m a x); [apply Hav; left; reflexivity| exact Hx].
Qed.

Lemma nret_writes_mem : forall ms r ws ci,
ms_mem (nret ms (mkEffectU r ws [] [] [] ci)) = apply_writes (ms_mem ms) ws.
Proof. intros. reflexivity. Qed.

Lemma msview_nret_writes : forall L mo mo' ms r ws ci,
vmeq mo mo' ->
ranges_avoid (hidden L mo) (write_accesses ws) ->
msview L mo' (nret ms (mkEffectU r ws [] [] [] ci)) = nret (msview L mo ms) (mkEffectU r ws [] [] [] []).
Proof.
intros L mo mo' ms r ws ci Hv Hav. rewrite (msview_ext L mo mo' Hv).
unfold msview, restrict, nret, advance_past_svc, apply_effect. cbn. f_equal.
symmetry. apply apply_writes_restrict. exact Hav.
Qed.

Lemma ranges_avoid_app_inv : forall H l1 l2, ranges_avoid H (l1 ++ l2) -> ranges_avoid H l1 /\ ranges_avoid H l2.
Proof.
intros H l1 l2 Hr. split; intros a n Hin; apply Hr; apply in_or_app; [left|right]; exact Hin.
Qed.

Section Kit.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

#[local] Notation CINV := (cinv L (xinvA L) (jsome L)) (only parsing).

Lemma fdinv_frame : forall mo mo',
m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> fdinv mo -> fdinv mo'.
Proof.
intros mo mo' Hf Hs (M0 & M1 & M2 & MC & MF & MK). unfold fdinv. rewrite Hf, Hs.
split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [exact MC|]. split; [exact MF| exact MK].
Qed.

Lemma fdinv_drift : forall mo mo', drift L mo mo' -> fdinv mo -> fdinv mo'.
Proof.
intros mo mo' Hd. pose proof (drift_frame L _ _ Hd) as (Hf & Hs & _). apply fdinv_frame; assumption.
Qed.

Lemma vminvA_vmeq : forall mo mo', vmeq mo mo' -> vminvA L mo -> vminvA L mo'.
Proof.
intros mo mo' [Hv Hl] ((W1 & W2 & W3 & W4) & X & Y). unfold vminvA, excl_inside, model_ivs_wf, maps_below_top in *. rewrite Hv, Hl.
split; [repeat split; assumption| split; [exact X| exact Y]].
Qed.

Lemma xinvA_drift : forall mo mo', drift L mo mo' -> xinvA L mo -> xinvA L mo'.
Proof.
intros mo mo' Hd [HF HV]. split; [eapply fdinv_drift; eassumption| eapply vminvA_vmeq; [eapply drift_vmeq; exact Hd| exact HV]].
Qed.

Lemma file_kit : forall ms mo x8 (P : resp -> Model -> list event -> Prop) (chk : resp -> check_result),
ms_svc_pending ms = Some x8 -> m_halted mo = None -> CINV ms mo ->
(forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
(forall eff, chk eff <> CheckUnmodeled) ->
(forall eff mo2 evs, chk eff = CheckOk mo2 evs ->
P (canon eff) mo2 evs /\ m_halted mo2 = m_halted mo /\ m_vm mo2 = m_vm mo /\ fdinv mo2 /\
eff_zeros eff = [] /\ eff_unmaps eff = [] /\ eff_copies eff = [] /\
ranges_avoid (hidden L mo) (syscall_effect_accesses eff)) ->
(forall rsp mo2 evs, P rsp mo2 evs -> exists eff, canon eff = rsp /\ chk eff = CheckOk mo2 evs) ->
(forall evs X, sstep segs (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
(exists mo2, P rsp mo2 evs /\ drift L mo2 mo') /\ CINV ms' mo' /\ m_halted mo' = None)
/\ (forall rsp mo2 mo' evs, P rsp mo2 evs -> drift L mo2 mo' ->
exists ms' mo3, sstep segs (mkCfg ms mo) evs (SNext (mkCfg ms' mo3)) /\
msview L mo3 ms' = nret (msview L mo ms) rsp /\
(exists mo2', P rsp mo2' evs /\ drift L mo2' mo3) /\ msim mo' mo3 /\ m_halted mo3 = None)
/\ (exists rsp mo2 evs, P rsp mo2 evs).
Proof.
intros ms mo x8 P chk Hsvc Hh ([HXF HXV] & HI & HJ) Hchk Hnu Hok Hcompl.

assert (STEP : forall eff mo2 evs, chk eff = CheckOk mo2 evs ->
exists mo3, materialize_model_accesses mo2 (syscall_effect_accesses eff) = Some mo3 /\ drift L mo2 mo3 /\
P (canon eff) mo2 evs /\ m_halted mo3 = None /\ CINV (nret ms eff) mo3 /\
msview L mo3 (nret ms eff) = nret (msview L mo ms) (canon eff)).
{ intros eff mo2 evs Hc. destruct (Hok _ _ _ Hc) as (HP & Hh2 & Hvm & HX2 & Hz & Hu & Hcp & Hav).
assert (Hv : vmeq mo mo2) by (unfold vmeq, m_vmmaps, m_vm_lazy; rewrite Hvm; split; reflexivity).
assert (Hmat : m_vm_materialized mo2 = m_vm_materialized mo) by (unfold m_vm_materialized; rewrite Hvm; reflexivity).
assert (HI2 : lv_inv L mo2).
{ unfold lv_inv in *. rewrite (Phi_ext L mo mo2 Hv Hmat). destruct Hv as [-> _]. exact HI. }
assert (Hav2 : ranges_avoid (hidden L mo2) (syscall_effect_accesses eff)).
{ intros a n Hin k Hk. rewrite (hidden_ext L mo mo2 Hv). exact (Hav a n Hin k Hk). }
destruct (account_view L mo2 _ HI2 Hav2) as (mo3 & Hm & Hd).
exists mo3. split; [exact Hm|]. split; [exact Hd|]. split; [exact HP|].
pose proof (drift_frame L _ _ Hd) as (_ & _ & Hh3 & _).
split; [rewrite Hh3, Hh2; exact Hh|].
destruct eff as [r ws zs us cs ci]. cbn in Hz, Hu, Hcp. subst zs us cs.
unfold syscall_effect_accesses in Hav. cbn [eff_copyins eff_writes] in Hav. apply ranges_avoid_app_inv in Hav as [_ Havw].
assert (Hv3 : vmeq mo mo3).
{ destruct Hv as [Hv1 Hv2]. pose proof (drift_vmeq L _ _ Hd) as [Hd1 Hd2]. split; congruence. }
split.
{ split; [| split; [eapply lv_inv_drift; eassumption|]].
- eapply xinvA_drift; [eassumption|]. split; [exact HX2|]. eapply vminvA_vmeq; eassumption.
- eapply (jsome_stable L mo mo3); [exact Hv3| | exact HJ]. intros a Ha. rewrite nret_writes_mem. apply (apply_writes_hidden (hidden L mo)); [exact Havw| exact Ha]. }
unfold canon. cbn. apply msview_nret_writes; [exact Hv3| exact Havw]. }
split; [|split].
- intros evs X Hst.
destruct (sstep_svc_inv segs ms mo x8 evs X Hsvc Hst)
as [(eff & mo2 & mo3 & Hs & Hh2 & Hm & ->) | [(eff & mo2 & evs0 & Hs & Hh2 & Hm & -> & ->)
| [(eff & mo2 & evs0 & code & Hs & Hh2 & -> & ->) | [(Hs & -> & ->) | (eff & mo2 & evs0 & sig & Hs & Hk & -> & ->)]]]].
+ apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
destruct (STEP _ _ _ Hs) as (mo3' & Hm' & Hd & HP & Hh3 & HC3 & Hv3).
rewrite Hm' in Hm. injection Hm as <-.
exists (canon eff), (nret ms eff), mo3'. split; [reflexivity|]. split; [exact Hv3|].
split; [exists mo2; split; assumption|]. auto.
+ exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
destruct (STEP _ _ _ Hs) as (mo3' & Hm' & _). rewrite Hm' in Hm. discriminate.
+ exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
destruct (Hok _ _ _ Hs) as (_ & Hh2' & _). congruence.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. rewrite Hchk in Hs. exact (Hnu _ Hs).
+
exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
destruct (Hok _ _ _ Hs) as (_ & Hh2' & _). rewrite m_killed_of_m_halted_none in Hk by congruence. discriminate.
- intros rsp mo2 mo' evs HP Hd'. destruct (Hcompl _ _ _ HP) as (eff & <- & Hc).
destruct (STEP _ _ _ Hc) as (mo3 & Hm & Hd & _ & Hh3 & HC3 & Hv3).
exists (nret ms eff), mo3. split.
+ unfold nret. eapply sstep_syscall; [exact Hh|exact Hsvc| | |exact Hm].
* apply check_syscall_ok_iff. rewrite Hchk. exact Hc.
* destruct (Hok _ _ _ Hc) as (_ & Hh2 & _). rewrite Hh2. exact Hh.
+ split; [exact Hv3|]. split; [exists mo2; split; [|exact Hd]|].
{ destruct (Hok _ _ _ Hc) as (HP' & _). exact HP'. }
split; [|exact Hh3].
eapply msim_trans; [apply msim_sym; eapply drift_msim; exact Hd'| eapply drift_msim; exact Hd].
- pose proof (receptive (sys_input segs ms x8) mo) as Hr.
destruct (syscall_spec_witness (sys_input segs ms x8) mo) as [eff mo' evs|] eqn:E.
+ apply check_syscall_ok_iff in Hr. rewrite Hchk in Hr. destruct (Hok _ _ _ Hr) as (HP & _). eauto.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hr. rewrite Hchk in Hr. exact (Hnu _ Hr).
Qed.

End Kit.

Ltac arm_resolve :=
cbn [lookup_ca checked_table]; autorewrite with arm_unfold; cbn [Z.eqb Pos.eqb]; autorewrite with arm_unfold.

Ltac lookup_solve :=
first [ exact lookup_ca_29 | exact lookup_ca_56 | exact lookup_ca_57 | exact lookup_ca_63 | exact lookup_ca_66
| exact lookup_ca_93 | exact lookup_ca_94 | exact lookup_ca_96 | exact lookup_ca_214 | exact lookup_ca_215
| exact lookup_ca_222 | exact lookup_ca_226 ].
Ltac dispatch K :=
erewrite check_syscall_arm;
[| rewrite in_sysno_si; change (bv_unsigned (Z_to_bv 64 K)) with K; lookup_solve];
autorewrite with arm_unfold;
rewrite ?in_a0_si, ?in_a1_si, ?in_a2_si, ?in_a3_si, ?in_a4_si, ?in_a5_si.

Lemma areg_view : forall L mo ms r, areg (msview L mo ms) r = areg ms r.
Proof. reflexivity. Qed.

Section FileNodes.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.

Definition file_facts (ms : machine_state) (mo : Model) (P : resp -> Model -> list event -> Prop) : Prop :=
exists x8 (chk : resp -> check_result),
ms_svc_pending ms = Some x8 /\
(forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) /\
(forall eff, chk eff <> CheckUnmodeled) /\
(forall eff mo2 evs, chk eff = CheckOk mo2 evs ->
P (canon eff) mo2 evs /\ m_halted mo2 = m_halted mo /\ m_vm mo2 = m_vm mo /\ fdinv mo2 /\
eff_zeros eff = [] /\ eff_unmaps eff = [] /\ eff_copies eff = [] /\
ranges_avoid (hidden L mo) (syscall_effect_accesses eff)) /\
(forall rsp mo2 evs, P rsp mo2 evs -> exists eff, canon eff = rsp /\ chk eff = CheckOk mo2 evs).

Lemma m_vm_with_fds : forall f mo, m_vm (with_fds f mo) = m_vm mo.
Proof. intros f []; reflexivity. Qed.

Lemma std_chanA : forall mo fd, fdinv mo -> (fd = 1 \/ fd = 2) ->
fd_lookup (m_fds mo) (fd32 (Z_to_bv 64 fd)) = Some (FdChannel (Z_to_bv 64 fd)) /\ w_is0 (Z_to_bv 64 fd) = false.
Proof. intros mo fd (M0 & M1 & M2 & _) [-> | ->]; split; first [exact M1 | exact M2 | reflexivity]. Qed.

Lemma fdinv_open_insert : forall mo ent,
fdinv mo -> fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
fdinv (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo).
Proof.
intros mo ent (M0 & M1 & M2 & MC & MF & MK) Hfree Hent. unfold fdinv. autorewrite with model.
set (fd := alloc_fd (m_fds mo)) in *.
assert (Hne : forall k e, fd_lookup (m_fds mo) k = Some e -> bv_eqb fd k = false).
{ intros k e Hk. destruct (bv_eqb fd k) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k. congruence. }
rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split].
- intros k c. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [intros H; inversion H; subst; destruct Hent| apply MC].
- intros k p off. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [intros H; inversion H; subst; exact Hent| apply MF].
- intros k e. rewrite fd_lookup_insert. destruct (bv_eqb fd k); [|apply MK].
intros H. inversion H; subst. destruct e; first [exact I | destruct Hent].
Qed.

Lemma fdinv_update_file : forall mo k p off off',
fdinv mo -> fd_lookup (m_fds mo) k = Some (FdFile p off) ->
fdinv (with_fds (fd_insert (m_fds mo) k (FdFile p off')) mo).
Proof.
intros mo k p off off' (M0 & M1 & M2 & MC & MF & MK) Hk. unfold fdinv. autorewrite with model.
assert (Hne : forall k' c, fd_lookup (m_fds mo) k' = Some (FdChannel c) -> bv_eqb k k' = false).
{ intros k' c Hk'. destruct (bv_eqb k k') eqn:E; [|reflexivity]. apply bv_eqb_eq in E. subst k'. congruence. }
rewrite !fd_lookup_insert. rewrite (Hne _ _ M0), (Hne _ _ M1), (Hne _ _ M2).
split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split].
- intros k' c. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [intros H; discriminate| apply MC].
- intros k' p' o. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MF]. intros H. inversion H; subst. exact (MF _ _ _ Hk).
- intros k' e. rewrite fd_lookup_insert. destruct (bv_eqb k k'); [|apply MK]. intros H. inversion H; subst. exact I.
Qed.

Lemma fdinv_remove : forall mo fd, fdinv mo -> 3 <= fd < 2^32 ->
fdinv (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo).
Proof.
intros mo fd (M0 & M1 & M2 & MC & MF & MK) Hfd. unfold fdinv. autorewrite with model.
rewrite !fd_lookup_remove.
assert (Hne : forall z, 0 <= z < 3 -> bv_eqb (Z_to_bv 64 fd) (Z_to_bv 64 z) = false).
{ intros z Hz. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. lia. }
rewrite !Hne by lia.
split; [exact M0|]. split; [exact M1|]. split; [exact M2|]. split; [|split].
- intros k c. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MC].
- intros k p off. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MF].
- intros k e. rewrite fd_lookup_remove. destruct (bv_eqb _ k); [discriminate| apply MK].
Qed.

Lemma close_factsA : forall ms mo fd,
at_node segs (NClose fd) ms -> fdinv mo -> file_facts ms mo (nstep (NClose fd) mo).
Proof.
intros ms mo fd (Hsvc & Hfd & Ha0) HX.
exists (Z_to_bv 64 57),
(fun eff => match fd_lookup (m_fds mo) (Z_to_bv 64 fd) with
| None => check_ret_only eff (errno_ret EBADF) mo []
| Some _ => check_ret_only eff (Z_to_bv 64 0) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []
end).
split; [exact Hsvc|]. split; [|split; [|split]].
- intros eff. dispatch 57. unfold check_close. rewrite Ha0. unfold fd32. rewrite abi_low32_small by lia. reflexivity.
- intros eff. destruct (fd_lookup _ _); apply check_ret_only_no_unmodeled.
- intros eff mo2 evs Hc. cbn [nstep].
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) eqn:Hlk; apply check_ret_only_ok_iff in Hc as (-> & -> & ->).
+ split; [split; [reflexivity|]; split; [exact Hfd|]; split; reflexivity|].
split; [apply m_halted_with_fds|]. split; [apply m_vm_with_fds|].
split; [apply fdinv_remove; assumption|]. repeat split; try reflexivity. apply ranges_avoid_nil.
+ split; [split; [reflexivity|]; split; [exact Hfd|]; split; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HX|]. repeat split; try reflexivity. apply ranges_avoid_nil.
- intros rsp mo2 evs (-> & _ & H). cbn [nstep] in H.
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)); destruct H as [-> ->].
+ exists (eff0 (Z_to_bv 64 0)). split; [reflexivity|]. apply check_ret_only_ok_iff. repeat split; reflexivity.
+ exists (efferr EBADF). split; [reflexivity|]. apply check_ret_only_ok_iff. repeat split; reflexivity.
Qed.

Lemma ioctl_factsA : forall ms mo fd req,
at_node segs (NIoctl fd req) ms -> fdinv mo -> file_facts ms mo (nstep (NIoctl fd req) mo).
Proof.
intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) HX.
exists (Z_to_bv 64 29), (fun eff => check_ret_only eff (errno_ret ENOTTY) mo []).
split; [exact Hsvc|]. split; [|split; [|split]].
- intros eff. dispatch 29. unfold check_ioctl. rewrite Ha0, Ha1. subst req.
unfold fd32, cmd32. rewrite !abi_low32_small by lia.
destruct HX as (M0 & M1 & M2 & _).
assert (Hl : exists c, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel c)).
{ assert (fd = 0 \/ fd = 1 \/ fd = 2) as [-> | [-> | ->]] by lia; eexists; eassumption. }
destruct Hl as [c ->]. change (tty_only_request (Z_to_bv 64 21523)) with true. reflexivity.
- intros eff. apply check_ret_only_no_unmodeled.
- intros eff mo2 evs Hc. apply check_ret_only_ok_iff in Hc as (-> & -> & ->). cbn [nstep].
split; [repeat split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HX|].
repeat split; try reflexivity. apply ranges_avoid_nil.
- intros rsp mo2 evs (-> & -> & ->). exists (efferr ENOTTY). split; [reflexivity|]. apply check_ret_only_ok_iff. repeat split; reflexivity.
Qed.

Lemma cstr_access_len_le : forall path fuel mp a,
~ In (Z_to_bv 8 0) path -> bytes_in mp a (path ++ [Z_to_bv 8 0]) ->
(cstr_access_len_aux mp (wa a) fuel <= Datatypes.S (length path))%nat.
Proof.
induction path as [|b path IH]; intros fuel mp a Hnz Hb.
- destruct fuel as [|fuel]; cbn [cstr_access_len_aux length]; [lia|].
cbn [app] in Hb. apply bytes_in_cons in Hb as [Hb _]. rewrite Hb. rewrite bv_eqb_refl. lia.
- destruct fuel as [|fuel]; cbn [cstr_access_len_aux length]; [lia|].
cbn [app] in Hb. apply bytes_in_cons in Hb as [Hb0 Hb]. rewrite Hb0.
assert (Hne : bv_eqb b (Z_to_bv 8 0) = false).
{ destruct (bv_eqb b (Z_to_bv 8 0)) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnz. left. congruence. }
rewrite Hne, wa_succ. pose proof (IH fuel mp (a + 1) ltac:(intros Hin; apply Hnz; right; exact Hin) Hb). lia.
Qed.

Lemma open_nstep_shape : forall path mo e mo2 evs,
nstep (NOpen path) mo e mo2 evs ->
(exists r, e = eff0 r) /\ evs = [] /\
(mo2 = mo \/ exists ent, mo2 = with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent) mo /\
fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None /\
match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end).
Proof.
intros path mo e mo2 evs [-> H]. unfold efferr in H.
assert (OR : forall ent, open_result mo ent e mo2 ->
match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end ->
(exists r, e = eff0 r) /\ ([] : list event) = [] /\
(mo2 = mo \/ exists ent', mo2 = with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) ent') mo /\
fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None /\
match ent' with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end)).
{ intros ent [(er & _ & -> & ->) | (Hlk & -> & ->)] Hent; unfold efferr.
- split; [eexists; reflexivity|]. split; [reflexivity|]. left; reflexivity.
- split; [eexists; reflexivity|]. split; [reflexivity|]. right. exists ent. auto. }
destruct (path_max <=? length path)%nat. { destruct H as [-> ->]. split; [eexists; reflexivity|]. auto. }
destruct path as [|c path']. { destruct H as [-> ->]. split; [eexists; reflexivity|]. auto. }
destruct (path_eqb (c :: path') dot_path). { exact (OR FdDir H I). }
destruct (fs_lookup (m_fs mo) (c :: path')) eqn:E.
- apply (OR _ H). cbn. congruence.
- destruct H as [-> ->]. split; [eexists; reflexivity|]. auto.
Qed.

Lemma open_factsA : forall ms mo path,
at_node segs (NOpen path) (msview L mo ms) -> lv_inv L mo -> fdinv mo ->
file_facts ms mo (nstep (NOpen path) mo).
Proof.
intros ms mo path Hat HI HX.

pose proof Hat as (Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hpv). cbn [ms_svc_pending ms_rom ms_mem msview restrict] in Hsvc, Hrom, Hpv.
change (mrestrict (hidden L mo) (ms_mem ms)) with (view L mo (ms_mem ms)) in Hpv.
destruct (bytes_at_view L segs Hsegs mo (ms_mem ms) _ _ Hpv) as [Hp Hvis].
assert (Hatf : at_node segs (NOpen path) ms) by (split; [exact Hsvc|]; split; [exact Ha0|]; split; [exact Hfl|]; split; [exact Hnz|]; split; [exact Hsl|]; split; [exact Hdd|]; split; assumption).
set (reads := [(areg ms 11, cstr_access_len_aux (ms_read_byte ms) (areg ms 11) path_max)]).
exists (Z_to_bv 64 56), (fun eff => check_copyins_after reads eff (open_check path (clear_copyins eff) mo)).
split; [exact Hsvc|]. split; [|split; [|split]].
- intros eff. apply (open_check_spec segs ms mo path eff Hatf).
- intros eff Hu. apply check_copyins_after_unmodeled in Hu. exact (open_check_no_unmodeled _ _ _ Hu).
- intros eff mo2 evs Hc. apply check_copyins_after_ok_iff in Hc as [Hci Hc].
apply open_check_ok_iff in Hc. rewrite clear_copyins_canon in Hc.
destruct (open_nstep_shape _ _ _ _ _ Hc) as ((r & Hr) & -> & Hmo2).
split; [exact Hc|].
assert (Hshape : m_halted mo2 = m_halted mo /\ m_vm mo2 = m_vm mo /\ fdinv mo2).
{ destruct Hmo2 as [->|(ent & -> & Hfree & Hent)]; [auto|].
split; [apply m_halted_with_fds|]. split; [apply m_vm_with_fds|]. apply fdinv_open_insert; assumption. }
destruct Hshape as (S1 & S2 & S3). split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
destruct eff as [rt ws zs us cs ci]. unfold canon in Hr. cbn in Hr. unfold eff0 in Hr. injection Hr as -> -> -> -> ->.
cbn in Hci. subst ci. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses app].
apply ranges_avoid_cons; [|apply ranges_avoid_nil].
pose proof Hp as (Hpa & Hpl & _). rewrite length_app in Hpl. cbn [length] in Hpl.
intros k Hk. unfold woff.
pose proof (cstr_access_len_le path path_max (ms_read_byte ms) (bv_unsigned (areg ms 11)) Hnz
(bytes_at_in segs ms _ _ Hrom Hp)) as Hlen.
rewrite wa_unsigned_id in Hlen.
replace (Z_to_bv 64 (bv_unsigned (areg ms 11) + Z.of_nat k)) with (wa (bv_unsigned (areg ms 11) + Z.of_nat k)) by reflexivity.
apply Hvis. rewrite length_app. cbn [length]. lia.
- intros rsp mo2 evs HP. exists (with_copyins reads rsp).
pose proof (open_nstep_canonical _ _ _ _ _ HP) as Hcan.
split; [rewrite canon_with_copyins; apply canon_of_canonical; exact Hcan|].
apply check_copyins_after_ok_iff. rewrite eff_copyins_with_copyins. split; [reflexivity|].
apply open_check_ok_iff. rewrite clear_with_copyins, (canon_of_canonical _ Hcan). exact HP.
Qed.

Lemma read_check_specA : forall ms mo fd buf count eff,
at_node segs (NRead fd buf count) ms -> fdinv mo ->
check_syscall (sys_input segs ms (Z_to_bv 64 63)) eff mo = read_check fd buf count eff mo.
Proof.

intros ms mo fd buf count eff (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Htop & Hwr) (M0 & M1 & M2 & MC & MF & MK).
pose proof Hwr as (Hb & Hbc & _). pose proof Hc as Hc'. unfold access_ok_walk_max in Hc'.
pose proof Htop as Htop'. unfold task_size_max, TASK_SIZE in Htop'.
pose proof (access_okb_wr_at segs ms buf count Hwr Hc Htop) as Hok.
dispatch 63. unfold check_read, read_check. rewrite Ha0, Ha1, Ha2, in_wmem_si.
unfold fd32. rewrite abi_low32_small by lia.
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|dnr dnw| ]|] eqn:Hlk; try reflexivity.
- exfalso. apply MC in Hlk. rewrite unsigned_lit in Hlk by lia. lia.
- rewrite Hok. cbn [negb].
destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs. 2:{ exfalso. exact (MF _ _ _ Hlk Hfs). }
rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT; lia).
rewrite unsigned_lit by lia. cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
assert (Hlen : Z.of_nat (length bs) <= count /\ Z.of_nat (length bs) < 2^64).
{ pose proof (length_file_read_le data off (Z_to_bv 64 count)) as Ln. fold bs in Ln.
unfold word_to_nat in Ln. rewrite unsigned_lit in Ln by lia. lia. }
unfold len_word at 1. replace (read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length bs))))
with (Some (match read_bytes_map (ms_writable_byte segs ms) (Z_to_bv 64 buf) (Z_to_bv 64 (Z.of_nat (length bs))) with Some x => x | None => [] end)).
2:{ pose proof (read_bytes_map_wr_at segs ms buf count (Z.of_nat (length bs)) Hwr ltac:(lia) ltac:(lia)) as W.
destruct (read_bytes_map _ _ _); [reflexivity| congruence]. }
reflexivity.
- exfalso. exact (MK _ _ Hlk).
- exfalso. exact (MK _ _ Hlk).
- exfalso. exact (MK _ _ Hlk).
- rewrite Hok. reflexivity.
- exfalso. exact (MK _ _ Hlk).
- exfalso. exact (MK _ _ Hlk).
- exfalso. exact (MK _ _ Hlk).
- exfalso. exact (MK _ _ Hlk).
Qed.

Lemma read_check_ok_iffA : forall fd buf count eff mo mo' evs,
fdinv mo ->
read_check fd buf count eff mo = CheckOk mo' evs <-> nstep (NRead fd buf count) mo eff mo' evs.
Proof.
intros fd buf count eff mo mo' evs (_ & _ & _ & _ & MF & _). unfold read_check. cbn [nstep].
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|dnr dnw| ]|] eqn:Hlk.
- split; [discriminate| tauto].
- destruct (fs_lookup (m_fs mo) p) as [data|]. 2:{ split; [discriminate|tauto]. }
cbv zeta. destruct (file_read data off (Z_to_bv 64 count)) as [|b bs'] eqn:Ebs.
+ rewrite check_ret_only_ok_iff. cbn [delivered_writes]. change (len_word (@nil byte)) with (Z_to_bv 64 0). tauto.
+ cbn [delivered_writes]. destruct eff as [ret ws zs us cs ci]. split.
* intros H. destruct ws as [|[a bs''] [|? ?]]; try discriminate. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (bv_eqb a (Z_to_bv 64 buf)) eqn:E1; [|discriminate].
destruct (listN_eqb bs'' (b :: bs')) eqn:E2; [|discriminate].
destruct (bv_eqb ret (len_word (b :: bs'))) eqn:E3; [|discriminate].
cbn [andb] in H. inversion H; subst. apply bv_eqb_eq in E1. apply listN_eqb_eq in E2. apply bv_eqb_eq in E3.
subst. repeat split; reflexivity.
* intros (-> & Heff & ->). inversion Heff; subst. rewrite !bv_eqb_refl, listN_eqb_refl. reflexivity.
- split; [discriminate| tauto].
- split; [discriminate| tauto].
- split; [discriminate| tauto].
- rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
- split; [discriminate| tauto].
- split; [discriminate| tauto].
- split; [discriminate| tauto].
- split; [discriminate| tauto].
- rewrite check_ret_only_ok_iff. unfold efferr, eff0. tauto.
Qed.

Lemma read_nstep_shape : forall fd buf count mo e mo2 evs,
nstep (NRead fd buf count) mo e mo2 evs ->
evs = [] /\
((exists r, e = eff0 r /\ mo2 = mo)
\/ (exists p off data, fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) /\ fs_lookup (m_fs mo) p = Some data /\
let bs := file_read data off (Z_to_bv 64 count) in
e = mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [] /\
mo2 = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo)).
Proof.
intros fd buf count mo e mo2 evs [-> H]. split; [reflexivity|].
destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [[ch|p off|p off|p off|p off| |sk|id w|dnr dnw| ]|] eqn:Hlk; try contradiction.
- destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|contradiction]. destruct H as [-> ->]. right.
exists p, off, data. split; [reflexivity|]. split; [exact Hfs|]. split; reflexivity.
- destruct H as [-> ->]. left. eexists. unfold efferr. split; reflexivity.
- destruct H as [-> ->]. left. eexists. unfold efferr. split; reflexivity.
Qed.

Lemma read_factsA : forall ms mo fd buf count,
at_node segs (NRead fd buf count) (msview L mo ms) -> lv_inv L mo -> fdinv mo ->
file_facts ms mo (nstep (NRead fd buf count) mo).
Proof.
intros ms mo fd buf count Hat HI HX.
pose proof Hat as (Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Htop & Hwrv). cbn [ms_svc_pending ms_mem msview restrict] in Hsvc, Hwrv.
change (mrestrict (hidden L mo) (ms_mem ms)) with (view L mo (ms_mem ms)) in Hwrv.
destruct (wr_at_view L segs Hsegs mo (ms_mem ms) _ _ Hwrv) as [Hwr Hvis].
assert (Hatf : at_node segs (NRead fd buf count) ms).
{ split; [exact Hsvc|]. split; [exact Hfd|]. split; [exact Ha0|]. split; [exact Ha1|]. split; [exact Ha2|]. split; [exact Hc|]. split; [exact Htop| exact Hwr]. }
exists (Z_to_bv 64 63), (fun eff => read_check fd buf count eff mo).
split; [exact Hsvc|]. split; [|split; [|split]].
- intros eff. apply (read_check_specA ms mo fd buf count eff Hatf HX).
- intros eff. apply read_check_no_unmodeled.
- intros eff mo2 evs Hck. apply (read_check_ok_iffA _ _ _ _ _ _ _ HX) in Hck.
destruct (read_nstep_shape _ _ _ _ _ _ _ Hck) as [-> Hsh].
destruct Hsh as [(r & -> & ->)|(p & off & data & Hlk & Hfs & He & ->)].
+ split; [exact Hck|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HX|].
repeat split; try reflexivity. apply ranges_avoid_nil.
+ cbv zeta in He. subst eff.
pose proof (length_file_read_le data off (Z_to_bv 64 count)) as Ln.
revert Hck Ln. generalize (file_read data off (Z_to_bv 64 count)) as bs. intros bs Hck Ln.
split; [rewrite canon_of_canonical by reflexivity; exact Hck|].
split; [apply m_halted_with_fds|]. split; [apply m_vm_with_fds|].
split; [eapply fdinv_update_file; eassumption|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
unfold word_to_nat in Ln. pose proof Hc as Hc0. unfold access_ok_walk_max in Hc0. pose proof Htop as Htop0. unfold task_size_max, TASK_SIZE in Htop0. rewrite unsigned_lit in Ln by lia.
destruct bs as [|b bs']; cbn [delivered_writes write_accesses]; [apply ranges_avoid_nil|].
apply ranges_avoid_cons; [|apply ranges_avoid_nil].
pose proof Hwr as (Hb0 & _). cbn [length] in Ln.
intros k Hk. cbn [length] in Hk. unfold woff. change (Z_to_bv 64 buf) with (wa buf). rewrite wa_unsigned by lia.
change (Z_to_bv 64 (buf + Z.of_nat k)) with (wa (buf + Z.of_nat k)). apply Hvis. lia.
- intros rsp mo2 evs HP. exists rsp. split.
+ apply canon_of_canonical. destruct (read_nstep_shape _ _ _ _ _ _ _ HP) as [_ [(r & -> & _)|(p & off & data & _ & _ & -> & _)]]; reflexivity.
+ apply (read_check_ok_iffA _ _ _ _ _ _ _ HX). exact HP.
Qed.

Lemma writev_check_specA : forall ms mo fd bufs iovs eff,
(fd = 1 \/ fd = 2) ->
areg ms 10 = Z_to_bv 64 fd ->
areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) ->
(1 <= length bufs <= 1024)%nat ->
Z.of_nat (length (concat bufs)) <= writev_bytes_max ->
ms_rom ms = seg_rom segs ->
bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) ->
Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs ->
bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE ->
Forall (fun iov => bv_unsigned (fst iov) + bv_unsigned (snd iov) <= TASK_SIZE) iovs ->
fdinv mo ->
check_syscall (sys_input segs ms (Z_to_bv 64 66)) eff mo
= writev_check fd (concat bufs)
(copy_iovecs_accesses (ms_read_byte ms) (areg ms 11) (length bufs))
(iov_prefix_accesses iovs) eff mo.
Proof.
intros ms mo fd bufs iovs eff Hfd Ha0 Ha2 Hcnt Htot Hrom Hiov Hbufs Hts Hbts Hminv.
unfold writev_bytes_max in Htot.
pose proof (iovs_ok_of_at segs _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
pose proof (Forall2_length Hbufs) as Hleq.
pose proof (bytes_at_in segs _ _ _ Hrom Hiov) as Hin.
destruct (import_iovecs_bytes_in iovs bufs (ms_read_byte ms) (bv_unsigned (areg ms 11)) Hin Hok
ltac:(lia) ltac:(lia) Hbts) as [Himp Hacc].
rewrite wa_unsigned_id, Hleq in Himp, Hacc.
dispatch 66. unfold check_writev. rewrite Ha0, Ha2, in_mem_si.
destruct (std_chanA mo fd Hminv Hfd) as [-> Hw]. rewrite Hw.
unfold iovcnt32. rewrite abi_low32_small by lia.
rewrite Himp, Hacc.
unfold writev_gathered, cap_iovecs. rewrite (cap_iovecs_id _ _ _ _ Hok) by (unfold MAX_RW_COUNT; lia).
rewrite (gather_prefix_ok _ _ _ Hok), (iovs_total_ok _ _ _ Hok).
cbv zeta. unfold writev_check.
destruct (length (concat bufs)) as [|n] eqn:EL.
- cbn [Z.of_nat Z.eqb Nat.eqb]. reflexivity.
- replace (Z.of_nat (Datatypes.S n) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Nat.eqb].
unfold len_word. rewrite EL. replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat (Datatypes.S n)))) with false.
2:{ symmetry. unfold addr_is_error_b, two_pow_64. rewrite unsigned_lit by lia. apply Z.ltb_ge. lia. }
reflexivity.
Qed.

Lemma iov_prefix_accesses_In : forall iovs left b k,
In (b, k) (iov_prefix_accesses iovs left) -> exists len, In (b, len) iovs /\ (k <= word_to_nat len)%nat.
Proof.

induction iovs as [|[base len] iovs IH]; intros left b k Hin.
- destruct left; cbn in Hin; contradiction.
- destruct left as [|l']; [cbn in Hin; contradiction|].
cbn [iov_prefix_accesses] in Hin. rewrite word_to_nat_bounded_eq_min in Hin.
destruct (Nat.eqb (Nat.min (word_to_nat len) (Datatypes.S l')) 0) eqn:E.
+ destruct (IH _ _ _ Hin) as (len' & Hin' & Hk). exists len'. split; [right; exact Hin'| exact Hk].
+ destruct Hin as [Heq|Hin].
* injection Heq as <- <-. exists len. split; [left; reflexivity| apply Nat.le_min_l].
* destruct (IH _ _ _ Hin) as (len' & Hin' & Hk). exists len'. split; [right; exact Hin'| exact Hk].
Qed.

Lemma Forall2_In_combine : forall {A B} (R : A -> B -> Prop) l1 l2 x,
Forall2 R l1 l2 -> In x l1 -> exists y, In (x, y) (combine l1 l2) /\ In y l2.
Proof.
intros A B R l1 l2 x H. induction H as [|a b l1 l2 Hab H IH]; intros Hin; [destruct Hin|].
destruct Hin as [<-|Hin].
- exists b. split; [left; reflexivity| left; reflexivity].
- destruct (IH Hin) as (y & H1 & H2). exists y. split; [right; exact H1| right; exact H2].
Qed.

Lemma writev_factsA : forall ms mo fd bufs,
at_node segs (NWritev fd bufs) (msview L mo ms) -> lv_inv L mo -> fdinv mo ->
file_facts ms mo (nstep (NWritev fd bufs) mo).
Proof.
intros ms mo fd bufs Hat HI HX.
pose proof Hat as (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & iovs & Hiovv & Hbufsv & Hts & Hbts).
rewrite !areg_view in Ha0, Ha2, Hiovv, Hts.
cbn [ms_svc_pending ms_rom ms_mem ms_regs msview restrict] in Hsvc, Hrom, Hiovv, Hbufsv.
change (mrestrict (hidden L mo) (ms_mem ms)) with (view L mo (ms_mem ms)) in Hiovv, Hbufsv.
destruct (bytes_at_view L segs Hsegs mo (ms_mem ms) _ _ Hiovv) as [Hiov Hiovvis].
assert (Hbufs : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs).
{ eapply Forall2_impl; [|exact Hbufsv]. intros iov bs [Hl Hb]. split; [exact Hl|]. exact (proj1 (bytes_at_view L segs Hsegs mo _ _ _ Hb)). }
assert (Hbufvis : forall iov bs, In (iov, bs) (combine iovs bufs) ->
snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
forall i, (i < length bs)%nat -> hidden L mo (wa (bv_unsigned (fst iov) + Z.of_nat i)) = false).
{ clear -Hbufsv Hsegs. induction Hbufsv as [|iov bs iovs bufs [Hl Hb] _ IH]; intros iov' bs' Hin; [destruct Hin|].
cbn [combine] in Hin. destruct Hin as [Heq|Hin]; [|apply IH; exact Hin].
injection Heq as <- <-. split; [exact Hl|]. exact (proj2 (bytes_at_view L segs Hsegs mo _ _ _ Hb)). }
unfold writev_bytes_max in Htot. pose proof (Forall2_length Hbufs) as Hleq.
pose proof (iovs_ok_of_at segs _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
set (reads := copy_iovecs_accesses (ms_read_byte ms) (areg ms 11) (length bufs)).
assert (Hreads : reads = map (fun k => (wa (bv_unsigned (areg ms 11) + 16 * Z.of_nat k), 16%nat)) (seq 0 (length iovs))).
{ unfold reads. rewrite <- Hleq. rewrite <- (wa_unsigned_id (areg ms 11)) at 1.
apply (copy_iovecs_accesses_bytes_in iovs bufs); [eapply bytes_at_in; eassumption| exact Hok]. }

assert (Havr : ranges_avoid (hidden L mo) reads).
{ rewrite Hreads. intros a n Hin. apply in_map_iff in Hin as (k & Heq & Hk). injection Heq as <- <-.
apply in_seq in Hk. pose proof Hiov as (Ha11 & _). apply range_avoids_of_bytes; [lia|].
intros i Hi. replace (bv_unsigned (areg ms 11) + 16 * Z.of_nat k + i) with (bv_unsigned (areg ms 11) + Z.of_nat (16 * k + Z.to_nat i)) by lia.
apply Hiovvis. rewrite length_iovec_bytes. lia. }
assert (Havp : forall k, ranges_avoid (hidden L mo) (iov_prefix_accesses iovs k)).
{ intros k a n Hin. apply iov_prefix_accesses_In in Hin as (len & Hin & Hn).
destruct (Forall2_In_combine _ _ _ _ Hbufs Hin) as (bs & Hin2 & _).
destruct (Hbufvis _ _ Hin2) as [Hl Hvis]. cbn [fst snd] in Hl, Hvis.
assert (Hlen : word_to_nat len = length bs).
{ rewrite Hl. apply word_to_nat_of_nat.
pose proof (in_combine_r _ _ _ _ Hin2) as Hinb. apply in_split in Hinb as (l1 & l2 & El).
assert (length (concat bufs) = length (concat l1) + (length bs + length (concat l2)))%nat.
{ rewrite El, concat_app. cbn [concat]. rewrite !length_app. reflexivity. } lia. }
pose proof (bv_unsigned_in_range 64 a) as Har.
intros i Hi. unfold woff. change (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) with (wa (bv_unsigned a + Z.of_nat i)).
apply Hvis. lia. }
exists (Z_to_bv 64 66), (fun eff => writev_check fd (concat bufs) reads (iov_prefix_accesses iovs) eff mo).
split; [exact Hsvc|]. split; [|split; [|split]].
- intros eff. apply (writev_check_specA ms mo fd bufs iovs eff); assumption.
- intros eff. unfold writev_check.
destruct (Nat.eqb (length (concat bufs)) 0); [apply check_ret_only_copyins_no_unmodeled|].
destruct eff as [ret [|? ?] [|? ?] [|? ?] [|? ?] ci]; try discriminate. destruct (_ && _); [destruct (access_ranges_eqb _ _)|]; discriminate.
- intros eff mo2 evs. unfold writev_check. cbn [nstep].
destruct (Nat.eqb_spec (length (concat bufs)) 0) as [E|E].
+ rewrite check_ret_only_copyins_ok_iff. intros (-> & -> & ->).
split. { split; [reflexivity|]. left. split; [destruct (concat bufs); [reflexivity| cbn in E; lia]|]. split; reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [exact HX|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
unfold syscall_effect_accesses. rewrite eff_copyins_with_copyins. unfold eff0, with_copyins. cbn [eff_writes write_accesses]. rewrite app_nil_r. exact Havr.
+ destruct eff as [ret ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct us; [|discriminate]. destruct cs; [|discriminate].

destruct ((1 <=? bv_unsigned ret) && (bv_unsigned ret <=? Z.of_nat (length (concat bufs))) && negb (addr_is_error_b ret)) eqn:C; [|discriminate].
destruct (access_ranges_eqb ci (reads ++ iov_prefix_accesses iovs (Z.to_nat (bv_unsigned ret)))) eqn:Ceq; [|discriminate].
intros H. inversion H; subst. apply andb_prop in C as [C _]. apply andb_prop in C as [C1 C2].
apply Z.leb_le in C1. apply Z.leb_le in C2. apply access_ranges_eqb_eq in Ceq. subst ci.
split. { split; [reflexivity|]. right. exists (bv_unsigned ret). split; [lia|]. split; [|reflexivity].
unfold canon, eff0. cbn. rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [reflexivity|]. split; [reflexivity|]. split; [exact HX|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses]. rewrite app_nil_r.
apply ranges_avoid_app; [exact Havr| apply Havp].
- intros rsp mo2 evs (-> & [(E & -> & ->) | (k & Hk & -> & ->)]).
+ exists (with_copyins reads (eff0 (Z_to_bv 64 0))). split; [reflexivity|].
unfold writev_check. rewrite E. cbn [length Nat.eqb].
apply check_ret_only_copyins_ok_iff. repeat split; reflexivity.
+ exists (mkEffectU (Z_to_bv 64 k) [] [] [] [] (reads ++ iov_prefix_accesses iovs (Z.to_nat k))). split; [reflexivity|].
unfold writev_check.
destruct (Nat.eqb_spec (length (concat bufs)) 0) as [E|E]; [lia|].
rewrite unsigned_lit by lia.
replace (1 <=? k) with true by (symmetry; apply Z.leb_le; lia).
replace (k <=? Z.of_nat (length (concat bufs))) with true by (symmetry; apply Z.leb_le; lia).
replace (addr_is_error_b (Z_to_bv 64 k)) with false
by (symmetry; unfold addr_is_error_b, two_pow_64; rewrite unsigned_lit by lia; apply Z.ltb_ge; lia).
rewrite access_ranges_eqb_refl. reflexivity.
Qed.

End FileNodes.
