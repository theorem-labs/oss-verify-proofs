(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs Progress.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdStepA.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Check.

Lemma w_is0_rlen : forall len, 0 < len -> len <= 2^40 -> w_is0 (Z_to_bv 64 len) = false.
Proof. intros. rewrite w_is0_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma gates_off0 : mmap_off_aligned_b (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gates_anon_flags : forall fl, fl = FL_ANON \/ fl = FL_FIXED \/ fl = FL_FIXED_NR -> mmap_anon_b (Z_to_bv 64 fl) = true.
Proof. intros fl [-> | [-> | ->]]; vm_compute; reflexivity. Qed.

Lemma modeled_anon : mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 FL_ANON) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma noreserve_anon : mmap_noreserve_b (Z_to_bv 64 FL_ANON) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma modeled_fixed : forall fl, fl = FL_FIXED \/ fl = FL_FIXED_NR ->
mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 fl) (Z_to_bv 64 0) = false /\
mmap_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 fl) (Z_to_bv 64 0) = false /\
mmap_fixed_noaccess_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 fl) (Z_to_bv 64 0) = false /\
mmap_fixed_rw_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 fl) (Z_to_bv 64 0) = true.
Proof. intros fl [-> | ->]; vm_compute; repeat split; reflexivity. Qed.
Lemma noreserve_fixed : mmap_noreserve_b (Z_to_bv 64 FL_FIXED) = false.
Proof. vm_compute. reflexivity. Qed.
Lemma noreserve_fixed_nr : mmap_noreserve_b (Z_to_bv 64 FL_FIXED_NR) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rlen_facts : forall len, 0 < len -> len <= 2^40 ->
len <= rlen len /\ rlen len < len + 4096 /\ rlen len mod 4096 = 0 /\ 0 < rlen len /\ rlen len < 2^41 /\
bv_unsigned (rlenw len) = rlen len /\ page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = rlen len.
Proof.
intros len H1 H2. unfold rlenw, rlen, page_round_up_Z, page_size.
pose proof (Z.div_mod (len + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (len + 4096 - 1) 4096 ltac:(lia)).
assert (Hm : (len + 4096 - 1) / 4096 * 4096 mod 4096 = 0) by apply Z_mod_mult.
rewrite !unsigned_lit by lia. lia.
Qed.

Lemma mmap_kind_cases : forall addr prot flags,
match mmap_kind addr prot flags with
| KAnon => prot = PROT_RW /\ flags = FL_ANON /\ addr = 0
| KFixed => prot = PROT_RW /\ flags = FL_FIXED
| KRemap => prot = PROT_RW /\ flags = FL_FIXED_NR
| KNone => True
end.
Proof.
intros addr prot flags. unfold mmap_kind.
destruct (Z.eqb_spec prot PROT_RW); cbn [negb]; [|exact I].
destruct (Z.eqb_spec flags FL_ANON); destruct (Z.eqb_spec addr 0); cbn [andb];
destruct (Z.eqb_spec flags FL_FIXED); try (exfalso; lia); destruct (Z.eqb_spec flags FL_FIXED_NR); try (exfalso; lia); auto.
Qed.

Lemma mmap_errno_ENOMEM : forall r, errno_ret_in mmap_errnos r = true -> r = errno_ret ENOMEM.
Proof. intros r H. apply errno_ret_in_true in H as (e & [<-|[]] & ->). reflexivity. Qed.

Lemma unsigned_errno_ENOMEM : bv_unsigned (errno_ret ENOMEM) = 2^64 - 12.
Proof. reflexivity. Qed.

Lemma placed_not_errno0 : forall (r : word) n, 0 <= n -> bv_unsigned r + n <= 2^64 - 4096 -> errno_ret_in mmap_errnos r = false.
Proof.
intros r n Hn H. destruct (errno_ret_in mmap_errnos r) eqn:E; [|reflexivity]. exfalso.
apply mmap_errno_ENOMEM in E. subst r. rewrite unsigned_errno_ENOMEM in H. lia.
Qed.
Lemma below_top_room : forall h z, z <= alloc_top h -> z <= 2^64 - 4096.
Proof. intros h z H. pose proof (alloc_top_room h) as R. unfold stack_max_size, two_pow_64 in R. lia. Qed.

Lemma listNN_eqb_refl : forall l, listNN_eqb l l = true.
Proof. intros. apply listNN_eqb_eq. reflexivity. Qed.

Section Anon.
Variable len : Z.
Hypothesis Hlen : 0 < len /\ len <= 2^40.
#[local] Notation CHK eff mo := (check_mmap (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 FL_ANON) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).

Lemma check_anon_red : forall eff mo,
CHK eff mo =
match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mmap_errnos r
then match zs with [] => CheckOk mo [] | _ => CheckReject end
else if (bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + rlen len <=? alloc_top (m_vmmaps mo))%Z
&& region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (rlenw len)
&& mmap_noreserve_backed_ok (Z_to_bv 64 FL_ANON) mo (rlen len)
&& listNN_eqb zs [(r, rlenw len)]
then CheckOk (grant_model mo r (rlenw len)) [] else CheckReject
| _ => CheckReject
end.
Proof.
intros eff mo. pose proof (rlen_facts len (proj1 Hlen) (proj2 Hlen)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
unfold check_mmap. rewrite gates_off0, (gates_anon_flags FL_ANON) by auto. cbn [negb].
rewrite (w_is0_rlen len) by lia. rewrite modeled_anon. rewrite R7.
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct us; [|reflexivity]. destruct cs; [|reflexivity]. destruct ci; [|reflexivity].
destruct (errno_ret_in _ r); [reflexivity|]. cbv zeta.
unfold grant_model, h_add, with_mmap_backing. rewrite noreserve_anon. fold (rlenw len). reflexivity.
Qed.

Lemma check_anon_ok : forall eff mo mo2 evs,
errno_ret_in mmap_errnos (eff_ret eff) = false ->
CHK eff mo = CheckOk mo2 evs ->
evs = [] /\ exists r, eff = mkEffectU r [] [(r, rlenw len)] [] [] [] /\ anon_place_ok mo r (rlen len) = true /\
mo2 = grant_model mo r (rlenw len).
Proof.
intros eff mo mo2 evs Hnf H. rewrite check_anon_red in H.
destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
cbn [eff_ret] in Hnf. rewrite Hnf in H.
destruct ((bv_unsigned r mod page_size =? 0)%Z && (0 <? bv_unsigned r)%Z
&& (bv_unsigned r + rlen len <=? alloc_top (m_vmmaps mo))%Z
&& region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) r (rlenw len)
&& mmap_noreserve_backed_ok (Z_to_bv 64 FL_ANON) mo (rlen len)
&& listNN_eqb zs [(r, rlenw len)]) eqn:C; [|discriminate].
injection H as <- <-.
apply andb_prop in C as [C Cz]. apply andb_prop in C as [C _]. apply listNN_eqb_eq in Cz. subst zs.
split; [reflexivity|]. exists r. split; [reflexivity|]. split; [|reflexivity].
unfold anon_place_ok. unfold rlenw in C. exact C.
Qed.

Lemma check_anon_grant : forall mo r,
anon_place_ok mo r (rlen len) = true -> vm_backing_used mo + rlen len <= vm_limit (m_vmmaps mo) ->
CHK (mkEffectU r [] [(r, rlenw len)] [] [] []) mo = CheckOk (grant_model mo r (rlenw len)) [].
Proof.
intros mo r Hp Hb. pose proof (rlen_facts len (proj1 Hlen) (proj2 Hlen)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
rewrite check_anon_red.
pose proof Hp as Hp0. unfold anon_place_ok in Hp. apply andb_prop in Hp as [Hp _]. apply andb_prop in Hp as [_ Hce]. apply Z.leb_le in Hce.
rewrite (placed_not_errno0 r (rlen len)) by (first [exact (below_top_room _ _ Hce) | lia]).
unfold anon_place_ok in Hp0. unfold rlenw. rewrite Hp0. unfold mmap_noreserve_backed_ok. rewrite noreserve_anon.
replace (vm_backing_used mo + rlen len <=? vm_limit (m_vmmaps mo)) with true by (symmetry; apply Z.leb_le; exact Hb).
rewrite listNN_eqb_refl. reflexivity.
Qed.

Lemma check_anon_nu : forall eff mo, CHK eff mo <> CheckUnmodeled.
Proof.
intros eff mo. rewrite check_anon_red.
destruct eff as [r [|? ?] zs [|? ?] [|? ?] [|? ?]]; try discriminate.
destruct (errno_ret_in _ r); [destruct zs; discriminate|]. destruct (_ && _); discriminate.
Qed.

Lemma anon_place_not_errno : forall mo r, anon_place_ok mo r (rlen len) = true -> errno_ret_in mmap_errnos r = false.
Proof.
intros mo r Hp. pose proof (rlen_facts len (proj1 Hlen) (proj2 Hlen)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
unfold anon_place_ok in Hp. apply andb_prop in Hp as [Hp _]. apply andb_prop in Hp as [_ Hce]. apply Z.leb_le in Hce.
apply (placed_not_errno0 r (rlen len)); [lia| exact (below_top_room _ _ Hce)].
Qed.

End Anon.

Section Fixed.
Variables addr len fl : Z.
Hypothesis Hg : fixed_gates addr len.
Hypothesis Hfl : fl = FL_FIXED \/ fl = FL_FIXED_NR.
#[local] Notation CHK eff mo := (check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 fl) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).
#[local] Notation a := (Z_to_bv 64 addr).
#[local] Notation n := (rlenw len).

Definition repl (mo : Model) : Model :=
with_mmap_replacement (Z_to_bv 64 fl) a n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) a n) mo).
Definition fresh (mo : Model) : Model := with_mmap_backing (Z_to_bv 64 fl) a n (grant_model mo a n).

Lemma repl_fixed : fl = FL_FIXED -> forall mo, repl mo = commit_model mo a n.
Proof. intros H mo. unfold repl, with_mmap_replacement, with_mmap_backing. rewrite H, noreserve_fixed. reflexivity. Qed.
Lemma repl_fixed_nr : fl = FL_FIXED_NR -> forall mo, repl mo = remap_model mo a n.
Proof. intros H mo. unfold repl, with_mmap_replacement, with_mmap_backing. rewrite H, noreserve_fixed_nr. reflexivity. Qed.
Lemma fresh_fixed : fl = FL_FIXED -> forall mo, fresh mo = grant_model mo a n.
Proof. intros H mo. unfold fresh, with_mmap_backing. rewrite H, noreserve_fixed. reflexivity. Qed.

Lemma fixed_facts :
0 < len /\ len <= 2^40 /\ 0 < addr /\ addr mod 4096 = 0 /\ addr + rlen len <= grant_ceilA /\
bv_unsigned a = addr /\ bv_unsigned n = rlen len /\ addr < 2^64 /\
page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = rlen len /\ rlen len mod 4096 = 0 /\ 0 < rlen len.
Proof.
destruct Hg as (G1 & G2 & G3 & G4 & G5). pose proof (rlen_facts len G1 G2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
unfold grant_ceilA, sp_window_hi, stack_max_size in *. rewrite unsigned_lit by lia. repeat split; try assumption; lia.
Qed.

Lemma check_fixed_red : forall eff mo, addr + rlen len <= alloc_top (m_vmmaps mo) ->
CHK eff mo =
if fixed_contained mo a n then
match eff with
| mkEffectU r [] zs us [] [] =>
if errno_ret_in mmap_errnos r
then match zs with
| _ :: _ => CheckReject
| [] => match us with
| [] => CheckOk mo []
| _ => if listNN_eqb us [(a, n)]
then CheckOk (with_mmap_destroyed a n (mmap_fixed_destroyed_next (m_vmmaps mo) a n) mo) []
else CheckReject
end
end
else match us with
| _ :: _ => CheckReject
| [] => if bv_eqb r a && listNN_eqb zs [(a, n)] && mmap_fixed_rw_budget_ok (Z_to_bv 64 fl) mo a n
then CheckOk (repl mo) [] else CheckReject
end
| _ => CheckReject
end
else if fixed_free mo a n then
match eff with
| mkEffectU r [] zs [] [] [] =>
if errno_ret_in mmap_errnos r
then match zs with [] => CheckOk mo [] | _ => CheckReject end
else if bv_eqb r a && listNN_eqb zs [(a, n)] && mmap_noreserve_backed_ok (Z_to_bv 64 fl) mo (rlen len)
then CheckOk (fresh mo) [] else CheckReject
| _ => CheckReject
end
else if region_free (vm_reserved (m_vmmaps mo)) a n then
match eff with
| mkEffectU r [] zs us [] [] =>
if errno_ret_in mmap_errnos r
then match zs with
| _ :: _ => CheckReject
| [] => match us with
| [] => CheckOk mo []
| _ => if listNN_eqb us [(a, n)]
then CheckOk (with_mmap_destroyed a n (mmap_fixed_destroyed_next (m_vmmaps mo) a n) mo) []
else CheckReject
end
end
else match us with
| _ :: _ => CheckReject
| [] => if bv_eqb r a && listNN_eqb zs [(a, n)] && mmap_fixed_rw_span_budget_ok (Z_to_bv 64 fl) mo a n
then CheckOk (with_mmap_replacement (Z_to_bv 64 fl) a n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) a n) mo)) []
else CheckReject
end
| _ => CheckReject
end
else CheckUnmodeled.
Proof.
intros eff mo Htop. pose proof fixed_facts as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
destruct (modeled_fixed fl Hfl) as (M1 & M2 & M3 & M4).
unfold check_mmap. rewrite gates_off0, (gates_anon_flags fl) by (destruct Hfl; auto). cbn [negb].
rewrite (w_is0_rlen len) by lia. rewrite M1, M2, M3, M4. cbv zeta. rewrite PR.
replace (two_pow_64 <=? bv_unsigned a + rlen len) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, grant_ceilA, sp_window_hi, stack_max_size in *; lia).
replace (negb (bv_unsigned a + rlen len <=? alloc_top (m_vmmaps mo))) with false by (symmetry; rewrite Ua, (proj2 (Z.leb_le _ _)) by lia; reflexivity).
replace (negb (bv_unsigned a mod page_size =? 0)) with false by (symmetry; rewrite Ua; unfold page_size; rewrite G4; reflexivity).
replace (negb (0 <? bv_unsigned a)) with false by (symmetry; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
unfold fixed_contained, fixed_free, repl, fresh, grant_model, h_add. fold (rlenw len). rewrite ?Un. reflexivity.
Qed.

Lemma check_fixed_ok : forall eff mo mo2 evs, addr + rlen len <= alloc_top (m_vmmaps mo) ->
errno_ret_in mmap_errnos (eff_ret eff) = false ->
(fixed_contained mo a n = true \/ fixed_free mo a n = true) ->
CHK eff mo = CheckOk mo2 evs ->
evs = [] /\ eff = mkEffectU a [] [(a, n)] [] [] [] /\
((fixed_contained mo a n = true /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 fl) mo a n = true /\ mo2 = repl mo)
\/ (fixed_contained mo a n = false /\ fixed_free mo a n = true /\ mo2 = fresh mo)).
Proof.
intros eff mo mo2 evs Htop He Hcf H. rewrite (check_fixed_red eff mo Htop) in H.
destruct (fixed_contained mo a n) eqn:Hc.
- destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
cbn [eff_ret] in He. rewrite He in H.
destruct us; [|discriminate].
destruct (bv_eqb r a && listNN_eqb zs [(a, n)] && mmap_fixed_rw_budget_ok (Z_to_bv 64 fl) mo a n) eqn:C; [|discriminate].
injection H as <- <-. apply andb_prop in C as [C Cb]. apply andb_prop in C as [C1 C2]. apply bv_eqb_eq in C1. apply listNN_eqb_eq in C2.
subst. split; [reflexivity|]. split; [reflexivity|]. left. auto.
- destruct Hcf as [Hcf|Hff]; [discriminate|]. rewrite Hff in H.
destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
cbn [eff_ret] in He. rewrite He in H.
destruct (bv_eqb r a && listNN_eqb zs [(a, n)] && mmap_noreserve_backed_ok (Z_to_bv 64 fl) mo (rlen len)) eqn:C; [|discriminate].
injection H as <- <-. apply andb_prop in C as [C Cb]. apply andb_prop in C as [C1 C2]. apply bv_eqb_eq in C1. apply listNN_eqb_eq in C2.
subst. split; [reflexivity|]. split; [reflexivity|]. right. auto.
Qed.

Lemma check_fixed_nu : forall eff mo, addr + rlen len <= alloc_top (m_vmmaps mo) ->
fixed_contained mo a n = true \/ fixed_free mo a n = true -> CHK eff mo <> CheckUnmodeled.
Proof.
intros eff mo Htop Hc. rewrite (check_fixed_red eff mo Htop).
destruct (fixed_contained mo a n).
- destruct eff as [r [|? ?] zs us [|? ?] [|? ?]]; try discriminate.
destruct (errno_ret_in mmap_errnos r).
+ destruct zs; [|discriminate]. destruct us as [|u us]; [discriminate|]. cbv iota. destruct (listNN_eqb _ _); discriminate.
+ destruct us; [destruct (_ && _); discriminate| discriminate].
- destruct Hc as [Hc|Hc]; [discriminate| rewrite Hc].
destruct eff as [r [|? ?] zs [|? ?] [|? ?] [|? ?]]; try discriminate.
destruct (errno_ret_in _ r); [destruct zs; discriminate| destruct (_ && _); discriminate].
Qed.

Lemma check_fixed_repl : forall mo, addr + rlen len <= alloc_top (m_vmmaps mo) -> fixed_contained mo a n = true ->
mmap_fixed_rw_budget_ok (Z_to_bv 64 fl) mo a n = true ->
CHK (mkEffectU a [] [(a, n)] [] [] []) mo = CheckOk (repl mo) [].
Proof.
intros mo Htop Hc Hb. pose proof fixed_facts as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
rewrite (check_fixed_red _ mo Htop), Hc. rewrite (placed_not_errno0 a (rlen len)) by (first [rewrite Ua; exact (below_top_room _ _ Htop) | lia]).
rewrite bv_eqb_refl, listNN_eqb_refl, Hb. reflexivity.
Qed.

Lemma check_fixed_fresh : forall mo, addr + rlen len <= alloc_top (m_vmmaps mo) -> fixed_contained mo a n = false -> fixed_free mo a n = true ->
mmap_noreserve_backed_ok (Z_to_bv 64 fl) mo (rlen len) = true ->
CHK (mkEffectU a [] [(a, n)] [] [] []) mo = CheckOk (fresh mo) [].
Proof.
intros mo Htop Hc Hf Hb. pose proof fixed_facts as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
rewrite (check_fixed_red _ mo Htop), Hc, Hf. rewrite (placed_not_errno0 a (rlen len)) by (first [rewrite Ua; exact (below_top_room _ _ Htop) | lia]).
rewrite bv_eqb_refl, listNN_eqb_refl, Hb. reflexivity.
Qed.

End Fixed.

Section Munmap.
Variables addr len : Z.
Hypothesis Hlen : 0 < len /\ len <= 2^40.
Hypothesis Haddr : addr mod 4096 = 0 /\ 0 <= addr /\ addr + rlen len <= TASK_SIZE.
#[local] Notation CHK eff mo := (check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo).
#[local] Notation a := (Z_to_bv 64 addr).
#[local] Notation n := (rlenw len).

Lemma munmap_facts0 : bv_unsigned a = addr /\ bv_unsigned n = rlen len /\
page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) = rlen len /\ 0 < rlen len.
Proof.
pose proof (rlen_facts len (proj1 Hlen) (proj2 Hlen)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
pose proof Haddr as HA. unfold TASK_SIZE in HA. rewrite unsigned_lit by lia. auto.
Qed.

Lemma check_munmap_red : forall eff mo, map_has (vm_maps (m_vmmaps mo)) a n = true ->
CHK eff mo =
match eff with
| mkEffectU r [] [] us [] [] =>
if w_is0 r && listNN_eqb us [(a, n)] then CheckOk (munmap_model mo a n) [] else CheckReject
| _ => CheckReject
end.
Proof.
intros eff mo Hh. pose proof munmap_facts0 as (Ua & Un & PR & Rp).
unfold check_munmap. rewrite (w_is0_rlen len) by lia. rewrite Ua. unfold page_size. rewrite (proj1 Haddr). cbn [Z.eqb negb orb].
cbv zeta. rewrite PR.
replace (TASK_SIZE <? addr + rlen len) with false by (symmetry; apply Z.ltb_ge; lia).
fold (rlenw len). rewrite Hh. unfold munmap_model, with_mmap_destroyed, h_munmap. rewrite Ua, Un. reflexivity.
Qed.

Lemma check_munmap_ok : forall eff mo mo2 evs, map_has (vm_maps (m_vmmaps mo)) a n = true ->
CHK eff mo = CheckOk mo2 evs ->
evs = [] /\ mo2 = munmap_model mo a n /\ exists us, eff = mkEffectU (Z_to_bv 64 0) [] [] us [] [] /\ us = [(a, n)].
Proof.
intros eff mo mo2 evs Hh H. rewrite (check_munmap_red eff mo Hh) in H.
destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r && listNN_eqb us [(a, n)]) eqn:C; [|discriminate]. injection H as <- <-.
apply andb_prop in C as [C1 C2]. apply listNN_eqb_eq in C2. unfold w_is0 in C1. apply bv_eqb_eq in C1. subst.
split; [reflexivity|]. split; [reflexivity|]. exists [(a, n)]. auto.
Qed.

Lemma check_munmap_intro : forall mo, map_has (vm_maps (m_vmmaps mo)) a n = true ->
CHK (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []) mo = CheckOk (munmap_model mo a n) [].
Proof.
intros mo Hh. rewrite (check_munmap_red _ mo Hh). change (w_is0 (Z_to_bv 64 0)) with true. rewrite listNN_eqb_refl. reflexivity.
Qed.

Lemma check_munmap_nu : forall eff mo, map_has (vm_maps (m_vmmaps mo)) a n = true -> CHK eff mo <> CheckUnmodeled.
Proof.
intros eff mo Hh. rewrite (check_munmap_red eff mo Hh).
destruct eff as [r [|? ?] [|? ?] us [|? ?] [|? ?]]; try discriminate. destruct (_ && _); discriminate.
Qed.

End Munmap.

End Check.

Lemma nret_mem : forall ms r ws zs us ci,
ms_mem (nret ms (mkEffectU r ws zs us [] ci)) = apply_writes (apply_zeros (apply_unmaps (ms_mem ms) us) zs) ws.
Proof. reflexivity. Qed.

Lemma msview_nret_intro : forall L mo mo2 ms r w1 z1 u1 i1 w2 z2 u2 i2,
view L mo2 (apply_writes (apply_zeros (apply_unmaps (ms_mem ms) u1) z1) w1)
= apply_writes (apply_zeros (apply_unmaps (view L mo (ms_mem ms)) u2) z2) w2 ->
msview L mo2 (nret ms (mkEffectU r w1 z1 u1 [] i1)) = nret (msview L mo ms) (mkEffectU r w2 z2 u2 [] i2).
Proof.
intros L mo mo2 ms r w1 z1 u1 i1 w2 z2 u2 i2 Hm.
unfold msview, restrict, nret, advance_past_svc, apply_effect, set_reg, view in *.
replace (bv_eqb (10 : bv 5) 0) with false by reflexivity.
cbn [ms_regs ms_fregs ms_pc_val ms_pc ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins apply_copies] in *.
rewrite Hm. reflexivity.
Qed.

Lemma zeros_cover_cons : forall a n l x,
zeros_cover ((a, n) :: l) x = in_rng (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (bv_unsigned x) || zeros_cover l x.
Proof. reflexivity. Qed.

Lemma apply_zeros_1 : forall m a n x,
apply_zeros m [(a, n)] x = if inR a n (bv_unsigned x) then Some zero8 else m x.
Proof. intros. cbn [apply_zeros]. rewrite zeros_cover_cons. cbn [zeros_cover existsb]. rewrite orb_false_r. reflexivity. Qed.

Lemma apply_unmaps_cons : forall m a n l x,
apply_unmaps m ((a, n) :: l) x = if inR a n (bv_unsigned x) || zeros_cover l x then None else m x.
Proof. intros. cbn [apply_unmaps]. rewrite zeros_cover_cons. reflexivity. Qed.

Lemma apply_writes_bytes : forall (f : word -> byte) xs m y,
apply_writes m (map (fun x => (x, [f x])) xs) y = if existsb (bv_eqb y) xs then Some (f y) else m y.
Proof.
induction xs as [|x xs IH]; intros m y; cbn [map apply_writes existsb]; [reflexivity|].
rewrite IH. cbn [write_to_mem].
destruct (bv_eqb y x) eqn:E; cbn [orb]; [| reflexivity].
apply bv_eqb_eq in E. subst. destruct (existsb (bv_eqb x) xs); reflexivity.
Qed.

Lemma existsb_bv_eqb : forall (y : word) xs, existsb (bv_eqb y) xs = true <-> In y xs.
Proof.
intros y xs. rewrite existsb_exists. split.
- intros (x & Hin & E). apply bv_eqb_eq in E. subst. exact Hin.
- intros Hin. exists y. split; [exact Hin| apply bv_eqb_refl].
Qed.

Lemma zbytes_In : forall k lo (y : word), 0 <= lo -> lo + Z.of_nat k <= 2^64 ->
In y (zbytes lo k) <-> lo <= bv_unsigned y < lo + Z.of_nat k.
Proof.
induction k as [|k IH]; intros lo y H0 Hb.
- cbn. split; [intros []| lia].
- cbn [zbytes In]. rewrite (IH (lo + 1) y) by lia. split.
+ intros [<-|H]; [rewrite unsigned_lit by lia; lia| lia].
+ intros H. destruct (Z.eq_dec (bv_unsigned y) lo) as [E|E]; [left| right; lia].
apply bv_eq. rewrite unsigned_lit by lia. lia.
Qed.

Lemma bytes_of_In : forall lo hi (y : word), 0 <= lo -> hi <= 2^64 ->
In y (bytes_of (lo, hi)) <-> lo <= bv_unsigned y < hi.
Proof.
intros lo hi y H0 Hh. unfold bytes_of. cbn [fst snd].
destruct (Z.le_gt_cases lo hi).
- rewrite zbytes_In by lia. rewrite Z2Nat.id by lia. lia.
- rewrite Z2Nat.nonpos by lia. cbn. lia.
Qed.

Lemma zeros_cover_bytes : forall ys (x : word),
zeros_cover (map (fun y : word => (y, Z_to_bv 64 1)) ys) x = existsb (bv_eqb x) ys.
Proof.
induction ys as [|y ys IH]; intros x; cbn [map zeros_cover existsb]; [reflexivity|].
fold (zeros_cover (map (fun y0 : word => (y0, Z_to_bv 64 1)) ys) x). rewrite IH. cbn [fst snd]. f_equal.
change (bv_unsigned (Z_to_bv 64 1)) with 1. unfold bv_eqb.
destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)); [rewrite e; rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia; reflexivity|].
destruct (Z.leb_spec (bv_unsigned y) (bv_unsigned x)); destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y + 1)); cbn; try reflexivity. exfalso. lia.
Qed.

Definition shoff_ok (L : lvp) : Prop := 0 <= lv_shoff L /\ lv_shoff L + 2^62 < 2^64.

Section Views.
Variable L : lvp.
Hypothesis HL : shoff_ok L.

Lemma shadow_iv_bounds : forall a n : word,
0 <= fst (shadow_iv L a n) /\ snd (shadow_iv L a n) <= 2^64.
Proof.
intros a n. unfold shadow_iv, sh_iv, shz, wiv2z. cbn [fst snd]. destruct HL as [H0 H1].
pose proof (u64_range a). pose proof (u64_range n).
split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]|].
assert ((bv_unsigned a + bv_unsigned n - 1) / 8 < 2^62) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma bytes_of_shadow : forall (a n y : word),
In y (bytes_of (shadow_iv L a n)) <-> zin (bv_unsigned y) (shadow_iv L a n) = true.
Proof.
intros a n y. pose proof (shadow_iv_bounds a n) as [B0 B1].
destruct (shadow_iv L a n) as [lo hi] eqn:E. cbn [fst snd] in *. rewrite bytes_of_In by lia. rewrite zin_true. cbn. tauto.
Qed.

Definition reveal_of (mo : Model) (M1 : word -> option byte) (a n : word) : list (word * list byte) :=
map (fun x => (x, [match M1 x with Some b => b | None => zero8 end])) (reveal L mo a n).

Lemma reveal_of_fst : forall mo M1 a n, map fst (reveal_of mo M1 a n) = reveal L mo a n.
Proof. intros. unfold reveal_of. rewrite map_map. cbn [fst]. apply map_id. Qed.

Lemma reveal_of_wunit : forall mo M1 a n, wunit (reveal_of mo M1 a n) = true.
Proof.
intros. unfold wunit, reveal_of. apply forallb_forall. intros w Hin. apply in_map_iff in Hin as (x & <- & _). reflexivity.
Qed.

Lemma reveal_In : forall mo a n x,
In x (reveal L mo a n) <-> hidden L mo x = true /\ zin (bv_unsigned x) (shadow_iv L a n) = true.
Proof. intros. unfold reveal. rewrite filter_In, bytes_of_shadow. tauto. Qed.

Lemma reveal_all : forall mo (a n : word),
0 < bv_unsigned n -> bv_unsigned a mod 8 = 0 -> bv_unsigned n mod 8 = 0 ->
(forall y, bv_unsigned a <= y < bv_unsigned a + bv_unsigned n -> appcov L mo y = false) ->
(forall z, zin z (shadow_iv L a n) = true -> appcov L mo z = false) ->
reveal L mo a n = bytes_of (shadow_iv L a n).
Proof.
intros mo a n Hn Ha8 Hn8 Hfree Hshfree. unfold reveal. apply forallb_filter_id. apply forallb_forall. intros x Hx.
apply bytes_of_shadow in Hx. pose proof Hx as Hz. apply zin_true in Hx. unfold shadow_iv, sh_iv, wiv2z in Hx. cbn [fst snd] in Hx.
destruct (proj1 (sh_iv_iff L (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (bv_unsigned x) ltac:(lia)) Hx) as (y0 & Hy0 & Hs0).
apply hidden_iff. split; [apply Hshfree; exact Hz|].
intros y Hy Hs. rewrite <- Hs0 in Hs. unfold shz in Hs.
assert (Hyy : y / 8 = y0 / 8) by lia.

assert (Hblk : bv_unsigned a <= y < bv_unsigned a + bv_unsigned n).
{ pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)).
pose proof (Z.div_mod y0 8 ltac:(lia)). pose proof (Z.mod_pos_bound y0 8 ltac:(lia)).
pose proof (Z.div_mod (bv_unsigned a) 8 ltac:(lia)). pose proof (Z.div_mod (bv_unsigned a + bv_unsigned n) 8 ltac:(lia)).
assert ((bv_unsigned a + bv_unsigned n) mod 8 = 0) by (rewrite Z.add_mod, Ha8, Hn8 by lia; reflexivity).
assert (bv_unsigned a / 8 <= y0 / 8) by (apply Z.div_le_mono; lia).
assert (y0 / 8 < (bv_unsigned a + bv_unsigned n) / 8).
{ apply Z.div_lt_upper_bound; [lia|]. lia. }
nia. }
rewrite (Hfree y Hblk) in Hy. discriminate.
Qed.

Lemma view_grant : forall mo mo2 m (a n : word),
(forall z, allowed_byte L mo2 z = allowed_byte L mo z || inR a n z || zin z (shadow_iv L a n)) ->
(forall x, In x (reveal L mo a n) -> inR a n (bv_unsigned x) = false -> m x <> None) ->
view L mo2 (apply_zeros m [(a, n)])
= apply_writes (apply_zeros (view L mo m) [(a, n)]) (reveal_of mo (apply_zeros m [(a, n)]) a n).
Proof.
intros mo mo2 m a n Hal Hsome. apply FunctionalExtensionality.functional_extensionality. intros y.
unfold reveal_of. rewrite apply_writes_bytes. cbn beta.
unfold view, mrestrict. cbn beta. rewrite !apply_zeros_1. unfold hidden. rewrite Hal.
destruct (existsb (bv_eqb y) _) eqn:Ex.
- apply existsb_bv_eqb in Ex. pose proof (proj1 (reveal_In mo a n y) Ex) as [Hh Hz]. unfold hidden in Hh. apply negb_true_iff in Hh.
rewrite Hh, Hz. cbn [negb andb orb]. rewrite orb_true_r. cbn [negb].
destruct (inR a n (bv_unsigned y)) eqn:A2; [reflexivity|].
destruct (m y) eqn:Em; [reflexivity|]. exfalso. exact (Hsome y Ex A2 Em).
- destruct (allowed_byte L mo (bv_unsigned y)) eqn:A1; cbn [negb orb andb].
+ destruct (inR a n (bv_unsigned y)); reflexivity.
+ destruct (inR a n (bv_unsigned y)) eqn:A2; cbn [negb orb]; [reflexivity|].
destruct (zin (bv_unsigned y) (shadow_iv L a n)) eqn:A3; cbn [negb]; [|reflexivity].
exfalso. lazymatch type of Ex with ?t = false => assert (Ht : t = true) end.
{ apply existsb_bv_eqb. apply reveal_In. unfold hidden. rewrite A1. auto. }
rewrite Ht in Ex. discriminate.
Qed.

Lemma view_zeros_same : forall mo mo2 m (a n : word),
(forall z, hidden L mo2 z = hidden L mo z) ->
(forall x : word, inR a n (bv_unsigned x) = true -> hidden L mo x = false) ->
view L mo2 (apply_zeros m [(a, n)]) = apply_zeros (view L mo m) [(a, n)].
Proof.
intros mo mo2 m a n Hh Hvis. apply FunctionalExtensionality.functional_extensionality. intros y.
unfold view, mrestrict. rewrite !apply_zeros_1, Hh.
destruct (inR a n (bv_unsigned y)) eqn:E; [rewrite (Hvis y E); reflexivity| reflexivity].
Qed.

Lemma view_unmap : forall mo mo2 m (a n : word),
(forall z, allowed_byte L mo2 z = true -> allowed_byte L mo z = true) ->
(forall z, allowed_byte L mo z = true -> allowed_byte L mo2 z = false -> inR a n z = true \/ zin z (shadow_iv L a n) = true) ->
view L mo2 (apply_unmaps m [(a, n)]) = apply_unmaps (view L mo m) ((a, n) :: conceal L mo2 a n).
Proof.
intros mo mo2 m a n Hsh Hlost. apply FunctionalExtensionality.functional_extensionality. intros y.
unfold view, mrestrict. rewrite !apply_unmaps_cons. unfold conceal. rewrite zeros_cover_bytes.
replace (zeros_cover [] y) with false by reflexivity. rewrite orb_false_r.
unfold hidden.
destruct (inR a n (bv_unsigned y)) eqn:HR; cbn [orb]; [destruct (allowed_byte L mo2 (bv_unsigned y)); reflexivity|].
destruct (existsb (bv_eqb y) _) eqn:Ex.
- apply existsb_bv_eqb in Ex. apply filter_In in Ex as [_ Hc]. unfold hidden in Hc. apply negb_true_iff in Hc. rewrite Hc. reflexivity.
- destruct (allowed_byte L mo2 (bv_unsigned y)) eqn:A2; cbn [negb].
+ rewrite (Hsh _ A2). reflexivity.
+ destruct (allowed_byte L mo (bv_unsigned y)) eqn:A1; cbn [negb]; [|reflexivity]. exfalso.
destruct (Hlost _ A1 A2) as [H|H]; [congruence|].
lazymatch type of Ex with ?t = false => assert (Ht : t = true) end.
{ apply existsb_bv_eqb. apply filter_In. split; [apply bytes_of_shadow; exact H|]. cbv beta. rewrite A2. reflexivity. }
rewrite Ht in Ex. discriminate.
Qed.

Lemma jsome_grant : forall mo mo2 m (a n : word),
(forall z, allowed_byte L mo2 z = allowed_byte L mo z || inR a n z || zin z (shadow_iv L a n)) ->
jsome L mo m -> jsome L mo2 (apply_zeros m [(a, n)]).
Proof.
intros mo mo2 m a n Hal HJ. eapply jsome_mono; [|exact HJ]. intros x _ Hh. unfold hidden in *. rewrite Hal in Hh.
apply negb_true_iff in Hh. apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _]. rewrite Hh. split; [reflexivity|].
intros Hm. rewrite apply_zeros_1. destruct (inR a n (bv_unsigned x)); [discriminate| exact Hm].
Qed.

Lemma jsome_zeros_same : forall mo mo2 m (a n : word),
(forall z, hidden L mo2 z = hidden L mo z) -> jsome L mo m -> jsome L mo2 (apply_zeros m [(a, n)]).
Proof.
intros mo mo2 m a n Hh HJ. eapply jsome_mono; [|exact HJ]. intros x _ Hx. rewrite Hh in Hx. split; [exact Hx|].
intros Hm. rewrite apply_zeros_1. destruct (inR a n (bv_unsigned x)); [discriminate| exact Hm].
Qed.

Lemma jsome_unmap : forall mo mo2 m (a n : word),
(forall z, allowed_byte L mo2 z = true -> allowed_byte L mo z = true) ->
(forall z, allowed_byte L mo z = true -> allowed_byte L mo2 z = false -> inR a n z = true \/ zin z (shadow_iv L a n) = true) ->
(forall x, in_bands L x = true -> inR a n (bv_unsigned x) = false) ->
sh_some L a n (view L mo m) ->
jsome L mo m -> jsome L mo2 (apply_unmaps m [(a, n)]).
Proof.
intros mo mo2 m a n Hsh Hlost Hdis Hss HJ x Hb Hh2.
rewrite apply_unmaps_cons. rewrite (Hdis x Hb). replace (zeros_cover [] x) with false by reflexivity. cbn [orb].
destruct (hidden L mo x) eqn:Hh1; [exact (HJ x Hb Hh1)|].
unfold hidden in Hh1, Hh2. apply negb_false_iff in Hh1. apply negb_true_iff in Hh2.
destruct (Hlost _ Hh1 Hh2) as [H|H]; [rewrite (Hdis x Hb) in H; discriminate|].
intros Hm. apply (Hss x); [apply bytes_of_shadow; exact H|]. unfold view, mrestrict, hidden. rewrite Hh1. exact Hm.
Qed.

End Views.

Lemma apply_writes_units_notIn : forall ws m x,
wunit ws = true -> ~ In x (map fst ws) -> apply_writes m ws x = m x.
Proof.
induction ws as [|[a bs] ws IH]; intros m x Hw Hnin; [reflexivity|].
cbn [map fst In] in Hnin. cbn [wunit forallb fst snd] in Hw. apply andb_prop in Hw as [Hl Hw].
cbn [apply_writes]. rewrite IH; [| exact Hw| intros H; apply Hnin; right; exact H].
destruct bs as [|b1 [|b2 bs2]]; try discriminate. cbn [write_to_mem].
destruct (bv_eqb x a) eqn:E; [| reflexivity]. apply bv_eqb_eq in E. exfalso. apply Hnin. left. symmetry. exact E.
Qed.

Lemma apply_writes_units_In : forall ws m x,
wunit ws = true -> In x (map fst ws) -> apply_writes m ws x <> None.
Proof.
induction ws as [|[a bs] ws IH]; intros m x Hw Hin; [destruct Hin|].
cbn [map fst In] in Hin. cbn [wunit forallb fst snd] in Hw. apply andb_prop in Hw as [Hl Hw].
cbn [apply_writes].
destruct (in_dec weq_dec x (map fst ws)) as [Hin'|Hnin]; [apply IH; assumption|].
destruct Hin as [->|Hin]; [| exfalso; exact (Hnin Hin)].
rewrite (apply_writes_units_notIn ws _ x Hw Hnin).
destruct bs as [|b1 [|b2 bs2]]; try discriminate. cbn [write_to_mem]. rewrite bv_eqb_refl. discriminate.
Qed.

Lemma halted_destroyed : forall mo a n h, m_halted (with_mmap_destroyed a n h mo) = m_halted mo.
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n h. reflexivity. Qed.

Section MmNodes.
Variable segs : list Segment.
Variable L : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base L segs.
Hypothesis HL : shoff_ok L.
Hypothesis HBe : bands_excl L.
Hypothesis HBc : bands_cover L.

#[local] Notation CINV := (cinv L (xinvA L) (jsome L)) (only parsing).

Lemma sstep_cfg_svc_invA : forall ms mo x8 evs X,
ms_svc_pending ms = Some x8 -> sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X ->
(exists eff mo' mo'', syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) /\
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) mo eff /\ m_halted mo' = None /\
materialize_model_accesses mo' (syscall_effect_accesses eff) = Some mo'' /\
X = SNext (mkCfg (nret ms eff) mo''))
\/ (exists eff mo' evs0, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = None /\
materialize_model_accesses mo' (syscall_effect_accesses eff) = None /\ evs = [] /\ X = SError)
\/ (exists eff mo' evs0 code, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_halted mo' = Some code /\
evs = evs0 ++ [ExitEv code (m_fs mo')] /\ X = SNext (mkCfg ms mo'))
\/ (syscall_spec (sys_input segs ms x8) mo Unmodeled /\ evs = [] /\ X = SError)
\/ (exists eff mo' evs0 sig, syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs0) /\ m_killed mo' = Some sig /\
evs = evs0 ++ [KillEv sig (m_fs mo')] /\ X = SNext (mkCfg ms mo')).
Proof.
intros ms mo x8 evs X Hsvc Hst. inversion Hst; subst; try congruence;
match goal with H : ms_svc_pending ms = Some ?x |- _ => rewrite Hsvc in H; inversion H; subst end.
- left. eexists _, _, _. eauto 8.
- right; left. eexists _, _, _. eauto 6.
- right; right; left. eexists _, _, _, _. eauto.
- right; right; right; right. eexists _, _, _, _. eauto.
- right; right; right; left. auto.
Qed.

Lemma mm_kit : forall ms mo x8 (chk : resp -> check_result),
ms_svc_pending ms = Some x8 -> m_halted mo = None ->
(forall eff, check_syscall (sys_input segs ms x8) eff mo = chk eff) ->
(forall eff, chk eff <> CheckUnmodeled) ->
(forall eff mo2 evs, chk eff = CheckOk mo2 evs -> eff_copyins eff = [] /\ eff_writes eff = [] /\ m_halted mo2 = None) ->
(forall evs X, sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs X -> exists eff mo2, X = SNext (mkCfg (nret ms eff) mo2) /\
chk eff = CheckOk mo2 evs /\ ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) mo eff)
/\ (forall eff mo2 evs, chk eff = CheckOk mo2 evs -> ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) mo eff ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo2))).
Proof.
intros ms mo x8 chk Hsvc Hh Hchk Hnu Hok.
assert (Hmat : forall eff mo2 evs, chk eff = CheckOk mo2 evs -> materialize_model_accesses mo2 (syscall_effect_accesses eff) = Some mo2).
{ intros eff mo2 evs Hc. destruct (Hok _ _ _ Hc) as (Hci & Hw & _). unfold syscall_effect_accesses. rewrite Hci, Hw. apply materialize_nil. }
split.
- intros evs X Hst.
destruct (sstep_cfg_svc_invA ms mo x8 evs X Hsvc Hst)
as [(eff & mo2 & mo3 & Hs & Hns & Hh2 & Hm & ->) | [(eff & mo2 & evs0 & Hs & Hh2 & Hm & -> & ->)
| [(eff & mo2 & evs0 & code & Hs & Hh2 & -> & ->) | [(Hs & -> & ->) | (eff & mo2 & evs0 & sig & Hs & Hk & -> & ->)]]]].
+ apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. rewrite (Hmat _ _ _ Hs) in Hm. injection Hm as <-. eauto.
+ exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. rewrite (Hmat _ _ _ Hs) in Hm. discriminate.
+ exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. destruct (Hok _ _ _ Hs) as (_ & _ & Hh'). congruence.
+ exfalso. apply (check_syscall_complete_unmodeled _ _ (eff0 (Z_to_bv 64 0))) in Hs. rewrite Hchk in Hs. exact (Hnu _ Hs).
+
exfalso. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs. destruct (Hok _ _ _ Hs) as (_ & _ & Hh').
rewrite m_killed_of_m_halted_none in Hk by exact Hh'. discriminate.
- intros eff mo2 evs Hc Hns. destruct (Hok _ _ _ Hc) as (_ & _ & Hh2).
unfold nret. eapply sstep_cfg_syscall; [exact Hh|exact Hsvc| | exact Hns | exact Hh2 | exact (Hmat _ _ _ Hc)].
apply check_syscall_ok_iff. rewrite Hchk. exact Hc.
Qed.

Lemma mmap_sys : forall ms addr len prot flags eff mo,
at_node segs (NMmap addr len prot flags) ms ->
check_syscall (sys_input segs ms (Z_to_bv 64 222)) eff mo
= check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 prot) (Z_to_bv 64 flags) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo.
Proof.
intros ms addr len prot flags eff mo (Hsvc & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
dispatch 222. rewrite Ha0, Ha1, Ha2, Ha3, Ha4, Ha5. reflexivity.
Qed.

Lemma munmap_sys : forall ms addr len eff mo,
at_node segs (NMunmap addr len) ms ->
check_syscall (sys_input segs ms (Z_to_bv 64 215)) eff mo = check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo.
Proof.
intros ms addr len eff mo (Hsvc & Ha0 & Ha1). dispatch 215. rewrite Ha0, Ha1. reflexivity.
Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof.
intros l1 l2 a n H. apply region_free_intro. intros b s Hin. eapply region_free_In; [exact H|]. apply in_or_app. right. exact Hin.
Qed.

Lemma xinvA_intro : forall mo mo', vm_onlyA mo mo' -> fdinv mo -> model_ivs_wf mo' -> excl_inside L mo' ->
maps_below_top (m_vmmaps mo') -> xinvA L mo'.
Proof.
intros mo mo' Hv HF W X Y. split; [| split; [exact W| split; [exact X| exact Y]]].
destruct (vm_onlyA_facts _ _ Hv) as (Hf & Hs & _ & Ht & _). eapply fdinv_frame; eassumption.
Qed.

Lemma top_grant : forall mo a n, alloc_top (m_vmmaps (grant_model mo a n)) = alloc_top (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma top_commit : forall mo a n, alloc_top (m_vmmaps (commit_model mo a n)) = alloc_top (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma top_remap : forall mo a n, alloc_top (m_vmmaps (remap_model mo a n)) = alloc_top (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma top_munmap : forall mo a n, alloc_top (m_vmmaps (munmap_model mo a n)) = alloc_top (m_vmmaps mo).
Proof. intros [fd [maps lazy mat] io fs proc lim tm] a n. reflexivity. Qed.
Lemma mbt_grant : forall mo (a n : word), maps_below_top (m_vmmaps mo) -> bv_unsigned a + bv_unsigned n <= alloc_top (m_vmmaps mo) ->
maps_below_top (m_vmmaps (grant_model mo a n)).
Proof.
intros mo a n [T H] Ha. split; [rewrite top_grant; exact T|]. rewrite top_grant, maps_grant.
intros e [<-|He]; [exact Ha| exact (H e He)].
Qed.
Lemma mbt_commit : forall mo a n, maps_below_top (m_vmmaps mo) -> maps_below_top (m_vmmaps (commit_model mo a n)).
Proof. intros mo a n [T H]. split; [rewrite top_commit; exact T|]. rewrite top_commit, maps_commit. exact H. Qed.
Lemma mbt_remap : forall mo a n, maps_below_top (m_vmmaps mo) -> maps_below_top (m_vmmaps (remap_model mo a n)).
Proof. intros mo a n [T H]. split; [rewrite top_remap; exact T|]. rewrite top_remap, maps_remap. exact H. Qed.
Lemma mbt_munmap : forall mo a n, maps_below_top (m_vmmaps mo) -> maps_below_top (m_vmmaps (munmap_model mo a n)).
Proof.
intros mo a n [T H]. split; [rewrite top_munmap; exact T|]. rewrite top_munmap, maps_munmap.
intros e He. unfold map_remove in He. apply filter_In in He as [He _]. exact (H e He).
Qed.

Lemma sh_pages_le : forall (a n : word),
bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 -> 0 < bv_unsigned n ->
4096 * Z.of_nat (length (pages_meeting (shadow_iv L a n))) <= sh_cost (bv_unsigned n).
Proof.
intros a n Ha Hn Hp. unfold sh_cost, shadow_iv, wiv2z. cbn [fst snd].
pose proof (sh_iv_len L (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) as Hl.
destruct (sh_iv L (bv_unsigned a, bv_unsigned a + bv_unsigned n)) as [lo hi] eqn:E. cbn [fst snd] in Hl.
assert (Hm8 : forall z, z mod 4096 = 0 -> z mod 8 = 0).
{ intros z Hz. destruct (mod0_multiple z Hz) as [q ->]. replace (4096 * q) with ((512 * q) * 8) by lia. apply Z_mod_mult. }
assert (H8 : (bv_unsigned a + bv_unsigned n) mod 8 = 0).
{ rewrite Z.add_mod, (Hm8 _ Ha), (Hm8 _ Hn) by lia. reflexivity. }
specialize (Hl (Hm8 _ Ha) H8 ltac:(lia)).
assert (Hlh : lo <= hi).
{ unfold sh_iv in E. injection E as <- <-. cbn [fst snd]. pose proof (shz_mono L (bv_unsigned a) (bv_unsigned a + bv_unsigned n - 1) ltac:(lia)). lia. }
pose proof (length_pages_meeting_le lo hi Hlh) as Hle. rewrite Hl in Hle.
replace (bv_unsigned a + bv_unsigned n - bv_unsigned a) with (bv_unsigned n) in Hle by lia.
rewrite Z.div_div in Hle by lia. change (8 * 4096) with 32768 in Hle. nia.
Qed.

Lemma range_pages_eq : forall (a n : word),
bv_unsigned a mod 4096 = 0 -> bv_unsigned n mod 4096 = 0 ->
4096 * Z.of_nat (length (pages_meeting (wiv2z (a, n)))) = bv_unsigned n.
Proof.
intros a n Ha Hn. unfold wiv2z. cbn [fst snd]. pose proof (u64_range n).
rewrite length_pages_meeting_aligned; [| exact Ha| rewrite Z.add_mod, Ha, Hn by lia; reflexivity| lia].
replace (bv_unsigned a + bv_unsigned n - bv_unsigned a) with (bv_unsigned n) by lia.
destruct (mod0_multiple _ Hn) as [q Hq]. rewrite Hq. replace (4096 * q) with (q * 4096) by lia. rewrite Z.div_mul by lia. lia.
Qed.

Lemma range_not_excl : forall (a n : word) y,
excl_entry L (a, n) = false -> bv_unsigned a <= y < bv_unsigned a + bv_unsigned n -> in_zivs y (lv_excl L) = false.
Proof.
intros a n y He Hy. pose proof (proj1 (excl_entry_false L (a, n)) He) as H. cbn [fst snd] in H.
destruct (in_zivs y (lv_excl L)) eqn:E; [|reflexivity]. exfalso. apply in_zivs_true in E as (x & Hx & Hyx).
destruct (H x Hx ltac:(lia) ltac:(lia)); lia.
Qed.

Lemma reveal_in_bands : forall mo (a n x : word),
0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= lv_ceiling -> excl_entry L (a, n) = false ->
In x (reveal L mo a n) -> in_bands L x = true.
Proof.
intros mo a n x Hn Hce He Hin. apply (reveal_In L HL) in Hin as [_ Hz]. apply zin_true in Hz.
unfold shadow_iv, sh_iv, wiv2z in Hz. cbn [fst snd] in Hz. pose proof (u64_range a). pose proof (u64_range n).
destruct (proj1 (sh_iv_iff L (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (bv_unsigned x) ltac:(lia)) Hz) as (y & Hy & Hs).
unfold in_bands. rewrite <- Hs. apply HBc; [lia|]. eapply range_not_excl; [exact He| exact Hy].
Qed.

Lemma bands_avoid_range : forall (a n x : word),
excl_entry L (a, n) = false -> in_bands L x = true -> inR a n (bv_unsigned x) = false.
Proof.
intros a n x He Hb. unfold in_bands in Hb. apply in_zivs_true in Hb as (b & Hb & Hxb).
destruct (HBe b Hb) as (e & He' & H1 & H2).
pose proof (proj1 (excl_entry_false L (a, n)) He e He' ltac:(lia)) as H. cbn [fst snd] in H.
unfold inR. apply in_rng_false. pose proof (u64_range n). destruct (Z.le_gt_cases (bv_unsigned n) 0); [lia|]. destruct (H ltac:(lia)); lia.
Qed.

Definition W0 (ms : machine_state) (mo : Model) (a n : word) : list (word * list byte) :=
reveal_of L mo (apply_zeros (ms_mem ms) [(a, n)]) a n.

Lemma W0_fst : forall ms mo a n, map fst (W0 ms mo a n) = reveal L mo a n.
Proof. intros. apply reveal_of_fst. Qed.
Lemma W0_wunit : forall ms mo a n, wunit (W0 ms mo a n) = true.
Proof. intros. apply reveal_of_wunit. Qed.

Lemma grant_core : forall ms mo (a : word) (lenZ : Z),
0 < lenZ -> lenZ <= 2^40 ->
CINV ms mo -> m_halted mo = None ->
bv_unsigned a mod 4096 = 0 -> bv_unsigned a + rlen lenZ <= alloc_top (m_vmmaps mo) ->
region_free (vm_maps (m_vmmaps mo)) a (rlenw lenZ) = true -> excl_entry L (a, rlenw lenZ) = false ->
Phi L mo + 2 * rlen lenZ + 4096 * Z.of_nat (length (pages_meeting (shadow_iv L a (rlenw lenZ)))) <= vm_limit (m_vmmaps mo) ->
msview L (grant_model mo a (rlenw lenZ)) (nret ms (mkEffectU a [] [(a, rlenw lenZ)] [] [] []))
= nret (msview L mo ms) (rsp_grant a (rlenw lenZ) (W0 ms mo a (rlenw lenZ)))
/\ CINV (nret ms (mkEffectU a [] [(a, rlenw lenZ)] [] [] [])) (grant_model mo a (rlenw lenZ))
/\ m_halted (grant_model mo a (rlenw lenZ)) = None
/\ vm_backing_used mo + rlen lenZ <= vm_limit (m_vmmaps mo).
Proof.
intros ms mo a lenZ Hl1 Hl2 ([HF [W [X Y]]] & HI & HJ) Hh Hal Hce0 Hfree Hex Hbud. set (n := rlenw lenZ) in *. unfold W0.
pose proof (rlen_facts lenZ Hl1 Hl2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7). fold n in R6.
assert (Hn : 0 < bv_unsigned n) by (rewrite R6; lia).
assert (Hce : bv_unsigned a + rlen lenZ <= lv_ceiling) by (pose proof (proj1 Y) as T; unfold grant_ceilA, lv_ceiling in *; lia).
assert (Hb : bv_unsigned a + bv_unsigned n <= 2^64) by (rewrite R6; unfold lv_ceiling, sp_window_hi, stack_max_size in Hce; lia).
assert (Hgrow : forall z, allowed_byte L (grant_model mo a n) z = allowed_byte L mo z || inR a n z || zin z (shadow_iv L a n)).
{ apply allowed_grow; [| exact Hn]. intros y. apply appcov_grant. exact Hex. }
split; [|split; [|split]].
- unfold rsp_grant. apply msview_nret_intro. cbn [apply_unmaps apply_writes]. apply view_grant; [exact HL| exact Hgrow|].
intros x Hin _. apply (HJ x); [| exact (proj1 (proj1 (reveal_In L HL mo a n x) Hin))].
apply (reveal_in_bands mo a n x Hn); [rewrite R6; exact Hce| exact Hex| exact Hin].
- split; [| split].
+ eapply xinvA_intro; [apply vm_onlyA_grant| exact HF| apply wf_grant; [exact W| exact Hb]| apply excl_inside_grant; [exact X| exact Hex]|].
apply mbt_grant; [exact Y| rewrite R6; exact Hce0].
+ unfold lv_inv. rewrite limit_grant.
pose proof (Phi_grant L mo a n W Hex Hn Hb) as HP. rewrite length_app, Nat2Z.inj_add in HP.
pose proof (range_pages_eq a n Hal ltac:(rewrite R6; exact R3)) as HR. unfold shadow_iv in Hbud. rewrite R6 in *. lia.
+ rewrite nret_mem. cbn [apply_unmaps apply_writes]. eapply jsome_grant; [exact Hgrow| exact HJ].
- destruct (vm_onlyA_facts _ _ (vm_onlyA_grant mo a n)) as (_ & _ & -> & _). exact Hh.
- unfold lv_inv in HI. pose proof (Rsv_nonneg L mo). unfold Phi in *. lia.
Qed.

Section AnonNode.
Variables (ms : machine_state) (mo : Model) (len : Z).
Hypothesis Hat : at_node segs (NMmap 0 len PROT_RW FL_ANON) ms.
Hypothesis Hh : m_halted mo = None.
Hypothesis HC : CINV ms mo.
Hypothesis Hns : 0 < len /\ len <= 2^40 /\ excl_mapped L mo /\ Phi L mo + cost_anon len <= vm_limit (m_vmmaps mo)
/\ vm_gap_available (m_vmmaps mo) (rlen len) = true.
#[local] Notation n := (rlenw len).
#[local] Notation CHK eff mo := (check_mmap (Z_to_bv 64 0) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 FL_ANON) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).
#[local] Notation NODE := (NMmap 0 len PROT_RW FL_ANON).
#[local] Notation EFF r := (mkEffectU r [] [(r, n)] [] [] []).
#[local] Notation STEP := (sstep_cfg segs (alloc_only_cfg false)).
#[local] Notation SPUR eff := (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (Z_to_bv 64 222)) mo eff).

Lemma anon_budget : vm_backing_used mo + rlen len <= vm_limit (m_vmmaps mo).
Proof.
destruct Hns as (Hl1 & Hl2 & _ & Hbud & _). pose proof (Rsv_nonneg L mo) as HR.
pose proof (rlen_facts len Hl1 Hl2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
assert (Hsh : 0 <= sh_cost (rlen len)) by (unfold sh_cost; pose proof (Z.div_pos (rlen len) 32768 ltac:(lia) ltac:(lia)); lia).
unfold cost_anon in Hbud. unfold Phi in Hbud. lia.
Qed.

Lemma anon_place : exists r, anon_place_ok mo r (rlen len) = true.
Proof.
destruct Hns as (Hl1 & Hl2 & _ & _ & Hg). apply vm_gap_available_find in Hg as (r & Hr).
apply vm_find_base_sound in Hr as (A1 & A2 & A3 & A4). exists r.
unfold anon_place_ok. rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3). cbn [andb].
unfold rlenw in A4 |- *. exact A4.
Qed.

Lemma anon_ret_ok : forall eff, ~ SPUR eff -> errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
intros eff Hsp. destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:E; [|reflexivity]. exfalso. apply Hsp.
destruct anon_place as (r & Hp). destruct Hns as (Hl1 & Hl2 & _).
apply (sp_mmap_of_ok _ mo eff (EFF r) (grant_model mo r n) []); [reflexivity| exact E| |].
- rewrite (mmap_sys ms 0 len PROT_RW FL_ANON (EFF r) mo Hat). apply check_anon_grant; [lia| exact Hp| exact anon_budget].
- cbn [eff_ret]. eapply (anon_place_not_errno len); [lia| exact Hp].
Qed.

Lemma anon_kit :
(forall evs X, STEP (mkCfg ms mo) evs X -> exists eff mo2, X = SNext (mkCfg (nret ms eff) mo2) /\ CHK eff mo = CheckOk mo2 evs /\ ~ SPUR eff)
/\ (forall eff mo2 evs, CHK eff mo = CheckOk mo2 evs -> ~ SPUR eff -> STEP (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo2))).
Proof.
destruct Hns as (Hl1 & Hl2 & _).
apply (mm_kit ms mo (Z_to_bv 64 222)); [exact (proj1 Hat)| exact Hh| | |].
- intros eff. apply mmap_sys. exact Hat.
- intros eff. apply check_anon_nu. lia.
- intros eff mo2 evs Hc. destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:He.
+ rewrite (check_anon_red len ltac:(lia)) in Hc.
destruct eff as [r ws zs us cs ci]. cbn [eff_ret] in He. destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite He in Hc. destruct zs; [|discriminate]. cbv iota in Hc. injection Hc as <- <-. cbn [eff_copyins eff_writes]. auto.
+ apply check_anon_ok in Hc as (-> & r & -> & _ & ->); [| lia| exact He].
cbn [eff_copyins eff_writes]. split; [reflexivity|]. split; [reflexivity|].
destruct (vm_onlyA_facts _ _ (vm_onlyA_grant mo r n)) as (_ & _ & -> & _). exact Hh.
Qed.

Lemma anon_grant : forall r, anon_place_ok mo r (rlen len) = true ->
msview L (grant_model mo r n) (nret ms (EFF r)) = nret (msview L mo ms) (rsp_grant r n (W0 ms mo r n))
/\ CINV (nret ms (EFF r)) (grant_model mo r n) /\ m_halted (grant_model mo r n) = None
/\ vm_backing_used mo + rlen len <= vm_limit (m_vmmaps mo).
Proof.
intros r Hp. destruct Hns as (Hl1 & Hl2 & Hem & Hbud & _).
pose proof (rlen_facts len Hl1 Hl2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
pose proof Hp as Hp0. unfold anon_place_ok in Hp. apply andb_prop in Hp as [Hp Hfree].
apply andb_prop in Hp as [Hp Hce]. apply andb_prop in Hp as [Hal Hpos].
apply Z.eqb_eq in Hal. apply Z.leb_le in Hce. unfold page_size in Hal.
pose proof (region_free_app_r _ _ _ _ Hfree) as Hfree2. fold (rlenw len) in Hfree2.
assert (Hex : excl_entry L (r, n) = false) by (apply (fresh_not_excl L mo); [exact Hem| rewrite R6; lia| exact Hfree2]).
apply (grant_core ms mo r len Hl1 Hl2 HC Hh Hal Hce Hfree2 Hex).
unfold cost_anon in Hbud. pose proof (sh_pages_le r n Hal ltac:(rewrite R6; exact R3) ltac:(rewrite R6; lia)) as Hsh. rewrite R6 in Hsh. lia.
Qed.

Lemma anon_complete : forall evs X, STEP (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L NODE mo rsp mo' evs /\ CINV ms' mo' /\ m_halted mo' = None.
Proof.
intros evs X Hst. destruct Hns as (Hl1 & Hl2 & _).
destruct (proj1 anon_kit evs X Hst) as (eff & mo2 & -> & Hc & Hsp).
apply check_anon_ok in Hc as (-> & r & -> & Hp & ->); [| lia| exact (anon_ret_ok eff Hsp)].
destruct (anon_grant r Hp) as (Hv & HC2 & Hh2 & _).
eexists (rsp_grant r n (W0 ms mo r n)), _, (grant_model mo r n). split; [reflexivity|]. split; [exact Hv|].
split; [| auto]. cbn -[rlen rlenw grant_model W0 anon_place_ok reveal wunit rsp_grant rsp_err]. split; [reflexivity|].
exists r, (W0 ms mo r n). split; [exact Hp|]. split; [apply W0_fst|]. split; [apply W0_wunit|]. split; reflexivity.
Qed.

Lemma anon_sound : forall rsp mo' evs, nstep_raw L NODE mo rsp mo' evs ->
exists ms' mo2 rsp2, STEP (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L NODE mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA NODE rsp rsp2 /\ m_halted mo2 = None.
Proof.
intros rsp mo' evs Hr. destruct Hns as (Hl1 & Hl2 & _).
cbn -[rlen rlenw grant_model anon_place_ok reveal wunit rsp_grant] in Hr. destruct Hr as [-> Hr].
destruct Hr as (r & ws & Hp & Hfst & Hws & -> & ->).
destruct (anon_grant r Hp) as (Hv & HC2 & Hh2 & Hbk).
exists (nret ms (EFF r)), (grant_model mo r n), (rsp_grant r n (W0 ms mo r n)). split.
{ apply (proj2 anon_kit); [apply check_anon_grant; [lia| exact Hp| exact Hbk]|].
apply ns_mmap_ret; [reflexivity| cbn [eff_ret]; eapply (anon_place_not_errno len); [lia| exact Hp]]. }
split; [exact Hv|]. split.
{ cbn -[rlen rlenw grant_model W0 anon_place_ok reveal wunit rsp_grant rsp_err]. split; [reflexivity|]. exists r, (W0 ms mo r n).
split; [exact Hp|]. split; [apply W0_fst|]. split; [apply W0_wunit|]. split; reflexivity. }
split; [apply msim_refl|]. split; [| exact Hh2].
right. cbn. rewrite W0_fst, Hfst. repeat split; try reflexivity; try assumption. apply W0_wunit.
Qed.

Lemma anon_progress : exists rsp mo' evs, nstep_raw L NODE mo rsp mo' evs.
Proof.
destruct Hns as (Hl1 & Hl2 & _ & _ & Hg). apply vm_gap_available_find in Hg as (r & Hr).
apply vm_find_base_sound in Hr as (A1 & A2 & A3 & A4).
set (ws := map (fun x => (x, [zero8])) (reveal L mo r n)).
exists (rsp_grant r n ws), (grant_model mo r n), []. cbn -[rlen rlenw grant_model anon_place_ok reveal wunit rsp_grant].
split; [reflexivity|]. exists r, ws. split.
- unfold anon_place_ok. rewrite (proj2 (Z.eqb_eq _ _) A1), (proj2 (Z.ltb_lt _ _) A2), (proj2 (Z.leb_le _ _) A3). cbn [andb].
unfold rlenw in A4 |- *. exact A4.
- split; [unfold ws; rewrite map_map; cbn; apply map_id|]. split; [|split; reflexivity].
unfold ws, wunit. apply forallb_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & _). reflexivity.
Qed.

End AnonNode.

Section FixedNode.
Variables (ms : machine_state) (mo : Model) (addr len : Z).
Hypothesis Hat : at_node segs (NMmap addr len PROT_RW FL_FIXED) ms.
Hypothesis Hh : m_halted mo = None.
Hypothesis HC : CINV ms mo.
#[local] Notation a := (Z_to_bv 64 addr).
#[local] Notation n := (rlenw len).
Hypothesis Hns : fixed_gates addr len /\ fixed_top mo addr len /\
((fixed_contained mo a n = true /\ range_vis L mo a n /\ Phi L mo + cost_commit mo addr len <= vm_limit (m_vmmaps mo))
\/ (fixed_contained mo a n = false /\ fixed_free mo a n = true /\ excl_entry L (a, n) = false /\
Phi L mo + cost_fixed L addr len <= vm_limit (m_vmmaps mo))).
#[local] Notation CHK eff mo := (check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 FL_FIXED) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).
#[local] Notation NODE := (NMmap addr len PROT_RW FL_FIXED).
#[local] Notation EFF := (mkEffectU a [] [(a, n)] [] [] []).
#[local] Notation STEP := (sstep_cfg segs (alloc_only_cfg false)).
#[local] Notation SPUR eff := (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (Z_to_bv 64 222)) mo eff).

Let Hg : fixed_gates addr len := proj1 Hns.
Let Htop : addr + rlen len <= alloc_top (m_vmmaps mo) := proj1 (proj2 Hns).
Let Hfl : FL_FIXED = FL_FIXED \/ FL_FIXED = FL_FIXED_NR := or_introl eq_refl.

Lemma fixed_cf : fixed_contained mo a n = true \/ fixed_free mo a n = true.
Proof. destruct (proj2 (proj2 Hns)) as [(Hc & _)|(_ & Hf & _)]; [left; exact Hc| right; exact Hf]. Qed.

Lemma fixed_commit : fixed_contained mo a n = true -> range_vis L mo a n -> Phi L mo + cost_commit mo addr len <= vm_limit (m_vmmaps mo) ->
msview L (commit_model mo a n) (nret ms EFF) = nret (msview L mo ms) (rsp_grant a n [])
/\ CINV (nret ms EFF) (commit_model mo a n) /\ m_halted (commit_model mo a n) = None
/\ mmap_fixed_rw_budget_ok (Z_to_bv 64 FL_FIXED) mo a n = true.
Proof.
intros Hc Hvis Hbud. destruct HC as ([HF [W [X Y]]] & HI & HJ). pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
pose proof (Phi_commit L mo a n W) as HP. unfold cost_commit in Hbud. rewrite Ua, Un in HP.
assert (Hhid : forall z, hidden L (commit_model mo a n) z = hidden L mo z) by (intros z; apply (hidden_maps L mo); apply maps_commit).
split; [|split; [|split]].
- unfold rsp_grant. apply msview_nret_intro. cbn [apply_unmaps apply_writes].
apply view_zeros_same; [exact Hhid|]. intros x Hx. apply Hvis. unfold inR in Hx. apply in_rng_true in Hx. exact Hx.
- split; [| split].
+ eapply xinvA_intro; [apply vm_onlyA_commit| exact HF| apply wf_commit; exact W| apply excl_inside_commit; assumption| apply mbt_commit; exact Y].
+ unfold lv_inv in *. rewrite limit_commit. lia.
+ rewrite nret_mem. cbn [apply_unmaps apply_writes]. eapply jsome_zeros_same; [exact Hhid| exact HJ].
- destruct (vm_onlyA_facts _ _ (vm_onlyA_commit mo a n)) as (_ & _ & -> & _). exact Hh.
- unfold mmap_fixed_rw_budget_ok. fold (repl addr len FL_FIXED mo). rewrite (repl_fixed addr len FL_FIXED eq_refl).
unfold vm_backing_within_limit. apply Z.leb_le. rewrite limit_commit.
unfold lv_inv in HI. pose proof (Rsv_nonneg L (commit_model mo a n)). unfold Phi in *. lia.
Qed.

Lemma fixed_fresh : fixed_contained mo a n = false -> fixed_free mo a n = true -> excl_entry L (a, n) = false ->
Phi L mo + cost_fixed L addr len <= vm_limit (m_vmmaps mo) ->
msview L (grant_model mo a n) (nret ms EFF) = nret (msview L mo ms) (rsp_grant a n (W0 ms mo a n))
/\ CINV (nret ms EFF) (grant_model mo a n) /\ m_halted (grant_model mo a n) = None
/\ vm_backing_used mo + rlen len <= vm_limit (m_vmmaps mo).
Proof.
intros Hc Hf Hex Hbud. pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
apply (grant_core ms mo a len G1 G2 HC Hh); [rewrite Ua; exact G4| rewrite Ua; exact Htop| | exact Hex|].
- unfold fixed_free in Hf. exact (region_free_app_r _ _ _ _ Hf).
- unfold cost_fixed, sh_cost_at in Hbud. unfold shadow_iv, wiv2z. cbn [fst snd]. rewrite Ua, Un. lia.
Qed.

Lemma fixed_a_not_errno : errno_ret_in mmap_errnos a = false.
Proof.
pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
apply (placed_not_errno0 a (rlen len)); [lia| rewrite Ua; exact (below_top_room _ _ Htop)].
Qed.

Lemma fixed_grant_ok : exists mo2, CHK EFF mo = CheckOk mo2 [].
Proof.
destruct (proj2 (proj2 Hns)) as [(Hc & Hvis & Hbud)|(Hc & Hf & Hex & Hbud)].
- exists (repl addr len FL_FIXED mo). apply (check_fixed_repl addr len FL_FIXED Hg Hfl); [exact Htop| exact Hc|].
exact (proj2 (proj2 (proj2 (fixed_commit Hc Hvis Hbud)))).
- exists (fresh addr len FL_FIXED mo). apply (check_fixed_fresh addr len FL_FIXED Hg Hfl); [exact Htop| exact Hc| exact Hf|].
pose proof (proj2 (proj2 (proj2 (fixed_fresh Hc Hf Hex Hbud)))) as Hbk.
unfold mmap_noreserve_backed_ok. rewrite noreserve_fixed. apply Z.leb_le. exact Hbk.
Qed.

Lemma fixed_ret_ok : forall eff, ~ SPUR eff -> errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
intros eff Hsp. destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:E; [|reflexivity]. exfalso. apply Hsp.
destruct fixed_grant_ok as (mo2 & Hck).
apply (sp_mmap_of_ok _ mo eff EFF mo2 []); [reflexivity| exact E| |].
- rewrite (mmap_sys ms addr len PROT_RW FL_FIXED EFF mo Hat). exact Hck.
- exact fixed_a_not_errno.
Qed.

Lemma fixed_ok : forall eff mo2 evs, errno_ret_in mmap_errnos (eff_ret eff) = false -> CHK eff mo = CheckOk mo2 evs ->
evs = [] /\ eff = EFF /\
((fixed_contained mo a n = true /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 FL_FIXED) mo a n = true /\ mo2 = commit_model mo a n)
\/ (fixed_contained mo a n = false /\ fixed_free mo a n = true /\ mo2 = grant_model mo a n)).
Proof.
intros eff mo2 evs He Hck.
apply (check_fixed_ok addr len FL_FIXED Hg Hfl eff mo mo2 evs Htop He fixed_cf) in Hck as (-> & -> & Hcase).
split; [reflexivity|]. split; [reflexivity|].
rewrite (repl_fixed addr len FL_FIXED eq_refl), (fresh_fixed addr len FL_FIXED eq_refl) in Hcase. exact Hcase.
Qed.

Lemma fixed_kit :
(forall evs X, STEP (mkCfg ms mo) evs X -> exists eff mo2, X = SNext (mkCfg (nret ms eff) mo2) /\ CHK eff mo = CheckOk mo2 evs /\ ~ SPUR eff)
/\ (forall eff mo2 evs, CHK eff mo = CheckOk mo2 evs -> ~ SPUR eff -> STEP (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo2))).
Proof.
apply (mm_kit ms mo (Z_to_bv 64 222)); [exact (proj1 Hat)| exact Hh| | |].
- intros eff. apply mmap_sys. exact Hat.
- intros eff. apply (check_fixed_nu addr len FL_FIXED Hg Hfl eff mo Htop). apply fixed_cf.
- intros eff mo2 evs Hc. destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:He.
+ rewrite (check_fixed_red addr len FL_FIXED Hg Hfl eff mo Htop) in Hc.
destruct eff as [r ws zs us cs ci]. cbn [eff_ret] in He. cbn [eff_copyins eff_writes].
pose proof fixed_cf as Hcf. destruct (fixed_contained mo a n) eqn:Hc1.
* destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite He in Hc. destruct zs; [|discriminate]. split; [reflexivity|]. split; [reflexivity|].
destruct us as [|u us]; [cbv iota in Hc; injection Hc as <- _; exact Hh|].
cbv iota in Hc. destruct (listNN_eqb (u :: us) [(a, n)]); [|discriminate]. injection Hc as <- _. rewrite halted_destroyed. exact Hh.
* destruct Hcf as [Hc2|Hf1]; [discriminate|]. rewrite Hf1 in Hc.
destruct ws; [|discriminate]. destruct us; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite He in Hc. destruct zs; [|discriminate]. cbv iota in Hc. injection Hc as <- _. auto.
+ apply fixed_ok in Hc as (-> & -> & Hcase); [| exact He].
cbn [eff_copyins eff_writes]. split; [reflexivity|]. split; [reflexivity|].
destruct Hcase as [(_ & _ & ->)|(_ & _ & ->)].
* destruct (vm_onlyA_facts _ _ (vm_onlyA_commit mo a n)) as (_ & _ & -> & _). exact Hh.
* destruct (vm_onlyA_facts _ _ (vm_onlyA_grant mo a n)) as (_ & _ & -> & _). exact Hh.
Qed.

Lemma fixed_complete : forall evs X, STEP (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L NODE mo rsp mo' evs /\ CINV ms' mo' /\ m_halted mo' = None.
Proof.
intros evs X Hst.
destruct (proj1 fixed_kit evs X Hst) as (eff & mo2 & -> & Hck & Hsp).
apply fixed_ok in Hck as (-> & -> & Hcase); [| exact (fixed_ret_ok eff Hsp)].
destruct Hcase as [(Hc & Hb & ->)|(Hc & Hf & ->)].
- destruct (proj2 (proj2 Hns)) as [(_ & Hvis & Hbud)|(Hc' & _)]; [| rewrite Hc in Hc'; discriminate].
destruct (fixed_commit Hc Hvis Hbud) as (Hv & HC2 & Hh2 & _).
eexists (rsp_grant a n []), _, (commit_model mo a n). split; [reflexivity|]. split; [exact Hv|].
split; [| auto]. cbn -[fixed_contained fixed_free rlenw rsp_err commit_model grant_model reveal wunit rsp_grant]. rewrite Hc.
split; [reflexivity|]. split; reflexivity.
- destruct (proj2 (proj2 Hns)) as [(Hc' & _)|(_ & _ & Hex & Hbud)]; [rewrite Hc in Hc'; discriminate|].
destruct (fixed_fresh Hc Hf Hex Hbud) as (Hv & HC2 & Hh2 & _).
eexists (rsp_grant a n (W0 ms mo a n)), _, (grant_model mo a n). split; [reflexivity|]. split; [exact Hv|].
split; [| auto]. cbn -[fixed_contained fixed_free rlenw rsp_err commit_model grant_model reveal wunit rsp_grant W0]. rewrite Hc, Hf.
split; [reflexivity|]. exists (W0 ms mo a n). split; [apply W0_fst|]. split; [apply W0_wunit|]. split; reflexivity.
Qed.

Lemma fixed_sound : forall rsp mo' evs, nstep_raw L NODE mo rsp mo' evs ->
exists ms' mo2 rsp2, STEP (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L NODE mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA NODE rsp rsp2 /\ m_halted mo2 = None.
Proof.
intros rsp mo' evs Hr.
cbn -[fixed_contained fixed_free rlenw rsp_err commit_model grant_model reveal wunit rsp_grant] in Hr. destruct Hr as [-> Hr].
destruct (fixed_contained mo a n) eqn:Hc in Hr.
- destruct Hr as (-> & ->).
destruct (proj2 (proj2 Hns)) as [(_ & Hvis & Hbud)|(Hc' & _)]; [| rewrite Hc in Hc'; discriminate].
destruct (fixed_commit Hc Hvis Hbud) as (Hv & HC2 & Hh2 & Hb).
exists (nret ms EFF), (commit_model mo a n), (rsp_grant a n []). split.
{ rewrite <- (repl_fixed addr len FL_FIXED eq_refl mo). apply (proj2 fixed_kit); [apply (check_fixed_repl addr len FL_FIXED Hg Hfl); assumption|].
apply ns_mmap_ret; [reflexivity| exact fixed_a_not_errno]. }
split; [exact Hv|]. split.
{ cbn -[fixed_contained fixed_free rlenw rsp_err commit_model grant_model reveal wunit rsp_grant]. rewrite Hc.
split; [reflexivity|]. split; reflexivity. }
split; [apply msim_refl|]. split; [apply rvarA_refl| exact Hh2].
- destruct (proj2 (proj2 Hns)) as [(Hc' & _)|(_ & Hf & Hex & Hbud)]; [rewrite Hc in Hc'; discriminate|]. rewrite Hf in Hr.
destruct Hr as (ws & Hfst & Hws & -> & ->).
destruct (fixed_fresh Hc Hf Hex Hbud) as (Hv & HC2 & Hh2 & Hbk).
exists (nret ms EFF), (grant_model mo a n), (rsp_grant a n (W0 ms mo a n)). split.
{ rewrite <- (fresh_fixed addr len FL_FIXED eq_refl mo). apply (proj2 fixed_kit).
+ apply (check_fixed_fresh addr len FL_FIXED Hg Hfl); [exact Htop| exact Hc| exact Hf|].
unfold mmap_noreserve_backed_ok. rewrite noreserve_fixed. apply Z.leb_le. exact Hbk.
+ apply ns_mmap_ret; [reflexivity| exact fixed_a_not_errno]. }
split; [exact Hv|]. split.
{ cbn -[fixed_contained fixed_free rlenw rsp_err commit_model grant_model reveal wunit rsp_grant W0]. rewrite Hc, Hf.
split; [reflexivity|]. exists (W0 ms mo a n). split; [apply W0_fst|]. split; [apply W0_wunit|]. split; reflexivity. }
split; [apply msim_refl|]. split; [| exact Hh2]. right. cbn. rewrite W0_fst, Hfst. repeat split; try reflexivity; try assumption. apply W0_wunit.
Qed.

Lemma fixed_progress : exists rsp mo' evs, nstep_raw L NODE mo rsp mo' evs.
Proof.
cbn -[fixed_contained fixed_free rlenw rsp_err commit_model grant_model reveal wunit rsp_grant].
destruct (proj2 (proj2 Hns)) as [(Hc & _)|(Hc & Hf & _)].
- exists (rsp_grant a n []), (commit_model mo a n), []. rewrite Hc. split; [reflexivity|]. split; reflexivity.
- set (ws := map (fun x => (x, [zero8])) (reveal L mo a n)).
exists (rsp_grant a n ws), (grant_model mo a n), []. rewrite Hc, Hf. split; [reflexivity|].
exists ws. split; [unfold ws; rewrite map_map; cbn; apply map_id|]. split; [|split; reflexivity].
unfold ws, wunit. apply forallb_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & _). reflexivity.
Qed.

End FixedNode.

Section RemapNode.
Variables (ms : machine_state) (mo : Model) (addr len : Z).
Hypothesis Hat : at_node segs (NMmap addr len PROT_RW FL_FIXED_NR) ms.
Hypothesis Hh : m_halted mo = None.
Hypothesis HC : CINV ms mo.
#[local] Notation a := (Z_to_bv 64 addr).
#[local] Notation n := (rlenw len).
Hypothesis Hns : fixed_gates addr len /\ fixed_top mo addr len /\ fixed_contained mo a n = true /\ range_vis L mo a n.
#[local] Notation CHK eff mo := (check_mmap (Z_to_bv 64 addr) (Z_to_bv 64 len) (Z_to_bv 64 PROT_RW) (Z_to_bv 64 FL_FIXED_NR) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo).
#[local] Notation NODE := (NMmap addr len PROT_RW FL_FIXED_NR).
#[local] Notation EFF := (mkEffectU a [] [(a, n)] [] [] []).
#[local] Notation STEP := (sstep_cfg segs (alloc_only_cfg false)).
#[local] Notation SPUR eff := (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (Z_to_bv 64 222)) mo eff).

Let Hg : fixed_gates addr len := proj1 Hns.
Let Htop : addr + rlen len <= alloc_top (m_vmmaps mo) := proj1 (proj2 Hns).
Let Hc : fixed_contained mo a n = true := proj1 (proj2 (proj2 Hns)).
Let Hfl : FL_FIXED_NR = FL_FIXED \/ FL_FIXED_NR = FL_FIXED_NR := or_intror eq_refl.

Lemma remap_success :
msview L (remap_model mo a n) (nret ms EFF) = nret (msview L mo ms) (rsp_remap a n)
/\ CINV (nret ms EFF) (remap_model mo a n) /\ m_halted (remap_model mo a n) = None
/\ mmap_fixed_rw_budget_ok (Z_to_bv 64 FL_FIXED_NR) mo a n = true.
Proof.
destruct HC as ([HF [W [X Y]]] & HI & HJ). pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
pose proof (proj2 (proj2 (proj2 Hns))) as Hvis.
assert (Hal : bv_unsigned a mod page_size = 0) by (rewrite Ua; unfold page_size; exact G4).
assert (Hnl : bv_unsigned n mod page_size = 0) by (rewrite Un; unfold page_size; exact Rm).
assert (Hpos : 0 < bv_unsigned n) by (rewrite Un; exact Rp).
assert (Hb : bv_unsigned a + bv_unsigned n <= 2^64) by (rewrite Ua, Un; unfold grant_ceilA, sp_window_hi, stack_max_size in G5; lia).
pose proof (Phi_remap L mo a n W Hal Hnl Hpos Hb) as HP.
assert (Hhid : forall z, hidden L (remap_model mo a n) z = hidden L mo z) by (intros z; apply (hidden_maps L mo); apply maps_remap).
split; [|split; [|split]].
- unfold rsp_remap. apply msview_nret_intro. cbn [apply_unmaps apply_writes].
apply view_zeros_same; [exact Hhid|]. intros x Hx. apply Hvis. unfold inR in Hx. apply in_rng_true in Hx. exact Hx.
- split; [| split].
+ eapply xinvA_intro; [apply vm_onlyA_remap| exact HF| apply wf_remap; [exact W| exact Hb]| apply excl_inside_remap; assumption| apply mbt_remap; exact Y].
+ unfold lv_inv in *. rewrite limit_remap. lia.
+ rewrite nret_mem. cbn [apply_unmaps apply_writes]. eapply jsome_zeros_same; [exact Hhid| exact HJ].
- destruct (vm_onlyA_facts _ _ (vm_onlyA_remap mo a n)) as (_ & _ & -> & _). exact Hh.
- unfold mmap_fixed_rw_budget_ok. fold (repl addr len FL_FIXED_NR mo). rewrite (repl_fixed_nr addr len FL_FIXED_NR eq_refl).
unfold vm_backing_within_limit. apply Z.leb_le. rewrite limit_remap.
pose proof (backing_remap mo a n W Hal Hnl Hpos Hb) as Hbk.
pose proof (filter_length_le (page_outside_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) (m_vm_materialized mo)) as Hfl'.
rewrite (mat_remap mo a n) in Hbk.
unfold lv_inv in HI. pose proof (Rsv_nonneg L mo). unfold Phi in *. lia.
Qed.

Lemma remap_a_not_errno : errno_ret_in mmap_errnos a = false.
Proof.
pose proof (fixed_facts addr len Hg) as (G1 & G2 & G3 & G4 & G5 & Ua & Un & A64 & PR & Rm & Rp).
apply (placed_not_errno0 a (rlen len)); [lia| rewrite Ua; exact (below_top_room _ _ Htop)].
Qed.

Lemma remap_ret_ok : forall eff, ~ SPUR eff -> errno_ret_in mmap_errnos (eff_ret eff) = false.
Proof.
intros eff Hsp. destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:E; [|reflexivity]. exfalso. apply Hsp.
apply (sp_mmap_of_ok _ mo eff EFF (repl addr len FL_FIXED_NR mo) []); [reflexivity| exact E| |].
- rewrite (mmap_sys ms addr len PROT_RW FL_FIXED_NR EFF mo Hat).
apply (check_fixed_repl addr len FL_FIXED_NR Hg Hfl); [exact Htop| exact Hc| exact (proj2 (proj2 (proj2 remap_success)))].
- exact remap_a_not_errno.
Qed.

Lemma remap_ok : forall eff mo2 evs, errno_ret_in mmap_errnos (eff_ret eff) = false -> CHK eff mo = CheckOk mo2 evs ->
evs = [] /\ eff = EFF /\ mmap_fixed_rw_budget_ok (Z_to_bv 64 FL_FIXED_NR) mo a n = true /\ mo2 = remap_model mo a n.
Proof.
intros eff mo2 evs He Hck.
apply (check_fixed_ok addr len FL_FIXED_NR Hg Hfl eff mo mo2 evs Htop He (or_introl Hc)) in Hck as (-> & -> & Hcase).
split; [reflexivity|]. split; [reflexivity|].
rewrite (repl_fixed_nr addr len FL_FIXED_NR eq_refl) in Hcase.
destruct Hcase as [(_ & Hb & ->)|(Hc' & _)]; [auto| rewrite Hc in Hc'; discriminate].
Qed.

Lemma remap_kit :
(forall evs X, STEP (mkCfg ms mo) evs X -> exists eff mo2, X = SNext (mkCfg (nret ms eff) mo2) /\ CHK eff mo = CheckOk mo2 evs /\ ~ SPUR eff)
/\ (forall eff mo2 evs, CHK eff mo = CheckOk mo2 evs -> ~ SPUR eff -> STEP (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo2))).
Proof.
apply (mm_kit ms mo (Z_to_bv 64 222)); [exact (proj1 Hat)| exact Hh| | |].
- intros eff. apply mmap_sys. exact Hat.
- intros eff. apply (check_fixed_nu addr len FL_FIXED_NR Hg Hfl eff mo Htop). left. exact Hc.
- intros eff mo2 evs Hck. destruct (errno_ret_in mmap_errnos (eff_ret eff)) eqn:He.
+ rewrite (check_fixed_red addr len FL_FIXED_NR Hg Hfl eff mo Htop), Hc in Hck.
destruct eff as [r ws zs us cs ci]. cbn [eff_ret] in He. cbn [eff_copyins eff_writes].
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
rewrite He in Hck. destruct zs; [|discriminate]. split; [reflexivity|]. split; [reflexivity|].
destruct us as [|u us]; [cbv iota in Hck; injection Hck as <- _; exact Hh|].
cbv iota in Hck. destruct (listNN_eqb (u :: us) [(a, n)]); [|discriminate]. injection Hck as <- _. rewrite halted_destroyed. exact Hh.
+ apply remap_ok in Hck as (-> & -> & _ & ->); [| exact He].
cbn [eff_copyins eff_writes]. split; [reflexivity|]. split; [reflexivity|].
destruct (vm_onlyA_facts _ _ (vm_onlyA_remap mo a n)) as (_ & _ & -> & _). exact Hh.
Qed.

Lemma remap_complete : forall evs X, STEP (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L NODE mo rsp mo' evs /\ CINV ms' mo' /\ m_halted mo' = None.
Proof.
intros evs X Hst.
destruct (proj1 remap_kit evs X Hst) as (eff & mo2 & -> & Hck & Hsp).
apply remap_ok in Hck as (-> & -> & Hb & ->); [| exact (remap_ret_ok eff Hsp)].
destruct remap_success as (Hv & HC2 & Hh2 & _).
eexists (rsp_remap a n), _, (remap_model mo a n). split; [reflexivity|]. split; [exact Hv|].
split; [| auto]. cbn -[rlenw rsp_err remap_model rsp_remap]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma remap_sound : forall rsp mo' evs, nstep_raw L NODE mo rsp mo' evs ->
exists ms' mo2 rsp2, STEP (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L NODE mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA NODE rsp rsp2 /\ m_halted mo2 = None.
Proof.
intros rsp mo' evs Hr.
cbn -[rlenw rsp_err remap_model rsp_remap] in Hr. destruct Hr as [-> Hr].
destruct Hr as (-> & ->).
destruct remap_success as (Hv & HC2 & Hh2 & Hb).
exists (nret ms EFF), (remap_model mo a n), (rsp_remap a n). split.
{ rewrite <- (repl_fixed_nr addr len FL_FIXED_NR eq_refl mo). apply (proj2 remap_kit); [apply (check_fixed_repl addr len FL_FIXED_NR Hg Hfl); assumption|].
apply ns_mmap_ret; [reflexivity| exact remap_a_not_errno]. }
split; [exact Hv|]. split.
{ cbn -[rlenw rsp_err remap_model rsp_remap]. split; [reflexivity|]. split; reflexivity. }
split; [apply msim_refl|]. split; [apply rvarA_refl| exact Hh2].
Qed.

Lemma remap_progress : exists rsp mo' evs, nstep_raw L NODE mo rsp mo' evs.
Proof. exists (rsp_remap a n), (remap_model mo a n), []. cbn -[rlenw remap_model rsp_remap]. split; [reflexivity|]. split; reflexivity. Qed.

End RemapNode.

Section MunmapNode.
Variables (ms : machine_state) (mo : Model) (addr len : Z).
#[local] Notation a := (Z_to_bv 64 addr).
#[local] Notation n := (rlenw len).
Hypothesis Hat : at_node segs (NMunmap addr len) ms.
Hypothesis Hss : sh_some L a n (ms_mem (msview L mo ms)).
Hypothesis Hh : m_halted mo = None.
Hypothesis HC : CINV ms mo.
Hypothesis Hns : 0 < len /\ len <= 2^40 /\ addr mod 4096 = 0 /\ 0 <= addr /\ addr + rlen len <= TASK_SIZE /\
map_has (vm_maps (m_vmmaps mo)) a n = true /\
(forall e, In e (vm_maps (m_vmmaps mo)) -> fst e = a -> snd e = n) /\
region_free (map_remove (vm_maps (m_vmmaps mo)) a) a n = true /\ excl_entry L (a, n) = false.
#[local] Notation CHK eff mo := (check_munmap (Z_to_bv 64 addr) (Z_to_bv 64 len) eff mo).
#[local] Notation NODE := (NMunmap addr len).
#[local] Notation EFF := (mkEffectU (Z_to_bv 64 0) [] [] [(a, n)] [] []).
#[local] Notation STEP := (sstep_cfg segs (alloc_only_cfg false)).
#[local] Notation SPUR eff := (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (Z_to_bv 64 215)) mo eff).

Lemma munmap_ns : forall eff, ~ SPUR eff.
Proof. intros eff. apply ns_sysno. intros Hin. vm_compute in Hin. lia. Qed.

Lemma munmap_kit :
(forall evs X, STEP (mkCfg ms mo) evs X -> exists eff mo2, X = SNext (mkCfg (nret ms eff) mo2) /\ CHK eff mo = CheckOk mo2 evs /\ ~ SPUR eff)
/\ (forall eff mo2 evs, CHK eff mo = CheckOk mo2 evs -> ~ SPUR eff -> STEP (mkCfg ms mo) evs (SNext (mkCfg (nret ms eff) mo2))).
Proof.
destruct Hns as (H1 & H2 & H3 & H4 & H5 & Hhas & Hsz & Hfree & Hex).
apply (mm_kit ms mo (Z_to_bv 64 215)); [exact (proj1 Hat)| exact Hh| | |].
- intros eff. apply munmap_sys. exact Hat.
- intros eff. apply (check_munmap_nu addr len); [lia| lia| exact Hhas].
- intros eff mo2 evs Hck. apply (check_munmap_ok addr len) in Hck as (-> & -> & us & -> & ->); [|lia|lia|exact Hhas].
cbn [eff_copyins eff_writes]. split; [reflexivity|]. split; [reflexivity|].
destruct (vm_onlyA_facts _ _ (vm_onlyA_munmap mo a n)) as (_ & _ & -> & _). exact Hh.
Qed.

Lemma munmap_core :
msview L (munmap_model mo a n) (nret ms EFF) = nret (msview L mo ms) (rsp_munmap L (munmap_model mo a n) a n)
/\ CINV (nret ms EFF) (munmap_model mo a n) /\ m_halted (munmap_model mo a n) = None.
Proof.
destruct Hns as (H1 & H2 & H3 & H4 & H5 & Hhas & Hsz & Hfree & Hex). destruct HC as ([HF [W [X Y]]] & HI & HJ).
pose proof (rlen_facts len H1 H2) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
assert (Hn : 0 < bv_unsigned n) by (rewrite R6; lia).
assert (Hsh : forall z, allowed_byte L (munmap_model mo a n) z = true -> allowed_byte L mo z = true).
{ apply allowed_shrink. eapply appcov_shrink_of. intros y. apply appcov_munmap; assumption. }
assert (Hlost : forall z, allowed_byte L mo z = true -> allowed_byte L (munmap_model mo a n) z = false ->
inR a n z = true \/ zin z (shadow_iv L a n) = true).
{ apply allowed_lost; [| exact Hn]. intros y. apply appcov_munmap; assumption. }
split; [|split].
- unfold rsp_munmap. apply msview_nret_intro. cbn [apply_writes apply_zeros]. apply view_unmap; [exact HL| exact Hsh| exact Hlost].
- split; [| split].
+ eapply xinvA_intro; [apply vm_onlyA_munmap| exact HF| apply wf_munmap; exact W| apply excl_inside_munmap; assumption| apply mbt_munmap; exact Y].
+ unfold lv_inv in *. rewrite limit_munmap. pose proof (Phi_munmap L mo a n W Hsz Hfree Hn). lia.
+ rewrite nret_mem. cbn [apply_writes apply_zeros]. eapply (jsome_unmap L HL); [exact Hsh| exact Hlost| | | exact HJ].
* intros x Hb. apply bands_avoid_range; [exact Hex| exact Hb].
* rewrite <- msview_mem. exact Hss.
- destruct (vm_onlyA_facts _ _ (vm_onlyA_munmap mo a n)) as (_ & _ & -> & _). exact Hh.
Qed.

Lemma munmap_complete : forall evs X, STEP (mkCfg ms mo) evs X ->
exists rsp ms' mo', X = SNext (mkCfg ms' mo') /\ msview L mo' ms' = nret (msview L mo ms) rsp /\
nstep_raw L NODE mo rsp mo' evs /\ CINV ms' mo' /\ m_halted mo' = None.
Proof.
intros evs X Hst. destruct Hns as (H1 & H2 & H3 & H4 & H5 & Hhas & Hsz & Hfree & Hex).
destruct (proj1 munmap_kit evs X Hst) as (eff & mo2 & -> & Hck & _).
apply (check_munmap_ok addr len) in Hck as (-> & -> & us & -> & ->); [|lia|lia|exact Hhas].
destruct munmap_core as (Hv & HC2 & Hh2).
eexists (rsp_munmap L (munmap_model mo a n) a n), _, (munmap_model mo a n). split; [reflexivity|]. split; [exact Hv|].
split; [| auto]. cbn -[rlenw munmap_model rsp_munmap]. repeat split; reflexivity.
Qed.

Lemma munmap_sound : forall rsp mo' evs, nstep_raw L NODE mo rsp mo' evs ->
exists ms' mo2 rsp2, STEP (mkCfg ms mo) evs (SNext (mkCfg ms' mo2)) /\
msview L mo2 ms' = nret (msview L mo ms) rsp2 /\
nstep_raw L NODE mo rsp2 mo2 evs /\ msim mo' mo2 /\ rvarA NODE rsp rsp2 /\ m_halted mo2 = None.
Proof.
intros rsp mo' evs Hr. destruct Hns as (H1 & H2 & H3 & H4 & H5 & Hhas & Hsz & Hfree & Hex).
cbn -[rlenw munmap_model rsp_munmap] in Hr. destruct Hr as (-> & -> & ->).
destruct munmap_core as (Hv & HC2 & Hh2).
exists (nret ms EFF), (munmap_model mo a n), (rsp_munmap L (munmap_model mo a n) a n). split.
{ apply (proj2 munmap_kit); [apply (check_munmap_intro addr len); [lia| lia| exact Hhas]| apply munmap_ns]. }
split; [exact Hv|]. split; [cbn -[rlenw munmap_model rsp_munmap]; repeat split; reflexivity|].
split; [apply msim_refl|]. split; [apply rvarA_refl| exact Hh2].
Qed.

Lemma munmap_progress : exists rsp mo' evs, nstep_raw L NODE mo rsp mo' evs.
Proof. eexists _, _, []. cbn -[rlenw munmap_model rsp_munmap]. repeat split; reflexivity. Qed.

End MunmapNode.

End MmNodes.
