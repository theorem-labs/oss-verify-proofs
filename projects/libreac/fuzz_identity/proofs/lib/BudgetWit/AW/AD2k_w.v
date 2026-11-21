(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD2k.v, with its module paths and addresses changed; 12 of its 153 lines of code are new or changed and 31 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD2k.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (changed Zify, e254, finv_check, finv_check_all, Hch, hw and 5 more; added SINV_sp0, inst). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_identity.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK0g YK0c YK0d YK0e YK0f YK09 YA01.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0c_w YA0e_w YA0d_w YA02_w YA0j_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB12.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB1h_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB13.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AB01r_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG01 YG0f YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0r_w YG0b_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD1g_w AD2i_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YE00_w YE01_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AE2k_w.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
(* LPS 727298f3: the hand-off states this driver reads are BudgetWit/AW/AB01r_w.v's, computed from the run, and their fresh
   variables are numbered as the new run numbers them: v < 9 unchanged, 9 -> 10 (the launch layout, YA01: V_G 9,
   V_HW 10, V_GID 11), 10..292 -> +4, 357 and up -> +6, the map read on A's states (lib/A/ZZ_iddrv.v, outputs
   ZZIDD_MAPS_NEW_0_0 / ZZIDD_MAPS_OLD_0, ZZIDD_RANGES_NEW_0_0 / ZZIDD_RANGES_OLD_0, zz_idhs_A0.out / zz_idhs_A1.out), and on
   the 16 GiB run's own states (lib/BudgetWit/AW/ZZ_idstartW.v, outputs ZZIDW_MAPS_NEW_0_0 / ZZIDW_MAPS_OLD_0,
   ZZIDW_RANGES_NEW_0_0 / ZZIDW_RANGES_OLD_0, ZZIDW_MAPS_NEW_1_0, ZZIDW_RANGES_NEW_1_0).  Every variable literal below is renumbered by that map. *)
Definition e254 : expr := EMd M_MUL (ELit 4096) (EVar 258).
Definition finv_check (ch : acs) : bool :=
(match kn_read TSEGS ch (ELit 0) 0xa4800 8 with Some v => expr_eqb v (ELit 0xa4808) | _ => false end
&& match kn_read TSEGS ch (ELit 0) 0xa4808 8 with Some v => expr_eqb v e254 | _ => false end
&& kn_mem (KZero (SA e254 0) (ELit 3727360)) ch
&& kn_mem (KRange (EVar 258) 1530 34359735410) ch
(* Theorem Labs, 2026-10-29: no-file sink form, grant's AD2k.v:31-32; the path, mode, "rwa" and trailer kn_img conjuncts are removed. *)
&& kn_img ch 0x5f81e1 1 && kn_img ch 0x5f81e3 1 && kn_img ch 0x5f8640 4 && kn_img ch 0x5f8648 8
&& match kn_read TSEGS ch (ELit 0) 0x5f7f90 8 with Some _ => true | None => false end)%bool.
Lemma finv_check_all : forallb finv_check HS_tfib_list_all = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {fx : YK11.FPState}.
Section e.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
(* The invariant abstract and the input's own fields, as A/AD2i_w.v. *)
Variable SINV : env -> (word -> option byte) -> Prop.
#[local] Notation argH := (YA02_w.argH0 sp rdraw argv envp
  (in_image_fs inp) (in_stdin inp) uid (in_gid inp) hw (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
#[local] Notation TOP := (YA02_w.TOP sp).
#[local] Notation LIM := YA02_w.LIMIT.
Hypothesis SINV_sp0 : forall E' M, SINV E' M -> uE E' e_sp0 = TOP + 8388608.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Context {rc : YM05.RunCeil}.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation m1 := (mrestrict (AD2i_w.H1 sp rdraw inp ch E model) FULL).
#[local] Notation u := (uE E).
Let CHK : finv_check ch = true := proj1 (forallb_forall _ _) finv_check_all ch (HS_tfib_r_In _ h ch Hch).
Let MRm1 := AD2i_w.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model.
(* AD1g's lemmas at this section's arguments, whatever subset each one takes. *)
Ltac inst H := try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch);
try specialize (H SINV); try specialize (H SINV_sp0); try specialize (H HC).
Lemma finv_read_val : forall a n v, kn_read TSEGS ch (ELit 0) a n = Some v -> 0 <= a ->
val_mem tfibsegs m1 a n (u v).
Proof.
intros a n v Hr Ha k Hk.
pose proof (ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (ELit 0) a n v Hr k Hk) as X.
rewrite uE_litv in X by lia. rewrite Z.add_0_l in X.
destruct (AD2i_w.hreader_mbyte sp rdraw inp ch E FULL model _ _ X) as (b & Hb & Hbu).
change tfibsegs with TSEGS. rewrite (MRm1 _ _ Hb). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hbu.
pose proof (ho_read_bound TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ Hr) as Hv. fold (u v) in Hv.
unfold YO0f.le_byte. rewrite (Z.mod_small (u v)) by exact Hv. rewrite Z.shiftr_div_pow2 by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma finv_img_byte : forall a len, kn_img ch a len = true -> forall i, a <= i < a + len -> 65536 <= a -> a + len <= 6266880 ->
mbyte tfibsegs m1 i = seg_rom tfibsegs (Z_to_bv 64 i) /\ seg_rom tfibsegs (Z_to_bv 64 i) <> None.
Proof.
intros a len H i Hi Hlo Hhi. unfold kn_img in H. apply existsb_exists in H as (K & HK & HKb).
destruct K as [| | |lo hi| | | | | |]; try discriminate HKb. apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
pose proof (Hnone i ltac:(lia)) as X.
pose proof (tfib_rom_all i ltac:(lia)) as Hrom. change AB1v.tfibsegs with tfibsegs in Hrom.
split; [|exact Hrom].
destruct (seg_rom tfibsegs (Z_to_bv 64 i)) as [b|] eqn:Hs; [|exfalso; exact (Hrom eq_refl)].
change tfibsegs with TSEGS. apply MRm1. unfold mbyte. rewrite X. exact Hs.
Qed.
Lemma finv_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x5fa000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
(* Theorem Labs, 2026-10-29: no-file sink form, grant's AD2k.v:92-93; finv_img_garr8 is removed, as only the four string splits used it. *)
Lemma finv_img_val : forall a n v, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= 6266880 ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k))) ->
val_mem tfibsegs m1 a n v.
Proof.
intros a n v Hk Hlo Hhi Hrom k Hk1.
destruct (finv_img_byte a (Z.of_nat n) Hk (a + Z.of_nat k) ltac:(lia) Hlo Hhi) as [-> _]. exact (Hrom k Hk1).
Qed.
Theorem tfib_finv_handoff :
(exists M, ameta_inv tfibsegs tfib_K (AD1g_w.ly0 ch E model) m1 M) /\
astdio_env tfibsegs tfib_K m1 /\
val_mem tfibsegs m1 A_ofl_head 8 0.
Proof.
pose proof CHK as H. unfold finv_check in H.
(* Theorem Labs, 2026-10-29: no-file sink form, grant's AD2k.v:106-107. *)
apply andb_prop in H as [H Kcan]. apply andb_prop in H as [H Kofh]. apply andb_prop in H as [H Kofl]. apply andb_prop in H as [H Knl].
apply andb_prop in H as [H Kthr]. apply andb_prop in H as [H Krng]. apply andb_prop in H as [H Kzero]. apply andb_prop in H as [Kptr Kmem].
pose proof (@AD1g_w.u254) as U254. inst U254. destruct U254 as [E254 R254]. change AD1g_w.e254 with e254 in E254, R254.
set (M := u e254) in *.
assert (ZC : forall a n, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= 6266880 ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 0)) -> val_mem tfibsegs m1 a n 0).
{ intros a n Hk Hlo Hhi Hz. apply (finv_img_val a n 0 Hk Hlo Hhi). intros k Hkn. rewrite (Hz k Hkn). f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
split; [|split].
-
exists M. split; [|split].
+
cbn [AD1g_w.ly0 ly_extra]. unfold AD1g_w.extra.
pose proof (AD1g_w.dm_vals E) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W254 & _). change AD1g_w.e254 with e254 in W254.
replace (M, AMETA_SIZE) with (wzp (AD1g_w.d254 E)) by (rewrite W254; reflexivity).
apply in_map. apply filter_In. split.
* pose proof (@AD1g_w.vm_shape) as VMS. inst VMS. destruct VMS as (fog & _ & _ & ->).
apply in_app_iff. right. apply in_app_iff. right. cbn. tauto.
*
destruct (AD1g_w.known E (AD1g_w.d254 E)) eqn:Hk; [|reflexivity]. exfalso.
unfold AD1g_w.known in Hk. apply existsb_exists in Hk as (d & Hd & Heq). apply AD1g_w.iv_eqb_eq in Heq.
apply (f_equal (fun iv => bv_unsigned (snd iv))) in Heq. unfold AD1g_w.d254 in Heq. rewrite AD1g_w.u_snd_dm in Heq by lia.
unfold AD1g_w.KNOWN in Hd. cbn [In] in Hd.
unfold AD1g_w.dP, AD1g_w.dQ, AD1g_w.dT, AD1g_w.dF, AD1g_w.dNB, AD1g_w.dSB, AD1g_w.dC, AD1g_w.dD in Hd.
unfold AD1g_w.dLow, AD1g_w.dHigh, AD1g_w.dGap in Hd.
repeat (destruct Hd as [<- | Hd]; [rewrite AD1g_w.u_snd_dm in Heq by lia; discriminate Heq|]). exact Hd.
+
intros a Ha. pose proof (finv_img_range a Ha). subst M. lia.
+
destruct (kn_read TSEGS ch (ELit 0) 0xa4800 8) as [vp|] eqn:Hrp; [|discriminate Kptr]. apply expr_eqb_eq in Kptr. subst vp.
destruct (kn_read TSEGS ch (ELit 0) 0xa4808 8) as [vm|] eqn:Hrm; [|discriminate Kmem]. apply expr_eqb_eq in Kmem. subst vm.
pose proof (finv_read_val _ _ _ Hrp ltac:(lia)) as Vp. rewrite uE_litv in Vp by lia.
pose proof (finv_read_val _ _ _ Hrm ltac:(lia)) as Vm. fold M in Vm.
unfold ameta_ok. cbn [ak_meta_ptr ak_meta_mem tfib_K]. unfold FF_meta_ptr, FF_meta_mem, AMETA_SIZE.
split; [exact Vp|]. split; [exact Vm|]. split; [lia|]. split; [lia|]. split; [rewrite E254, Z.mul_comm; apply Z_mod_mult|].
intros a Ha.
pose proof (ho_zero_at TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ Kzero (a - M)) as Z0.
unfold elenZ, estart in Z0. cbn [a_base a_off edenot] in Z0. rewrite u64_lit in Z0 by lia. fold (u e254) in Z0. fold M in Z0.
specialize (Z0 ltac:(lia)). replace (M + 0 + (a - M)) with a in Z0 by lia.
change tfibsegs with TSEGS. unfold mbyte. rewrite (AD2i_w.MR_m1 sp rdraw inp ch E FULL model _ _ Z0). reflexivity.
-
(* Theorem Labs, 2026-10-29: no-file sink form, grant's AD2k.v:147-148. *)
unfold astdio_env. cbn [ak_threaded ak_need_locks ak_ofl_lock ak_canary tfib_K].
unfold A_threaded, A_need_locks, A_ofl_lock, FF_canary.
split; [apply (ZC 6259169 1%nat); [exact Kthr | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC 6259171 1%nat); [exact Knl | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC 6260288 4%nat); [exact Kofl | lia | lia | intros k Hk; do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia]|].
(* Theorem Labs, 2026-10-29: no-file sink form, grant's AD2k.v:151-152; the sink_path_Z, sink_mode_Z, sink_rwa_Z, sink_trailer_Z splits are removed. *)
destruct (kn_read TSEGS ch (ELit 0) 6258576 8) as [vc|] eqn:Hrc; [|discriminate Kcan].
exists (u vc). split; [apply uE_bound | exact (finv_read_val _ _ _ Hrc ltac:(lia))].
-
unfold A_ofl_head. apply (ZC 6260296 8%nat); [exact Kofh | lia | lia | intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia].
Qed.
End e.
End c.
