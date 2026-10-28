(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB12 AB1h AB13 AB01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05 YD1h.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD1g AD2i.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG0d YI04 YI00 YE00 YE01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Definition e254 : expr := EMd M_MUL (ELit 4096) (EVar 254).
Definition finv_check (ch : acs) : bool :=
(match kn_read TSEGS ch (ELit 0) 0xa5840 8 with Some v => expr_eqb v (ELit 0xa5848) | _ => false end
&& match kn_read TSEGS ch (ELit 0) 0xa5848 8 with Some v => expr_eqb v e254 | _ => false end
&& kn_mem (KZero (SA e254 0) (ELit 3727360)) ch
&& kn_mem (KRange (EVar 254) 1531 34359735410) ch
&& kn_img ch 0x20e00 13 && kn_img ch 0x20e60 3 && kn_img ch 0x20ea0 2 && kn_img ch 0x20124 4
&& kn_img ch 0x5f9221 1 && kn_img ch 0x5f9223 1 && kn_img ch 0x5f9680 4 && kn_img ch 0x5f9688 8
&& match kn_read TSEGS ch (ELit 0) 0x5f8fd0 8 with Some _ => true | None => false end)%bool.
Lemma finv_check_all : forallb finv_check HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {fx : YK11.FPState}.
Section e.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Context {rc : YM05.RunCeil}.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation m1 := (mrestrict (AD2i.H1 sp rdraw inp ch E model) FULL).
#[local] Notation u := (uE E).
Let CHK : finv_check ch = true := proj1 (forallb_forall _ _) finv_check_all ch (HS_tfib_In h ch Hch).
Let MRm1 := AD2i.mbyte_MR_m1 sp rdraw inp Hsp Hva ch E FULL model.
Lemma finv_read_val : forall a n v, kn_read TSEGS ch (ELit 0) a n = Some v -> 0 <= a ->
val_mem tfibsegs m1 a n (u v).
Proof.
intros a n v Hr Ha k Hk.
pose proof (ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (ELit 0) a n v Hr k Hk) as X.
rewrite uE_litv in X by lia. rewrite Z.add_0_l in X.
destruct (AD2i.hreader_mbyte sp rdraw inp ch E FULL model _ _ X) as (b & Hb & Hbu).
change tfibsegs with TSEGS. rewrite (MRm1 _ _ Hb). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, Hbu.
pose proof (ho_read_bound TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ _ _ Hr) as Hv. fold (u v) in Hv.
unfold YO0f.le_byte. rewrite (Z.mod_small (u v)) by exact Hv. rewrite Z.shiftr_div_pow2 by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma finv_img_byte : forall a len, kn_img ch a len = true -> forall i, a <= i < a + len -> 65536 <= a -> a + len <= 6270976 ->
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
Lemma finv_img_range : forall a, in_img tfibsegs a -> 0x10000 <= a < 0x5fb000.
Proof.
intros a (sg & Hin & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
(map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; lia.
Qed.
Lemma finv_img_garr8 : forall a (l : list Z), kn_img ch a (Z.of_nat (length l)) = true -> 65536 <= a -> a + Z.of_nat (length l) <= 6270976 ->
(forall j, (j < length l)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat j)) = Some (Z_to_bv 8 (nth j l 0))) ->
Forall (fun b => 0 <= b < 256) l ->
garr8 tfibsegs m1 a l.
Proof.
intros a l Hk Hlo Hhi Hrom Hb j Hj. split; [| exact (proj1 (Forall_forall _ _) Hb _ (nth_In l 0 Hj))].
intros k Hk1. destruct k; [|cbn in Hk1; lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
destruct (finv_img_byte a (Z.of_nat (length l)) Hk (a + Z.of_nat j) ltac:(lia) Hlo Hhi) as [-> _].
rewrite (Hrom j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned.
pose proof (proj1 (Forall_forall _ _) Hb _ (nth_In l 0 Hj)) as Rb.
unfold YO0f.le_byte. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
cbn beta in Rb. rewrite !(Z.mod_small (nth j l 0) 256) by lia. reflexivity.
Qed.
Lemma finv_img_val : forall a n v, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= 6270976 ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (YO0f.le_byte v n k))) ->
val_mem tfibsegs m1 a n v.
Proof.
intros a n v Hk Hlo Hhi Hrom k Hk1.
destruct (finv_img_byte a (Z.of_nat n) Hk (a + Z.of_nat k) ltac:(lia) Hlo Hhi) as [-> _]. exact (Hrom k Hk1).
Qed.
Theorem tfib_finv_handoff :
(exists M, ameta_inv tfibsegs tfib_K (AD1g.ly0 ch E model) m1 M) /\
astdio_env tfibsegs tfib_K m1 /\
val_mem tfibsegs m1 A_ofl_head 8 0.
Proof.
pose proof CHK as H. unfold finv_check in H.
apply andb_prop in H as [H Kcan]. apply andb_prop in H as [H Kofh]. apply andb_prop in H as [H Kofl]. apply andb_prop in H as [H Knl].
apply andb_prop in H as [H Kthr]. apply andb_prop in H as [H Krwa]. apply andb_prop in H as [H Ktr]. apply andb_prop in H as [H Kwb].
apply andb_prop in H as [H Kpath]. apply andb_prop in H as [H Krng]. apply andb_prop in H as [H Kzero]. apply andb_prop in H as [Kptr Kmem].
destruct (AD1g.u254 sp rdraw brk inp h ch E R FULL model Hch HC) as [E254 R254]. change AD1g.e254 with e254 in E254, R254.
set (M := u e254) in *.
assert (ZC : forall a n, kn_img ch a (Z.of_nat n) = true -> 65536 <= a -> a + Z.of_nat n <= 6270976 ->
(forall k, (k < n)%nat -> seg_rom tfibsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 0)) -> val_mem tfibsegs m1 a n 0).
{ intros a n Hk Hlo Hhi Hz. apply (finv_img_val a n 0 Hk Hlo Hhi). intros k Hkn. rewrite (Hz k Hkn). f_equal. f_equal.
unfold YO0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
split; [|split].
-
exists M. split; [|split].
+
cbn [AD1g.ly0 ly_extra]. unfold AD1g.extra.
pose proof (AD1g.dm_vals E) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & W254 & _). change AD1g.e254 with e254 in W254.
replace (M, AMETA_SIZE) with (wzp (AD1g.d254 E)) by (rewrite W254; reflexivity).
apply in_map. apply filter_In. split.
* destruct (AD1g.vm_shape sp rdraw brk inp h ch E R FULL model Hch HC) as (fog & _ & _ & ->).
apply in_app_iff. right. apply in_app_iff. right. cbn. tauto.
*
destruct (AD1g.known E (AD1g.d254 E)) eqn:Hk; [|reflexivity]. exfalso.
unfold AD1g.known in Hk. apply existsb_exists in Hk as (d & Hd & Heq). apply AD1g.iv_eqb_eq in Heq.
apply (f_equal (fun iv => bv_unsigned (snd iv))) in Heq. unfold AD1g.d254 in Heq. rewrite AD1g.u_snd_dm in Heq by lia.
unfold AD1g.KNOWN in Hd. cbn [In] in Hd.
unfold AD1g.dP, AD1g.dQ, AD1g.dT, AD1g.dF, AD1g.dNB, AD1g.dSB, AD1g.dC, AD1g.dD in Hd.
unfold AD1g.dLow, AD1g.dHigh, AD1g.dGap in Hd.
repeat (destruct Hd as [<- | Hd]; [rewrite AD1g.u_snd_dm in Heq by lia; discriminate Heq|]). exact Hd.
+
intros a Ha. pose proof (finv_img_range a Ha). subst M. lia.
+
destruct (kn_read TSEGS ch (ELit 0) 0xa5840 8) as [vp|] eqn:Hrp; [|discriminate Kptr]. apply expr_eqb_eq in Kptr. subst vp.
destruct (kn_read TSEGS ch (ELit 0) 0xa5848 8) as [vm|] eqn:Hrm; [|discriminate Kmem]. apply expr_eqb_eq in Kmem. subst vm.
pose proof (finv_read_val _ _ _ Hrp ltac:(lia)) as Vp. rewrite uE_litv in Vp by lia.
pose proof (finv_read_val _ _ _ Hrm ltac:(lia)) as Vm. fold M in Vm.
unfold ameta_ok. cbn [ak_meta_ptr ak_meta_mem tfib_K]. unfold FF_meta_ptr, FF_meta_mem, AMETA_SIZE.
split; [exact Vp|]. split; [exact Vm|]. split; [lia|]. split; [lia|]. split; [rewrite E254, Z.mul_comm; apply Z_mod_mult|].
intros a Ha.
pose proof (ho_zero_at TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ Kzero (a - M)) as Z0.
unfold elenZ, estart in Z0. cbn [a_base a_off edenot] in Z0. rewrite u64_lit in Z0 by lia. fold (u e254) in Z0. fold M in Z0.
specialize (Z0 ltac:(lia)). replace (M + 0 + (a - M)) with a in Z0 by lia.
change tfibsegs with TSEGS. unfold mbyte. rewrite (AD2i.MR_m1 sp rdraw inp ch E FULL model _ _ Z0). reflexivity.
-
unfold astdio_env. cbn [ak_threaded ak_need_locks ak_ofl_lock ak_path ak_mode ak_rwa ak_trailer ak_canary tfib_K].
unfold A_threaded, A_need_locks, A_ofl_lock, A_PATH, A_WB, A_RWA, A_TRAILER, FF_canary.
split; [apply (ZC 6263329 1%nat); [exact Kthr | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC 6263331 1%nat); [exact Knl | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC 6264448 4%nat); [exact Kofl | lia | lia | intros k Hk; do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia]|].
split; [apply (finv_img_garr8 134656 (YI16.sink_path_Z ++ [0])); [exact Kpath | lia | cbn; lia | intros j Hj; do 13 (destruct j as [|j]; [vm_compute; reflexivity|]); cbn in Hj; lia | apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb]|].
split; [apply (finv_img_garr8 134752 (YI16.sink_mode_Z ++ [0])); [exact Kwb | lia | cbn; lia | intros j Hj; do 3 (destruct j as [|j]; [vm_compute; reflexivity|]); cbn in Hj; lia | apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb]|].
split; [apply (finv_img_garr8 131364 (sink_rwa_Z ++ [0])); [exact Krwa | lia | cbn; lia | intros j Hj; do 4 (destruct j as [|j]; [vm_compute; reflexivity|]); cbn in Hj; lia | apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb]|].
split; [apply (finv_img_garr8 134816 (sink_trailer_Z ++ [0])); [exact Ktr | lia | cbn; lia | intros j Hj; do 2 (destruct j as [|j]; [vm_compute; reflexivity|]); cbn in Hj; lia | apply Forall_forall; intros b Hb; cbn in Hb; repeat (destruct Hb as [<-|Hb]; [lia|]); destruct Hb]|].
destruct (kn_read TSEGS ch (ELit 0) 6262736 8) as [vc|] eqn:Hrc; [|discriminate Kcan].
exists (u vc). split; [apply uE_bound | exact (finv_read_val _ _ _ Hrc ltac:(lia))].
-
unfold A_ofl_head. apply (ZC 6264456 8%nat); [exact Kofh | lia | lia | intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia].
Qed.
End e.
End c.
