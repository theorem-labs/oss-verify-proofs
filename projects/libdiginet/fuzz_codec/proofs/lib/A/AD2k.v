(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD2k.v, with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build; the sink's path, mode, "rwa" and trailer strings are removed from finv_check and tfib_finv_handoff, with finv_img_garr8, which only they used, as fuzz_scene.asan holds none of the strings; finv_check carries no kn_img conjunct for fuzz_scene's five registered globals either, as in fuzz_grant's adapted A/AD2k.v:27-33, because astdio_env no longer reads any string; the mmap page floor in the hand-off check is IMG_TOP / 4096 (1529 for fuzz_scene: image top 0x5f9000), where the released file states cgif_file's 1531; and the ofl head that tfib_finv_handoff reads is fuzz_scene's ofl_head (0x5f6e90). *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_scene/proofs/lib/A/AD2k.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libdiginet.fuzz_codec.images Require Import Asan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r YG0b.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AF0m.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AD1g AD2i.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0d YI04 YI00 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AB1v AE2k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Definition e254 : expr := EMd M_MUL (ELit 4096) (EVar 254).
Definition finv_check (ch : acs) : bool :=
(match kn_read TSEGS ch (ELit 0) 0xa5cc0 8 with Some v => expr_eqb v (ELit 0xa5cc8) | _ => false end
&& match kn_read TSEGS ch (ELit 0) 0xa5cc8 8 with Some v => expr_eqb v e254 | _ => false end
&& kn_mem (KZero (SA e254 0) (ELit 3727360)) ch
&& kn_mem (KRange (EVar 254) (IMG_TOP / 4096) 34359735410) ch
&& kn_img ch 0x5f96a1 1 && kn_img ch 0x5f96a3 1 && kn_img ch 0x5f9b00 4 && kn_img ch 0x5f9b08 8
&& match kn_read TSEGS ch (ELit 0) 0x5f9450 8 with Some _ => true | None => false end)%bool.
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
pose proof (tfib_rom_all i ltac:(lia)) as Hrom. change AWalkFw0.tfibsegs with tfibsegs in Hrom.
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
apply andb_prop in H as [H Kthr]. apply andb_prop in H as [H Krng]. apply andb_prop in H as [H Kzero]. apply andb_prop in H as [Kptr Kmem].
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
destruct (kn_read TSEGS ch (ELit 0) 0xa5cc0 8) as [vp|] eqn:Hrp; [|discriminate Kptr]. apply expr_eqb_eq in Kptr. subst vp.
destruct (kn_read TSEGS ch (ELit 0) 0xa5cc8 8) as [vm|] eqn:Hrm; [|discriminate Kmem]. apply expr_eqb_eq in Kmem. subst vm.
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
unfold astdio_env. cbn [ak_threaded ak_need_locks ak_ofl_lock ak_canary tfib_K].
unfold A_threaded, A_need_locks, A_ofl_lock, FF_canary.
split; [apply (ZC 6264481 1%nat); [exact Kthr | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC 6264483 1%nat); [exact Knl | lia | lia | intros k Hk; destruct k as [|k]; [vm_compute; reflexivity | cbn in Hk; lia]]|].
split; [apply (ZC 6265600 4%nat); [exact Kofl | lia | lia | intros k Hk; do 4 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia]|].
destruct (kn_read TSEGS ch (ELit 0) 6263888 8) as [vc|] eqn:Hrc; [|discriminate Kcan].
exists (u vc). split; [apply uE_bound | exact (finv_read_val _ _ _ Hrc ltac:(lia))].
-
unfold A_ofl_head. apply (ZC 6265608 8%nat); [exact Kofh | lia | lia | intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); cbn in Hk; lia].
Qed.
End e.
End c.
