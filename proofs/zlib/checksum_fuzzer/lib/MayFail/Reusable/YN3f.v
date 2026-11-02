(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3f.v, with its module paths, addresses and numbers changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable.R Require Import Cfg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma t_alt_wall' : forall (ch : word) (rest : list byte) (T : TSet),
(1 <= length rest)%nat ->
t_eq (t_alt (fun i : wr_index rest =>
t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
(t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
(t_emit (map (WriteEv ch) rest) T).
Proof.
intros ch rest T Hnb tr. split.
- intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
destruct Hi as [Hp | (tr1 & -> & Hi)].
+ left. eapply is_prefix_trans; [exact Hp|].
rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_r. apply is_prefix_refl.
+ destruct Hi as [Hp | (tr2 & -> & Ht)].
* left. rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
apply is_prefix_app_mono. exact Hp.
* right. exists tr2. split; [|exact Ht].
rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
- intros [Hp | (tr' & -> & Ht)].
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all. left. exact Hp.
+ exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
rewrite firstn_all, skipn_all. right.
exists tr'. split; [reflexivity|]. cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.
Section e.
Variable segs : list Segment.
Lemma rz_writev_dep : forall regs pc mem rom model fd ch iovs bs (T : nat -> TSet),
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd -> getr regs 10 = fd ->
w_is0 (iovcnt32 (getr regs 12)) = false ->
(bv_unsigned (getr regs 12) <= IOV_MAX)%Z ->
copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
(word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
iovs_access_okb iovs = true ->
gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
(iovs_total iovs <= MAX_RW_COUNT)%Z ->
(1 <= length bs)%nat ->
(forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom)
model) (T n)) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model)
(t_alt (fun i : wr_index bs => t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
intros regs pc mem rom model fd ch iovs bs T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc.
pose proof (writev_chk_canon segs regs pc mem rom model fd ch iovs bs Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb)
as Hchk.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen.
assert (HMv : MAX_RW_COUNT = 0x7ffff000%Z) by reflexivity.
set (mp := ms_read_byte (pend_at regs pc mem rom)) in *.
pose (ef := fun i : wr_index bs => writev_eff mp (getr regs 11) (getr regs 12) iovs (proj1_sig i)).
apply (rz_node segs (mkCfg (pend_at regs pc mem rom) model) (wr_index bs)
(fun i => map (WriteEv ch) (firstn (proj1_sig i) bs))
(fun i => mkCfg (advance_past_svc (apply_effect (pend_at regs pc mem rom) (ef i))) model)
(fun i => T (proj1_sig i)) (wr_full bs Hnb)).
- apply (node_chk segs (pend_at regs pc mem rom) model (getr regs 17) (wr_index bs) (wr_full bs Hnb)
ef (fun _ => model) (fun i => map (WriteEv ch) (firstn (proj1_sig i) bs)) Hh eq_refl).
+ intros [n [Hn1 Hn2]]. unfold ef, writev_eff; cbn [proj1_sig]. rewrite Hchk.
assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat n)) = Z.of_nat n).
{ rewrite Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. lia. }
rewrite Hu, Nat2Z.id.
rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia.
replace (addr_is_error_b (Z_to_bv 64 (Z.of_nat n))) with false
by (symmetry; unfold addr_is_error_b; apply Z.ltb_ge; rewrite Hu; unfold two_pow_64; lia).
rewrite (proj2 (access_ranges_eqb_eq _ _) eq_refl). reflexivity.
+ intros _. exact Hh.
+ intros _. exact Hlz.
+ intros [ret ws zs us cs ci] m' evs Hk. rewrite Hchk in Hk.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate].
destruct (((1 <=? bv_unsigned ret)%Z && (bv_unsigned ret <=? Z.of_nat (length bs))%Z) &&
negb (addr_is_error_b ret) && access_ranges_eqb ci _) eqn:E; [|discriminate].
injection Hk as <- <-.
apply andb_prop in E as [E Hci]. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
apply Z.leb_le in E1. apply Z.leb_le in E2. apply access_ranges_eqb_eq in Hci.
assert (Hr : (1 <= Z.to_nat (bv_unsigned ret))%nat /\ (Z.to_nat (bv_unsigned ret) <= length bs)%nat) by lia.
exists (exist _ (Z.to_nat (bv_unsigned ret)) Hr). unfold ef, writev_eff; cbn [proj1_sig].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_bv_unsigned, Hci. auto.
+ exact (fun _ => acfg_nonspurious_no _ _ _ _ _ _ Hno eq_refl).
- intros [n [Hn1 Hn2]]. unfold ef; cbn [proj1_sig]. rewrite adv_pend.
rewrite effmem_writev_eff. unfold writev_eff; cbn [eff_ret]. apply Hc; assumption.
Qed.
Lemma rz_writev2_wall : forall regs pc mem rom model fd ch (b0 l0 b1 l1 : word) bs0 bs1 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 2 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
access_okb (getr regs 11) 32 = true ->
access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
(1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT)%Z ->
(forall n, (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
(t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T)) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros regs pc mem rom model fd ch b0 l0 b1 l1 bs0 bs1 T
Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hc.
rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
unfold MAX_RW_COUNT in Htot.
assert (Hnb : (1 <= length (bs0 ++ bs1))%nat) by lia.
eapply rz_conseq; [| apply (t_alt_wall' ch (bs0 ++ bs1) T Hnb)].
eapply (rz_writev_dep regs pc mem rom model fd ch [(b0, l0); (b1, l1)] (bs0 ++ bs1)
(fun n => t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T) Hh Hlz Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
apply copy_iovecs_2; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hc.
Qed.
Lemma rz_writev1_wall : forall regs pc mem rom model fd ch (b0 l0 : word) bs0 T,
m_halted model = None -> m_vm_lazy model = [] ->
bv_unsigned (getr regs 17) = 66%Z ->
fdchan fd ch model -> fd32 fd = fd ->
getr regs 10 = fd ->
getr regs 12 = Z_to_bv 64 1 ->
ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
access_okb (getr regs 11) 16 = true ->
access_okb b0 (bv_unsigned l0) = true ->
(1 <= bv_unsigned l0 <= MAX_RW_COUNT)%Z ->
(forall n, (1 <= n)%nat -> (n <= length bs0)%nat ->
realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
(t_emit (map (WriteEv ch) (skipn n bs0)) T)) ->
realizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) bs0) T).
Proof.
intros regs pc mem rom model fd ch b0 l0 bs0 T Hh Hlz Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hc.
rewrite <- read_bytes_map_read_byte in Hbs0.
pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0).
unfold MAX_RW_COUNT in Htot.
assert (Hnb : (1 <= length bs0)%nat) by lia.
eapply rz_conseq; [| apply (t_alt_wall' ch bs0 T Hnb)].
eapply (rz_writev_dep regs pc mem rom model fd ch [(b0, l0)] bs0
(fun n => t_emit (map (WriteEv ch) (skipn n bs0)) T) Hh Hlz Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
apply copy_iovecs_1; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hc.
Qed.
End e.
End d.
Notation ZV z := (Z_to_bv 64 z) (only parsing).
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma zv_mod : forall a, Z_to_bv 64 (a mod 2^64) = Z_to_bv 64 a.
Proof. intros a. apply Z_to_bv64_eq_mod. apply Z.mod_mod. lia. Qed.
Lemma u_zv : forall a, bv_unsigned (Z_to_bv 64 a) = a mod 2^64.
Proof. intros a. rewrite Z_to_bv_unsigned. apply bv_wrap64_mod. Qed.
Lemma zv_addi : forall a k, v_addi (Z_to_bv 64 a) k = Z_to_bv 64 (a + k).
Proof. intros a k. unfold v_addi. rewrite u_zv. apply Z_to_bv64_eq_mod. rewrite Zplus_mod_idemp_l. reflexivity. Qed.
Lemma zv_add : forall a b, v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b. unfold v_add. rewrite !u_zv. apply Z_to_bv64_eq_mod. rewrite <- Zplus_mod. reflexivity. Qed.
Lemma zv_sub : forall a b, v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof. intros a b. unfold v_sub. rewrite !u_zv. apply Z_to_bv64_eq_mod. rewrite <- Zminus_mod. reflexivity. Qed.
Lemma zv_sltu : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
intros a b Ha Hb. unfold v_sltu, c_ltu, bv_ltu. rewrite !u_Z2bv by lia.
destruct (a <? b); reflexivity.
Qed.
Lemma zv_slli4 : forall a, 0 <= a -> v_slli (Z_to_bv 64 a) 4 = Z_to_bv 64 (16 * a).
Proof.
intros a Ha. unfold v_slli. rewrite u_zv. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
apply Z_to_bv64_eq_mod. rewrite Zmult_mod_idemp_l. f_equal. lia.
Qed.
Lemma zv_and_0_l : forall b, v_and (Z_to_bv 64 0) b = Z_to_bv 64 0.
Proof. intros b. unfold v_and. rewrite u_zv. rewrite Z.mod_0_l by lia. rewrite Z.land_0_l. reflexivity. Qed.
Lemma zv_and_m1_l : forall b, 0 <= b < 2^64 -> v_and (Z_to_bv 64 (0 - 1)) (Z_to_bv 64 b) = Z_to_bv 64 b.
Proof.
intros b Hb. unfold v_and. rewrite !u_zv. rewrite (Z.mod_small b) by lia.
replace ((0 - 1) mod 2^64) with (Z.ones 64) by reflexivity.
rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma zv_subw_small : forall a b, 0 <= b <= a -> a < 2^31 ->
v_subw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a - b).
Proof.
intros a b Hab Ha. unfold v_subw. rewrite !u_Z2bv by lia. f_equal.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma v_lw_id : forall x : word, bv_unsigned x < 2^31 -> v_lw x = x.
Proof.
intros x Hx. pose proof (u64_range x). unfold v_lw, bv_swrap, bv_wrap.
change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
rewrite Z.mod_small by lia. replace (bv_unsigned x + 2 ^ 31 - 2 ^ 31) with (bv_unsigned x) by lia.
apply Z_to_bv_bv_unsigned.
Qed.
Lemma c_eq_zv : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma c_ltu_zv : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 ->
c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma c_lts_zv_0 : forall a, 0 <= a < 2^63 -> c_lts (Z_to_bv 64 a) (Z_to_bv 64 0) = false.
Proof. intros a Ha. apply c_lts_pos_0. rewrite u_Z2bv by lia. lia. Qed.
Lemma sysret_ltu : forall n, 0 <= n < 2^32 ->
c_ltu (Z_to_bv 64 n) (v_addiw (v_lui (Z.shiftl (bv_signed (1048575%bv : bv 20)) 12)) (bv_signed (1%bv : bv 12))) = true.
Proof.
intros n Hn.
match goal with |- c_ltu _ ?x = true =>
let v := eval vm_compute in (bv_unsigned x) in
assert (Hx : bv_unsigned x = v) by (vm_compute; reflexivity);
unfold c_ltu, bv_ltu; rewrite Hx end.
rewrite u_Z2bv by lia. apply Z.ltb_lt. lia.
Qed.
Lemma fetch_lit : forall (p : word) (w : bv 32),
clookup src0tbl (bv_unsigned p) = Some (bv_unsigned w) ->
fetch_word src0segs p = Some w.
Proof.
intros p w H.
rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply src0tbl_ok. exact H.
Qed.
End f.
Ltac ftac := apply fetch_lit; vm_compute; reflexivity.
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_15a34 : fetch_word src0segs (0x15cf8%bv : word) = Some (0xfffff5b7%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15a34 : decode_any (0xfffff5b7%bv : bv 32) = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15a38 : fetch_word src0segs (0x15cfc%bv : word) = Some (0x0015859b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15a38 : decode_any (0x0015859b%bv : bv 32) = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15a3c : fetch_word src0segs (0x15d00%bv : word) = Some (0x02b56663%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15a3c : decode_any (0x02b56663%bv : bv 32) = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_15a68 : fetch_word src0segs (0x15d2c%bv : word) = Some (0x00008067%bv : bv 32).
Proof. ftac. Qed.
Lemma D_15a68 : decode_any (0x00008067%bv : bv 32) = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17b94 : fetch_word src0segs (0x18148%bv : word) = Some (0x00000073%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17b94 : decode_any (0x00000073%bv : bv 32) = Some (Ecall, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17b98 : fetch_word src0segs (0x1814c%bv : word) = Some (0xbadfd0ef%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17b98 : decode_any (0xbadfd0ef%bv : bv 32) = Some (Jal 1 2087852, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17b9c : fetch_word src0segs (0x18150%bv : word) = Some (0x09651863%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17b9c : decode_any (0x09651863%bv : bv 32) = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17ba0 : fetch_word src0segs (0x18154%bv : word) = Some (0x0584b503%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17ba0 : decode_any (0x0584b503%bv : bv 32) = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17bf0 : fetch_word src0segs (0x181a4%bv : word) = Some (0x00800713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17bf0 : decode_any (0x00800713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17bf4 : fetch_word src0segs (0x181a8%bv : word) = Some (0x000a0593%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17bf4 : decode_any (0x000a0593%bv : bv 32) = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17bf8 : fetch_word src0segs (0x181ac%bv : word) = Some (0x00e98733%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17bf8 : decode_any (0x00e98733%bv : bv 32) = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17bfc : fetch_word src0segs (0x181b0%bv : word) = Some (0x00073783%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17bfc : decode_any (0x00073783%bv : bv 32) = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c00 : fetch_word src0segs (0x181b4%bv : word) = Some (0x40ab0b33%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c00 : decode_any (0x40ab0b33%bv : bv 32) = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c04 : fetch_word src0segs (0x181b8%bv : word) = Some (0x0784a503%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c04 : decode_any (0x0784a503%bv : bv 32) = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c08 : fetch_word src0segs (0x181bc%bv : word) = Some (0x40c9093b%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c08 : decode_any (0x40c9093b%bv : bv 32) = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c0c : fetch_word src0segs (0x181c0%bv : word) = Some (0x40d787b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c0c : decode_any (0x40d787b3%bv : bv 32) = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c10 : fetch_word src0segs (0x181c4%bv : word) = Some (0x00f73023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c10 : decode_any (0x00f73023%bv : bv 32) = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c14 : fetch_word src0segs (0x181c8%bv : word) = Some (0x04200893%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c14 : decode_any (0x04200893%bv : bv 32) = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c18 : fetch_word src0segs (0x181cc%bv : word) = Some (0x00090613%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c18 : decode_any (0x00090613%bv : bv 32) = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c1c : fetch_word src0segs (0x181d0%bv : word) = Some (0x00000073%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c1c : decode_any (0x00000073%bv : bv 32) = Some (Ecall, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c20 : fetch_word src0segs (0x181d4%bv : word) = Some (0xb25fd0ef%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c20 : decode_any (0xb25fd0ef%bv : bv 32) = Some (Jal 1 2087716, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c24 : fetch_word src0segs (0x181d8%bv : word) = Some (0x000a0993%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c24 : decode_any (0x000a0993%bv : bv 32) = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c28 : fetch_word src0segs (0x181dc%bv : word) = Some (0xf7650ce3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c28 : decode_any (0xf7650ce3%bv : bv 32) = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c2c : fetch_word src0segs (0x181e0%bv : word) = Some (0x02054c63%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c2c : decode_any (0x02054c63%bv : bv 32) = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c30 : fetch_word src0segs (0x181e4%bv : word) = Some (0x0089b583%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c30 : decode_any (0x0089b583%bv : bv 32) = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c34 : fetch_word src0segs (0x181e8%bv : word) = Some (0x00a5b633%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c34 : decode_any (0x00a5b633%bv : bv 32) = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c38 : fetch_word src0segs (0x181ec%bv : word) = Some (0x00461a13%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c38 : decode_any (0x00461a13%bv : bv 32) = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c3c : fetch_word src0segs (0x181f0%bv : word) = Some (0x01498a33%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c3c : decode_any (0x01498a33%bv : bv 32) = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c40 : fetch_word src0segs (0x181f4%bv : word) = Some (0x000a3703%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c40 : decode_any (0x000a3703%bv : bv 32) = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c44 : fetch_word src0segs (0x181f8%bv : word) = Some (0x40c006b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c44 : decode_any (0x40c006b3%bv : bv 32) = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c48 : fetch_word src0segs (0x181fc%bv : word) = Some (0x00b6f6b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c48 : decode_any (0x00b6f6b3%bv : bv 32) = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c4c : fetch_word src0segs (0x18200%bv : word) = Some (0x40d506b3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c4c : decode_any (0x40d506b3%bv : bv 32) = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c50 : fetch_word src0segs (0x18204%bv : word) = Some (0x00d70733%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c50 : decode_any (0x00d70733%bv : bv 32) = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c54 : fetch_word src0segs (0x18208%bv : word) = Some (0x00ea3023%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c54 : decode_any (0x00ea3023%bv : bv 32) = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c58 : fetch_word src0segs (0x1820c%bv : word) = Some (0xf8a5fce3%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c58 : decode_any (0xf8a5fce3%bv : bv 32) = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c5c : fetch_word src0segs (0x18210%bv : word) = Some (0x01800713%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c5c : decode_any (0x01800713%bv : bv 32) = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl_bv. Qed.
Lemma F_17c60 : fetch_word src0segs (0x18214%bv : word) = Some (0xf95ff06f%bv : bv 32).
Proof. ftac. Qed.
Lemma D_17c60 : decode_any (0xf95ff06f%bv : bv 32) = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl_bv. Qed.
End h.
Ltac msteps_done :=
lazymatch goal with
| |- msteps _ (mkst _ ?p _ _) (mkst _ ?q _ _) =>
first [ apply mst_refl
| replace q with p by (symmetry; bveq); apply mst_refl ]
end.
Ltac gr :=
repeat first [ rewrite getr_same by reg_neq_tac
| rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition inW (SP : Z) (a : word) : Prop := SP + 8 <= bv_unsigned a < SP + 40.
Definition wl_kept (r : reg) : Prop :=
r <> 1%bv /\ r <> 10%bv /\ r <> 11%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv /\ r <> 15%bv
/\ r <> 17%bv /\ r <> 18%bv /\ r <> 19%bv /\ r <> 20%bv /\ r <> 22%bv.
Definition iov_mem (mem : word -> option byte) (SP c b0 l0 b1 l1 : Z) : Prop :=
(c = 2 -> rdn src0segs mem (Z_to_bv 64 (SP + 8)) 8 = Some (word_le8 (Z_to_bv 64 b0))
/\ rdn src0segs mem (Z_to_bv 64 (SP + 16)) 8 = Some (word_le8 (Z_to_bv 64 l0)))
/\ rdn src0segs mem (Z_to_bv 64 (SP + 24)) 8 = Some (word_le8 (Z_to_bv 64 b1))
/\ rdn src0segs mem (Z_to_bv 64 (SP + 32)) 8 = Some (word_le8 (Z_to_bv 64 l1)).
End j.
Ltac stepbt F D tac :=
chain_step;
[ reflexivity
| eapply step_branch_tk_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepbf F D tac :=
chain_step;
[ reflexivity
| eapply step_branch_ft_gen; [ exact F | reflexivity | exact D | tac ]
| step_simpl ].
Ltac stepld F D vv rdtac :=
chain_step;
[ reflexivity
| eapply (step_ld _ _ _ _ _ _ _ _ _ _ vv); [ exact F | reflexivity | exact D | rdtac | apply bytes_le_n_to_le_8 ]
| step_simpl ].
Section o. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma step_op_at : forall segs regs pc mem rom w op rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op op rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
alu64 op (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w op rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_op_gen segs regs pc mem rom w op rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
End o.
Ltac stepov F D vv tac :=
chain_step;
[ reflexivity
| eapply step_op_at with (v := vv);
[ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_subw (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) =
MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
rewrite (step_subw segs regs pc mem rom w rd rs1 rs2 Hf He Hd), Hrd, Hv. reflexivity.
Qed.
End s.
Ltac stepsubw F D vv tac :=
chain_step;
[ reflexivity
| eapply step_subw_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Ltac steplw F D vv rdtac valtac :=
chain_step;
[ reflexivity
| eapply (step_lw _ _ _ _ _ _ _ _ _ _ vv); [ exact F | reflexivity | exact D | rdtac | valtac ]
| step_simpl ].
Ltac stepsd F D aa vv atac vtac oktac :=
chain_step;
[ reflexivity
| eapply step_sd_at with (a := aa) (v := vv); [ exact F | reflexivity | exact D | atac | vtac | oktac ]
| step_simpl ].
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma wbytes_out : forall bs m (addr x : word),
bv_unsigned addr + Z.of_nat (length bs) <= 2^64 ->
(bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x) ->
wbytes m addr bs x = m x.
Proof.
intros bs m addr x Hnw [Hb|Ha].
- apply wbytes_below; [exact Hnw| exact Hb].
- apply wbytes_above. pose proof (u64_range x). lia.
Qed.
Lemma length_wle8 : forall v : word, length (word_to_le_bytes 8 v) = 8%nat.
Proof. intros v. rewrite length_N_to_le_bytes. reflexivity. Qed.
Section u.
Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
Variables (SP F c b0 l0 b1 l1 rem n : Z) (fd : word) (fdbs : list byte).
Definition body_pre : Prop :=
(c = 1 \/ c = 2)
/\ (0 <= SP /\ SP + 40 <= 2^64)
/\ (0 <= b0 /\ 0 <= l0 /\ b0 + l0 <= 2^64)
/\ (0 <= b1 /\ 0 <= l1 /\ b1 + l1 <= 2^64)
/\ rem = (if c =? 2 then l0 else 0) + l1
/\ (1 <= n < rem)
/\ rem <= 2^25
/\ getr regs 2 = Z_to_bv 64 SP
/\ getr regs 9 = Z_to_bv 64 F
/\ getr regs 18 = Z_to_bv 64 c
/\ getr regs 19 = Z_to_bv 64 (SP + 40 - 16 * c)
/\ getr regs 22 = Z_to_bv 64 rem
/\ getr regs 10 = Z_to_bv 64 n
/\ store_ok src0segs mem (Z_to_bv 64 (SP + 8)) 32 = true
/\ iov_mem mem SP c b0 l0 b1 l1
/\ rdn src0segs mem (Z_to_bv 64 (F + 120)) 4 = Some fdbs
/\ bytes_le_to_Z fdbs = bv_unsigned fd
/\ bv_unsigned fd < 2^31
/\ (F + 124 <= SP + 8 \/ SP + 40 <= F + 120)
/\ (0 <= F /\ F + 124 <= 2^64).
Hypothesis HP : body_pre.
Ltac open_pre :=
destruct HP as (Hc & HSP & Hb0 & Hb1 & Hrem & Hn & Hrem25 & R2 & R9 & R18 & R19 & R22 & R10 & Hst & Hiov
& Hfd & Hfdv & Hfd31 & HFW & HF).
Definition body_post (c' : Z) (b0' l0' b1' l1' : Z) : Prop :=
exists regs' mem',
msteps src0segs (mkst regs (Z_to_bv 64 0x181e0) mem rom) (mkst regs' (Z_to_bv 64 0x181d0) mem' rom)
/\ getr regs' 2 = Z_to_bv 64 SP /\ getr regs' 9 = Z_to_bv 64 F
/\ getr regs' 18 = Z_to_bv 64 c' /\ getr regs' 12 = Z_to_bv 64 c'
/\ getr regs' 20 = Z_to_bv 64 (SP + 40 - 16 * c') /\ getr regs' 11 = Z_to_bv 64 (SP + 40 - 16 * c')
/\ getr regs' 22 = Z_to_bv 64 (rem - n) /\ getr regs' 10 = fd /\ getr regs' 17 = Z_to_bv 64 66
/\ (forall r, wl_kept r -> getr regs' r = getr regs r)
/\ (forall a, ~ inW SP a -> mem' a = mem a)
/\ store_ok src0segs mem' (Z_to_bv 64 (SP + 8)) 32 = true
/\ iov_mem mem' SP c' b0' l0' b1' l1'.
Lemma body_A : c = 2 -> n <= l0 -> body_post 2 (b0 + n) (l0 - n) b1 l1.
Proof.
intros Hc2 Hnl. open_pre. rewrite Hc2 in R18, R19, Hrem, Hiov. cbn in Hrem. destruct Hiov as [H01 [Hm1 Hl1]]. destruct (H01 eq_refl) as [Hm0 Hl0].
unfold body_post. eexists. eexists. split.
- norm_pc.
stepbf F_17c2c D_17c2c ltac:(rewrite R10, getr_zero; apply c_lts_zv_0; lia).
stepld F_17c30 D_17c30 (Z_to_bv 64 l0) ltac:(rewrite R19; imm_norm; rewrite zv_addi; replace (SP + 40 - 16*2 + 8) with (SP + 16) by lia; exact Hl0).
stepov F_17c34 D_17c34 (Z_to_bv 64 0)
ltac:(gr; rewrite R10, alu_sltu, zv_sltu by lia; rewrite (proj2 (Z.ltb_ge l0 n)) by lia; reflexivity).
stepiv F_17c38 D_17c38 (Z_to_bv 64 0) ltac:(gr; imm_norm; rewrite zv_slli4 by lia; reflexivity).
stepiv F_17c3c D_17c3c (Z_to_bv 64 (SP + 8)) ltac:(gr; rewrite R19, zv_add; f_equal; lia).
stepld F_17c40 D_17c40 (Z_to_bv 64 b0) ltac:(gr; imm_norm; rewrite zv_addi, Z.add_0_r; exact Hm0).
stepiv F_17c44 D_17c44 (Z_to_bv 64 0) ltac:(gr; rewrite zv_sub; reflexivity).
stepov F_17c48 D_17c48 (Z_to_bv 64 0) ltac:(gr; rewrite alu_and; apply zv_and_0_l).
stepiv F_17c4c D_17c4c (Z_to_bv 64 n) ltac:(gr; rewrite R10, zv_sub; f_equal; lia).
stepiv F_17c50 D_17c50 (Z_to_bv 64 (b0 + n)) ltac:(gr; rewrite zv_add; reflexivity).
stepsd F_17c54 D_17c54 (Z_to_bv 64 (SP + 8)) (Z_to_bv 64 (b0 + n))
ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia)
ltac:(gr; reflexivity)
ltac:(apply (store_ok_sub src0segs _ (Z_to_bv 64 (SP + 8)) _ 32 8); [rewrite u_Z2bv by lia; lia | exact Hst | lia | rewrite !u_Z2bv by lia; lia]).
stepbt F_17c58 D_17c58 ltac:(gr; rewrite R10; cbn [branch_taken]; unfold bv_ltu; rewrite !u_Z2bv by lia; apply negb_true_iff; apply Z.ltb_ge; lia).
stepiv F_17bf0 D_17bf0 (Z_to_bv 64 8) ltac:(gr; bveq).
stepiv F_17bf4 D_17bf4 (Z_to_bv 64 (SP + 8)) ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia).
stepiv F_17bf8 D_17bf8 (Z_to_bv 64 (SP + 16)) ltac:(gr; rewrite R19, zv_add; f_equal; lia).
stepld F_17bfc D_17bfc (Z_to_bv 64 l0)
ltac:(gr; imm_norm; rewrite zv_addi, Z.add_0_r;
rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia); exact Hl0).
stepiv F_17c00 D_17c00 (Z_to_bv 64 (rem - n)) ltac:(gr; rewrite R22, R10, zv_sub; reflexivity).
steplw F_17c04 D_17c04 fd
ltac:(gr; rewrite R9; imm_norm; rewrite zv_addi;
rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia); exact Hfd)
ltac:(exact Hfdv).
rewrite (v_lw_id fd Hfd31).
stepsubw F_17c08 D_17c08 (Z_to_bv 64 2) ltac:(gr; rewrite R18, zv_subw_small by lia; reflexivity).
stepiv F_17c0c D_17c0c (Z_to_bv 64 (l0 - n)) ltac:(gr; rewrite zv_sub; reflexivity).
stepsd F_17c10 D_17c10 (Z_to_bv 64 (SP + 16)) (Z_to_bv 64 (l0 - n))
ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia)
ltac:(gr; reflexivity)
ltac:(eapply store_ok_mono; [apply wbytes_grows|];
apply (store_ok_sub src0segs _ (Z_to_bv 64 (SP + 8)) _ 32 8); [rewrite u_Z2bv by lia; lia | exact Hst | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]).
stepiv F_17c14 D_17c14 (Z_to_bv 64 66) ltac:(gr; bveq).
stepiv F_17c18 D_17c18 (Z_to_bv 64 2) ltac:(gr; bveq).
msteps_done.
- split; [gr; exact R2|]. split; [gr; exact R9|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; f_equal; lia|]. split; [gr; f_equal; lia|].
split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split.
{ intros r Hr. destruct Hr as (K1 & K10 & K11 & K12 & K13 & K14 & K15 & K17 & K18 & K19 & K20 & K22).
rewrite !getr_other by assumption. reflexivity. }
split.
{ intros a Ha. unfold inW in Ha. rewrite !wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia). reflexivity. }
split.
{ eapply store_ok_mono; [apply wbytes_grows|]. eapply store_ok_mono; [apply wbytes_grows|]. exact Hst. }
unfold iov_mem. split; [intros _; split|split].
+ rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia).
apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
+ apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
+ rewrite !rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia). exact Hm1.
+ rewrite !rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia). exact Hl1.
Qed.
Lemma body_B : c = 2 -> l0 < n -> body_post 1 0 0 (b1 + (n - l0)) (l1 - (n - l0)).
Proof.
intros Hc2 Hnl. open_pre. rewrite Hc2 in R18, R19, Hrem, Hiov. cbn in Hrem. destruct Hiov as [H01 [Hm1 Hl1]]. destruct (H01 eq_refl) as [Hm0 Hl0].
unfold body_post. eexists. eexists. split.
- norm_pc.
stepbf F_17c2c D_17c2c ltac:(rewrite R10, getr_zero; apply c_lts_zv_0; lia).
stepld F_17c30 D_17c30 (Z_to_bv 64 l0) ltac:(rewrite R19; imm_norm; rewrite zv_addi; replace (SP + 40 - 16*2 + 8) with (SP + 16) by lia; exact Hl0).
stepov F_17c34 D_17c34 (Z_to_bv 64 1)
ltac:(gr; rewrite R10, alu_sltu, zv_sltu by lia; rewrite (proj2 (Z.ltb_lt l0 n)) by lia; reflexivity).
stepiv F_17c38 D_17c38 (Z_to_bv 64 16) ltac:(gr; imm_norm; rewrite zv_slli4 by lia; reflexivity).
stepiv F_17c3c D_17c3c (Z_to_bv 64 (SP + 24)) ltac:(gr; rewrite R19, zv_add; f_equal; lia).
stepld F_17c40 D_17c40 (Z_to_bv 64 b1) ltac:(gr; imm_norm; rewrite zv_addi, Z.add_0_r; exact Hm1).
stepiv F_17c44 D_17c44 (Z_to_bv 64 (0 - 1)) ltac:(gr; rewrite zv_sub; reflexivity).
stepov F_17c48 D_17c48 (Z_to_bv 64 l0) ltac:(gr; rewrite alu_and; apply zv_and_m1_l; lia).
stepiv F_17c4c D_17c4c (Z_to_bv 64 (n - l0)) ltac:(gr; rewrite R10, zv_sub; reflexivity).
stepiv F_17c50 D_17c50 (Z_to_bv 64 (b1 + (n - l0))) ltac:(gr; rewrite zv_add; reflexivity).
stepsd F_17c54 D_17c54 (Z_to_bv 64 (SP + 24)) (Z_to_bv 64 (b1 + (n - l0)))
ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia)
ltac:(gr; reflexivity)
ltac:(apply (store_ok_sub src0segs _ (Z_to_bv 64 (SP + 8)) _ 32 8); [rewrite u_Z2bv by lia; lia | exact Hst | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]).
stepbf F_17c58 D_17c58 ltac:(gr; rewrite R10; cbn [branch_taken]; unfold bv_ltu; rewrite !u_Z2bv by lia; apply negb_false_iff; apply Z.ltb_lt; lia).
stepiv F_17c5c D_17c5c (Z_to_bv 64 24) ltac:(gr; bveq).
stepj F_17c60 D_17c60.
stepiv F_17bf4 D_17bf4 (Z_to_bv 64 (SP + 24)) ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia).
stepiv F_17bf8 D_17bf8 (Z_to_bv 64 (SP + 32)) ltac:(gr; rewrite R19, zv_add; f_equal; lia).
stepld F_17bfc D_17bfc (Z_to_bv 64 l1)
ltac:(gr; imm_norm; rewrite zv_addi, Z.add_0_r;
rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia); exact Hl1).
stepiv F_17c00 D_17c00 (Z_to_bv 64 (rem - n)) ltac:(gr; rewrite R22, R10, zv_sub; reflexivity).
steplw F_17c04 D_17c04 fd
ltac:(gr; rewrite R9; imm_norm; rewrite zv_addi;
rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia); exact Hfd)
ltac:(exact Hfdv).
rewrite (v_lw_id fd Hfd31).
stepsubw F_17c08 D_17c08 (Z_to_bv 64 1) ltac:(gr; rewrite R18, zv_subw_small by lia; reflexivity).
stepiv F_17c0c D_17c0c (Z_to_bv 64 (l1 - (n - l0))) ltac:(gr; rewrite zv_sub; reflexivity).
stepsd F_17c10 D_17c10 (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 (l1 - (n - l0)))
ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia)
ltac:(gr; reflexivity)
ltac:(eapply store_ok_mono; [apply wbytes_grows|];
apply (store_ok_sub src0segs _ (Z_to_bv 64 (SP + 8)) _ 32 8); [rewrite u_Z2bv by lia; lia | exact Hst | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]).
stepiv F_17c14 D_17c14 (Z_to_bv 64 66) ltac:(gr; bveq).
stepiv F_17c18 D_17c18 (Z_to_bv 64 1) ltac:(gr; bveq).
msteps_done.
- split; [gr; exact R2|]. split; [gr; exact R9|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; f_equal; lia|]. split; [gr; f_equal; lia|].
split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split.
{ intros r Hr. destruct Hr as (K1 & K10 & K11 & K12 & K13 & K14 & K15 & K17 & K18 & K19 & K20 & K22).
rewrite !getr_other by assumption. reflexivity. }
split.
{ intros a Ha. unfold inW in Ha. rewrite !wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia). reflexivity. }
split.
{ eapply store_ok_mono; [apply wbytes_grows|]. eapply store_ok_mono; [apply wbytes_grows|]. exact Hst. }
unfold iov_mem. split; [intros HX; lia|split].
+ rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia).
apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
+ apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
Qed.
Lemma body_C : c = 1 -> body_post 1 0 0 (b1 + n) (l1 - n).
Proof.
intros Hc1. open_pre. rewrite Hc1 in R18, R19, Hrem, Hiov. cbn in Hrem. destruct Hiov as [_ [Hm1 Hl1]].
unfold body_post. eexists. eexists. split.
- norm_pc.
stepbf F_17c2c D_17c2c ltac:(rewrite R10, getr_zero; apply c_lts_zv_0; lia).
stepld F_17c30 D_17c30 (Z_to_bv 64 l1) ltac:(rewrite R19; imm_norm; rewrite zv_addi; replace (SP + 40 - 16*1 + 8) with (SP + 32) by lia; exact Hl1).
stepov F_17c34 D_17c34 (Z_to_bv 64 0)
ltac:(gr; rewrite R10, alu_sltu, zv_sltu by lia; rewrite (proj2 (Z.ltb_ge l1 n)) by lia; reflexivity).
stepiv F_17c38 D_17c38 (Z_to_bv 64 0) ltac:(gr; imm_norm; rewrite zv_slli4 by lia; reflexivity).
stepiv F_17c3c D_17c3c (Z_to_bv 64 (SP + 24)) ltac:(gr; rewrite R19, zv_add; f_equal; lia).
stepld F_17c40 D_17c40 (Z_to_bv 64 b1) ltac:(gr; imm_norm; rewrite zv_addi, Z.add_0_r; exact Hm1).
stepiv F_17c44 D_17c44 (Z_to_bv 64 0) ltac:(gr; rewrite zv_sub; reflexivity).
stepov F_17c48 D_17c48 (Z_to_bv 64 0) ltac:(gr; rewrite alu_and; apply zv_and_0_l).
stepiv F_17c4c D_17c4c (Z_to_bv 64 n) ltac:(gr; rewrite R10, zv_sub; f_equal; lia).
stepiv F_17c50 D_17c50 (Z_to_bv 64 (b1 + n)) ltac:(gr; rewrite zv_add; reflexivity).
stepsd F_17c54 D_17c54 (Z_to_bv 64 (SP + 24)) (Z_to_bv 64 (b1 + n))
ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia)
ltac:(gr; reflexivity)
ltac:(apply (store_ok_sub src0segs _ (Z_to_bv 64 (SP + 8)) _ 32 8); [rewrite u_Z2bv by lia; lia | exact Hst | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]).
stepbt F_17c58 D_17c58 ltac:(gr; rewrite R10; cbn [branch_taken]; unfold bv_ltu; rewrite !u_Z2bv by lia; apply negb_true_iff; apply Z.ltb_ge; lia).
stepiv F_17bf0 D_17bf0 (Z_to_bv 64 8) ltac:(gr; bveq).
stepiv F_17bf4 D_17bf4 (Z_to_bv 64 (SP + 24)) ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia).
stepiv F_17bf8 D_17bf8 (Z_to_bv 64 (SP + 32)) ltac:(gr; rewrite R19, zv_add; f_equal; lia).
stepld F_17bfc D_17bfc (Z_to_bv 64 l1)
ltac:(gr; imm_norm; rewrite zv_addi, Z.add_0_r;
rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia); exact Hl1).
stepiv F_17c00 D_17c00 (Z_to_bv 64 (rem - n)) ltac:(gr; rewrite R22, R10, zv_sub; reflexivity).
steplw F_17c04 D_17c04 fd
ltac:(gr; rewrite R9; imm_norm; rewrite zv_addi;
rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia); exact Hfd)
ltac:(exact Hfdv).
rewrite (v_lw_id fd Hfd31).
stepsubw F_17c08 D_17c08 (Z_to_bv 64 1) ltac:(gr; rewrite R18, zv_subw_small by lia; reflexivity).
stepiv F_17c0c D_17c0c (Z_to_bv 64 (l1 - n)) ltac:(gr; rewrite zv_sub; reflexivity).
stepsd F_17c10 D_17c10 (Z_to_bv 64 (SP + 32)) (Z_to_bv 64 (l1 - n))
ltac:(gr; imm_norm; rewrite zv_addi; f_equal; lia)
ltac:(gr; reflexivity)
ltac:(eapply store_ok_mono; [apply wbytes_grows|];
apply (store_ok_sub src0segs _ (Z_to_bv 64 (SP + 8)) _ 32 8); [rewrite u_Z2bv by lia; lia | exact Hst | rewrite !u_Z2bv by lia; lia | rewrite !u_Z2bv by lia; lia]).
stepiv F_17c14 D_17c14 (Z_to_bv 64 66) ltac:(gr; bveq).
stepiv F_17c18 D_17c18 (Z_to_bv 64 1) ltac:(gr; bveq).
msteps_done.
- split; [gr; exact R2|]. split; [gr; exact R9|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; f_equal; lia|]. split; [gr; f_equal; lia|].
split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split.
{ intros r Hr. destruct Hr as (K1 & K10 & K11 & K12 & K13 & K14 & K15 & K17 & K18 & K19 & K20 & K22).
rewrite !getr_other by assumption. reflexivity. }
split.
{ intros a Ha. unfold inW in Ha. rewrite !wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia). reflexivity. }
split.
{ eapply store_ok_mono; [apply wbytes_grows|]. eapply store_ok_mono; [apply wbytes_grows|]. exact Hst. }
unfold iov_mem. split; [intros HX; lia|split].
+ rewrite rdn_wbytes_out by (rewrite ?length_wle8, ?u_Z2bv by lia; lia).
apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
+ apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia.
Qed.
End u.
Section y.
Variables (regs : bvmap 5 word) (mem rom : word -> option byte) (n rem : Z).
Hypothesis Hn : 0 <= n < 2^32.
Hypothesis Hrem : 0 <= rem < 2^64.
Hypothesis R10 : getr regs 10 = Z_to_bv 64 n.
Hypothesis R22 : getr regs 22 = Z_to_bv 64 rem.
Lemma after_w2 :
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 0x181d4) mem rom)
(mkst regs' (Z_to_bv 64 (if n =? rem then 0x18154 else 0x181e0)) mem rom)
/\ getr regs' 19 = getr regs 20 /\ getr regs' 10 = Z_to_bv 64 n
/\ (forall r : reg, r <> 1%bv -> r <> 11%bv -> r <> 19%bv -> getr regs' r = getr regs r).
Proof.
eexists. split.
- norm_pc.
stepj F_17c20 D_17c20.
stepi F_15a34 D_15a34.
stepi F_15a38 D_15a38.
stepbt F_15a3c D_15a3c ltac:(gr; rewrite R10; apply sysret_ltu; lia).
stepjr F_15a68 D_15a68 (Z_to_bv 64 0x181d8) ltac:(gr; bveq).
stepiv F_17c24 D_17c24 (getr regs 20) ltac:(gr; imm_norm; apply v_addi_0).
destruct (Z.eqb_spec n rem) as [Heq|Hne].
+ stepbt F_17c28 D_17c28 ltac:(gr; rewrite R10, R22; cbn [branch_taken]; unfold bv_eqb; rewrite !u_Z2bv by lia; apply Z.eqb_eq; exact Heq).
msteps_done.
+ stepbf F_17c28 D_17c28 ltac:(gr; rewrite R10, R22; cbn [branch_taken]; unfold bv_eqb; rewrite !u_Z2bv by lia; apply Z.eqb_neq; exact Hne).
msteps_done.
- split; [gr; reflexivity|]. split; [gr; exact R10|].
intros r H1 H11 H19. rewrite !getr_other by assumption. reflexivity.
Qed.
Lemma after_w1 :
exists regs',
msteps src0segs (mkst regs (Z_to_bv 64 0x1814c) mem rom)
(mkst regs' (Z_to_bv 64 (if n =? rem then 0x18154 else 0x181e0)) mem rom)
/\ getr regs' 10 = Z_to_bv 64 n
/\ (forall r : reg, r <> 1%bv -> r <> 11%bv -> getr regs' r = getr regs r).
Proof.
eexists. split.
- norm_pc.
stepj F_17b98 D_17b98.
stepi F_15a34 D_15a34.
stepi F_15a38 D_15a38.
stepbt F_15a3c D_15a3c ltac:(gr; rewrite R10; apply sysret_ltu; lia).
stepjr F_15a68 D_15a68 (Z_to_bv 64 0x18150) ltac:(gr; bveq).
destruct (Z.eqb_spec n rem) as [Heq|Hne].
+ stepbf F_17b9c D_17b9c ltac:(gr; rewrite R10, R22; cbn [branch_taken]; unfold bv_eqb; rewrite !u_Z2bv by lia; apply negb_false_iff; apply Z.eqb_eq; exact Heq).
msteps_done.
+ stepbt F_17b9c D_17b9c ltac:(gr; rewrite R10, R22; cbn [branch_taken]; unfold bv_eqb; rewrite !u_Z2bv by lia; apply negb_true_iff; apply Z.eqb_neq; exact Hne).
msteps_done.
- split; [gr; exact R10|].
intros r H1 H11. rewrite !getr_other by assumption. reflexivity.
Qed.
End y.
Lemma ms_read_u64_of_rdn : forall regs pc mem a w,
rdn src0segs mem a 8 = Some (word_le8 w) ->
ms_read_u64 (pend_at regs pc mem (seg_rom src0segs)) a = Some w.
Proof.
intros regs pc mem a w H. unfold ms_read_u64.
rewrite (ms_read_bytes_rdn src0segs) by reflexivity. cbn [ms_mem pend_at].
change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H. f_equal.
change (le_bytes_to_word (word_le8 w)) with (Z_to_bv 64 (bytes_le_to_Z (word_le8 w))). rewrite bytes_le_n_to_le_8. apply Z_to_bv_bv_unsigned.
Qed.
Lemma ms_read_bytes_of_rdn : forall regs pc mem a (l : word) bs,
rdn src0segs mem a (word_to_nat l) = Some bs ->
ms_read_bytes (pend_at regs pc mem (seg_rom src0segs)) a l = Some bs.
Proof.
intros regs pc mem a l bs H. rewrite (ms_read_bytes_rdn src0segs) by reflexivity.
cbn [ms_mem pend_at]. exact H.
Qed.
Lemma word_to_nat_zv : forall z, 0 <= z < 2^64 -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof. intros z Hz. unfold word_to_nat. rewrite u_Z2bv by lia. reflexivity. Qed.
Lemma rdn_agree : forall (m m0 : word -> option byte) (a : Z) (k : nat) bs,
0 <= a -> a + Z.of_nat k <= 2^64 ->
(forall x : word, a <= bv_unsigned x < a + Z.of_nat k -> m x = m0 x) ->
rdn src0segs m0 (Z_to_bv 64 a) k = Some bs -> rdn src0segs m (Z_to_bv 64 a) k = Some bs.
Proof.
intros m m0 a k bs Ha Hk Hag H. destruct k as [|k]; [cbn in H |- *; exact H|].
rewrite <- H. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
intros x Hx. apply Hag. exact Hx.
Qed.
Lemma zv_add_nat : forall a k, (Z_to_bv 64 a + nat_to_word k)%bv = Z_to_bv 64 (a + Z.of_nat k).
Proof.
intros a k. unfold nat_to_word. apply bv_eq.
rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma rdn_advance : forall m a l bs k,
0 <= a -> 0 <= l -> a + l <= 2^64 -> (Z.of_nat k <= l) ->
rdn src0segs m (Z_to_bv 64 a) (Z.to_nat l) = Some bs ->
rdn src0segs m (Z_to_bv 64 (a + Z.of_nat k)) (Z.to_nat (l - Z.of_nat k)) = Some (skipn k bs).
Proof.
intros m a l bs k Ha Hl Hal Hk H.
rewrite <- zv_add_nat. replace (Z.to_nat (l - Z.of_nat k)) with (Z.to_nat l - k)%nat by lia.
apply rdn_skipn; [exact H| lia].
Qed.
Section a0.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlz : m_vm_lazy model = [].
Variables (fd ch : word).
Hypothesis Hfdc : fdchan fd ch model.
Hypothesis H32 : fd32 fd = fd.
Hypothesis Hfd31 : bv_unsigned fd < 2^31.
Variables (SP F : Z) (fdbs : list byte) (mem0 : word -> option byte) (regsK : bvmap 5 word) (T : TSet).
Hypothesis HSP : 0 <= SP /\ SP + 40 <= 2^47.
Hypothesis HF : 0 <= F /\ F + 124 <= 2^64.
Hypothesis HFW : F + 124 <= SP + 8 \/ SP + 40 <= F + 120.
Hypothesis Hfd : rdn src0segs mem0 (Z_to_bv 64 (F + 120)) 4 = Some fdbs.
Hypothesis Hfdv : bytes_le_to_Z fdbs = bv_unsigned fd.
Hypothesis HK : forall regs' mem',
(forall r, wl_kept r -> getr regs' r = getr regsK r) ->
getr regs' 17 = Z_to_bv 64 66 ->
(forall a, ~ inW SP a -> mem' a = mem0 a) ->
store_ok src0segs mem' (Z_to_bv 64 (SP + 8)) 32 = true ->
realizes src0segs (mkCfg (mkst regs' (Z_to_bv 64 0x18154) mem' (seg_rom src0segs)) model) T.
Let rom := seg_rom src0segs.
Definition wl_inv (ri : reg) (regs : bvmap 5 word) (mem : word -> option byte)
(c b0 l0 b1 l1 : Z) (bs0 bs1 : list byte) : Prop :=
(c = 1 \/ c = 2)
/\ 0 <= b0 /\ 0 <= l0 /\ b0 + l0 <= 2^47 /\ (b0 + l0 <= SP + 8 \/ SP + 40 <= b0)
/\ 0 <= b1 /\ 0 <= l1 /\ b1 + l1 <= 2^47 /\ (b1 + l1 <= SP + 8 \/ SP + 40 <= b1)
/\ 1 <= (if c =? 2 then l0 else 0) + l1 <= 2^25
/\ getr regs 2 = Z_to_bv 64 SP /\ getr regs 9 = Z_to_bv 64 F
/\ getr regs 18 = Z_to_bv 64 c /\ getr regs 12 = Z_to_bv 64 c
/\ getr regs ri = Z_to_bv 64 (SP + 40 - 16 * c) /\ getr regs 11 = Z_to_bv 64 (SP + 40 - 16 * c)
/\ getr regs 22 = Z_to_bv 64 ((if c =? 2 then l0 else 0) + l1)
/\ getr regs 10 = fd /\ getr regs 17 = Z_to_bv 64 66
/\ (forall r, wl_kept r -> getr regs r = getr regsK r)
/\ (forall a, ~ inW SP a -> mem a = mem0 a)
/\ store_ok src0segs mem (Z_to_bv 64 (SP + 8)) 32 = true
/\ iov_mem mem SP c b0 l0 b1 l1
/\ (c = 2 -> rdn src0segs mem0 (Z_to_bv 64 b0) (Z.to_nat l0) = Some bs0)
/\ rdn src0segs mem0 (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1
/\ Z.of_nat (length bs0) = (if c =? 2 then l0 else 0) /\ Z.of_nat (length bs1) = l1.
Ltac access_ok_tac :=
unfold access_okb, TASK_SIZE; rewrite ?u_Z2bv by lia;
apply andb_true_intro; split; apply Z.leb_le; lia.
Lemma wl_node : forall ri pc regs mem c b0 l0 b1 l1 bs0 bs1 (TT : nat -> TSet),
wl_inv ri regs mem c b0 l0 b1 l1 bs0 bs1 ->
(forall n, (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
realizes src0segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
(t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T)) ->
realizes src0segs (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros ri pc regs mem c b0 l0 b1 l1 bs0 bs1 TT HI Hc.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & Rri & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1).
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (Hrd1 : rdn src0segs mem (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1).
{ apply (rdn_agree mem mem0); [lia|lia| |exact Hbs1]. intros x Hx. apply Hout. unfold inW. lia. }
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
eapply (rz_writev1_wall src0segs regs pc mem rom model fd ch (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs1 T Hh Hlz).
+ rewrite R17. reflexivity.
+ exact Hfdc. + exact H32. + exact R10. + exact R12.
+ rewrite R11. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 1) with (SP + 24) by lia. exact Hm1.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 1 + 8) with (SP + 32) by lia. exact Hl1.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd1.
+ rewrite R11. access_ok_tac.
+ access_ok_tac.
+ rewrite u_Z2bv by lia. unfold MAX_RW_COUNT. lia.
+ exact Hc.
- cbn in Hrem, R22, Hlen0. destruct (Hiov0 eq_refl) as [Hm0 Hl0].
assert (Hrd0 : rdn src0segs mem (Z_to_bv 64 b0) (Z.to_nat l0) = Some bs0).
{ apply (rdn_agree mem mem0); [lia|lia| |exact (Hbs0 eq_refl)]. intros x Hx. apply Hout. unfold inW. lia. }
eapply (rz_writev2_wall src0segs regs pc mem rom model fd ch (Z_to_bv 64 b0) (Z_to_bv 64 l0) (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs0 bs1 T Hh Hlz).
+ rewrite R17. reflexivity.
+ exact Hfdc. + exact H32. + exact R10. + exact R12.
+ rewrite R11. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2) with (SP + 8) by lia. exact Hm0.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2 + 8) with (SP + 16) by lia. exact Hl0.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2 + 16) with (SP + 24) by lia. exact Hm1.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 2 + 24) with (SP + 32) by lia. exact Hl1.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd0.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd1.
+ rewrite R11. access_ok_tac.
+ access_ok_tac.
+ access_ok_tac.
+ rewrite !u_Z2bv by lia. unfold MAX_RW_COUNT. lia.
+ exact Hc.
Qed.
Let INV := wl_inv.
Lemma skipn_all_nil : forall {A} n (l : list A), (length l <= n)%nat -> skipn n l = [].
Proof. intros A n l H. apply skipn_all2. exact H. Qed.
Lemma wl_done : forall regs mem (l : list byte) n,
(forall r, wl_kept r -> getr regs r = getr regsK r) -> getr regs 17 = Z_to_bv 64 66 ->
(forall a, ~ inW SP a -> mem a = mem0 a) -> store_ok src0segs mem (Z_to_bv 64 (SP + 8)) 32 = true ->
(length l <= n)%nat ->
realizes src0segs (mkCfg (mkst regs (Z_to_bv 64 0x18154) mem rom) model) (t_emit (map (WriteEv ch) (skipn n l)) T).
Proof.
intros regs mem l n Hk H17 Hout Hst Hn.
pose proof (HK regs mem Hk H17 Hout Hst) as HR.
rewrite skipn_all_nil by exact Hn. cbn [map].
eapply rz_conseq; [exact HR|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact HR.
Qed.
Lemma wl_loop2 : forall k regs mem c b0 l0 b1 l1 bs0 bs1,
(length (bs0 ++ bs1) <= k)%nat ->
INV 20%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
realizes src0segs (mkCfg (mkst regs (Z_to_bv 64 0x181d0) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
induction k as [|k IH]; intros regs mem c b0 l0 b1 l1 bs0 bs1 Hlen HI.
{ exfalso. rewrite length_app in Hlen.
destruct HI as (Hc12 & _ & _ & _ & _ & _ & _ & _ & _ & Hrem & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl0 & Hl1).
destruct Hc12 as [-> | ->]; cbn in Hrem, Hl0; lia. }
pose proof HI as HI'.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & R20 & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1).
replace (Z_to_bv 64 0x181d0 : word) with (0x181d0%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply rz_step; [exact Hh | exact Hlz | reflexivity | apply (step_ecall _ _ _ _ _ _ F_17c1c eq_refl) |].
change (realizes src0segs (mkCfg (pend_at regs (0x181d0%bv : word) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T)).
eapply (wl_node 20%bv _ regs mem c b0 l0 b1 l1 bs0 bs1 (fun _ => T) HI').
intros n Hn1 Hn2. replace (v_addi (0x181d0%bv : word) 4) with (Z_to_bv 64 0x181d4 : word) by (apply bv_eq; vm_compute; reflexivity).
set (rem := (if c =? 2 then l0 else 0) + l1) in *.
assert (Hlenall : Z.of_nat (length (bs0 ++ bs1)) = rem) by (rewrite length_app; lia).
destruct (after_w2 (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) mem rom (Z.of_nat n) rem
ltac:(lia) ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; exact R22))
as (regs1 & Hms1 & R19a & R10a & Hfr1).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms1 |].
destruct (Z.eqb_spec (Z.of_nat n) rem) as [Heq | Hne].
{
apply wl_done; [ | | exact Hout | exact Hst | lia].
- intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr.
- rewrite Hfr1 by reg_neq_tac. rewrite getr_other by reg_neq_tac. exact R17. }
assert (R2a : getr regs1 2 = Z_to_bv 64 SP) by (rewrite Hfr1 by reg_neq_tac; gr; exact R2).
assert (R9a : getr regs1 9 = Z_to_bv 64 F) by (rewrite Hfr1 by reg_neq_tac; gr; exact R9).
assert (R18a : getr regs1 18 = Z_to_bv 64 c) by (rewrite Hfr1 by reg_neq_tac; gr; exact R18).
assert (R19b : getr regs1 19 = Z_to_bv 64 (SP + 40 - 16 * c)) by (rewrite R19a; gr; exact R20).
assert (R22a : getr regs1 22 = Z_to_bv 64 rem) by (rewrite Hfr1 by reg_neq_tac; gr; exact R22).
assert (Hfd' : rdn src0segs mem (Z_to_bv 64 (F + 120)) 4 = Some fdbs).
{ apply (rdn_agree mem mem0); [lia|cbn; lia| |exact Hfd]. intros x Hx. apply Hout. unfold inW. cbn in Hx. lia. }
assert (Hkept1 : forall r, wl_kept r -> getr regs1 r = getr regsK r).
{ intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr. }
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (HiovM : iov_mem mem SP c b0 l0 b1 l1) by (split; [exact Hiov0| split; assumption]).
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0, rem. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
assert (HP : body_pre regs1 mem SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (body_C regs1 mem rom SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl)
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms2 |].
change (skipn n bs1) with ([] ++ skipn n bs1).
apply (IH regs2 mem2 1 0 0 (b1 + Z.of_nat n) (l1 - Z.of_nat n) [] (skipn n bs1)).
+ cbn [app]. rewrite length_skipn. lia.
+ unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]]
| match goal with |- ?g => idtac "LEFT:" g end ].
-
cbn in Hrem, R22, Hlen0, rem.
assert (HP : body_pre regs1 mem SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (Z_le_gt_dec (Z.of_nat n) l0) as [Hle | Hgt].
+
destruct (body_A regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. replace (n - length bs0)%nat with 0%nat by lia. cbn [skipn].
apply (IH regs2 mem2 2 (b0 + Z.of_nat n) (l0 - Z.of_nat n) b1 l1 (skipn n bs0) bs1).
* rewrite length_app, length_skipn in *. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]]
| match goal with |- ?g => idtac "LEFT:" g end ].
+
destruct (body_B regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. rewrite (skipn_all_nil n bs0) by lia. cbn [app].
change (skipn (n - length bs0) bs1) with ([] ++ skipn (n - length bs0) bs1).
apply (IH regs2 mem2 1 0 0 (b1 + (Z.of_nat n - l0)) (l1 - (Z.of_nat n - l0)) [] (skipn (n - length bs0) bs1)).
* cbn [app]. rewrite length_app, length_skipn in *. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] ]
| replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1]
| match goal with |- ?g => idtac "LEFT:" g end ].
Qed.
Lemma wl_entry_pend : forall regs mem c b0 l0 b1 l1 bs0 bs1,
INV 19%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
realizes src0segs (mkCfg (pend_at regs (Z_to_bv 64 0x18148) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros regs mem c b0 l0 b1 l1 bs0 bs1 HI.
pose proof HI as HI'.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & R19 & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1).
eapply (wl_node 19%bv _ regs mem c b0 l0 b1 l1 bs0 bs1 (fun _ => T) HI').
intros n Hn1 Hn2. replace (v_addi (Z_to_bv 64 0x18148 : word) 4) with (Z_to_bv 64 0x1814c : word) by (apply bv_eq; vm_compute; reflexivity).
set (rem := (if c =? 2 then l0 else 0) + l1) in *.
assert (Hlenall : Z.of_nat (length (bs0 ++ bs1)) = rem) by (rewrite length_app; lia).
destruct (after_w1 (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) mem rom (Z.of_nat n) rem
ltac:(lia) ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; exact R22))
as (regs1 & Hms1 & R10a & Hfr1).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms1 |].
assert (Hkept1 : forall r, wl_kept r -> getr regs1 r = getr regsK r).
{ intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr. }
destruct (Z.eqb_spec (Z.of_nat n) rem) as [Heq | Hne].
{ apply wl_done; [ exact Hkept1 | | exact Hout | exact Hst | lia].
rewrite Hfr1 by reg_neq_tac. rewrite getr_other by reg_neq_tac. exact R17. }
assert (R2a : getr regs1 2 = Z_to_bv 64 SP) by (rewrite Hfr1 by reg_neq_tac; gr; exact R2).
assert (R9a : getr regs1 9 = Z_to_bv 64 F) by (rewrite Hfr1 by reg_neq_tac; gr; exact R9).
assert (R18a : getr regs1 18 = Z_to_bv 64 c) by (rewrite Hfr1 by reg_neq_tac; gr; exact R18).
assert (R19b : getr regs1 19 = Z_to_bv 64 (SP + 40 - 16 * c)) by (rewrite Hfr1 by reg_neq_tac; gr; exact R19).
assert (R22a : getr regs1 22 = Z_to_bv 64 rem) by (rewrite Hfr1 by reg_neq_tac; gr; exact R22).
assert (Hfd' : rdn src0segs mem (Z_to_bv 64 (F + 120)) 4 = Some fdbs).
{ apply (rdn_agree mem mem0); [lia|cbn; lia| |exact Hfd]. intros x Hx. apply Hout. unfold inW. cbn in Hx. lia. }
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (HiovM : iov_mem mem SP c b0 l0 b1 l1) by (split; [exact Hiov0| split; assumption]).
destruct Hc12 as [-> | ->].
- cbn in Hrem, R22, Hlen0, rem. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
assert (HP : body_pre regs1 mem SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (body_C regs1 mem rom SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl)
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms2 |].
change (skipn n bs1) with ([] ++ skipn n bs1).
apply (wl_loop2 (length bs1) regs2 mem2 1 0 0 (b1 + Z.of_nat n) (l1 - Z.of_nat n) [] (skipn n bs1)).
+ cbn [app]. rewrite length_skipn. lia.
+ unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ].
- cbn in Hrem, R22, Hlen0, rem.
assert (HP : body_pre regs1 mem SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (Z_le_gt_dec (Z.of_nat n) l0) as [Hle | Hgt].
+ destruct (body_A regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. replace (n - length bs0)%nat with 0%nat by lia. cbn [skipn].
apply (wl_loop2 (length (bs0 ++ bs1)) regs2 mem2 2 (b0 + Z.of_nat n) (l0 - Z.of_nat n) b1 l1 (skipn n bs0) bs1).
* rewrite !length_app, length_skipn in *. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; first [ lia | apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ]
| apply rdn_advance; [lia|lia|lia|lia| first [exact Hbs1 | exact (Hbs0 eq_refl)]] ].
+ destruct (body_B regs1 mem rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply rz_msteps; [exact Hh | exact Hlz | exact Hms2 |].
rewrite skipn_app. rewrite (skipn_all_nil n bs0) by lia. cbn [app].
change (skipn (n - length bs0) bs1) with ([] ++ skipn (n - length bs0) bs1).
apply (wl_loop2 (length bs1) regs2 mem2 1 0 0 (b1 + (Z.of_nat n - l0)) (l1 - (Z.of_nat n - l0)) [] (skipn (n - length bs0) bs1)).
* cbn [app]. rewrite length_skipn. lia.
* unfold INV, wl_inv. cbn [Z.eqb Pos.eqb].
repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
all: first
[ rewrite Q22; f_equal; lia
| intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr
| intros a Ha; rewrite (Qout a Ha); apply Hout; exact Ha
| rewrite length_skipn; lia
| reflexivity
| intros HX; lia
| replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] ].
Qed.
Lemma wl_entry : forall regs mem c b0 l0 b1 l1 bs0 bs1,
INV 19%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
realizes src0segs (mkCfg (mkst regs (Z_to_bv 64 0x18148) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros regs mem c b0 l0 b1 l1 bs0 bs1 HI.
replace (Z_to_bv 64 0x18148 : word) with (0x18148%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply rz_step; [exact Hh | exact Hlz | reflexivity | apply (step_ecall _ _ _ _ _ _ F_17b94 eq_refl) |].
change (realizes src0segs (mkCfg (pend_at regs (0x18148%bv : word) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T)).
replace (0x18148%bv : word) with (Z_to_bv 64 0x18148 : word) by (apply bv_eq; vm_compute; reflexivity).
apply wl_entry_pend with (c := c) (b0 := b0) (l0 := l0) (b1 := b1) (l1 := l1). exact HI.
Qed.
End a0.
End t.
