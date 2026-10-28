(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0n YP0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0m YA0n YA0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AF0x.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AE3e.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable segs : list Segment.
Variable H : word -> bool.
Variable A : list (Z * Z).
Lemma srz_writev_dep : forall regs pc mem rom model fd ch iovs bs (T : nat -> TSet),
AI segs H A model ->
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
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) iovs n)) ->
(forall n model', (1 <= n)%nat -> (n <= length bs)%nat ->
AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model') (T n)) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model)
(t_alt (fun i : wr_index bs => t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
intros regs pc mem rom model fd ch iovs bs T HAI Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hav Hc.
destruct (node_writev_lazy segs H A regs pc mem rom model fd ch iovs bs HAI Hno Hfdc H32 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hav)
as [Hn Hs].
eapply (srz_node segs _ (wr_index bs) _ _ (fun i => T (proj1_sig i)) (wr_full bs Hnb) Hn).
intros [n [Hn1 Hn2]]. cbn [proj1_sig]. destruct (Hs (exist _ n (conj Hn1 Hn2))) as [HA Hsm]. cbn [proj1_sig] in HA, Hsm.
apply (Hc n _ Hn1 Hn2 HA Hsm).
Qed.
Lemma srz_writev2_wall : forall regs pc mem rom model fd ch (b0 l0 b1 l1 : word) bs0 bs1 T,
AI segs H A model ->
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
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) [(b0, l0); (b1, l1)] n)) ->
(forall n model', (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model')
(t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T)) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros regs pc mem rom model fd ch b0 l0 b1 l1 bs0 bs1 T
HAI Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hav Hc.
rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
unfold MAX_RW_COUNT in Htot.
assert (Hnb : (1 <= length (bs0 ++ bs1))%nat) by lia.
eapply srz_conseq; [| apply (t_alt_wall' ch (bs0 ++ bs1) T Hnb)].
eapply (srz_writev_dep regs pc mem rom model fd ch [(b0, l0); (b1, l1)] (bs0 ++ bs1)
(fun n => t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T) HAI Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
apply copy_iovecs_2; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hav.
- exact Hc.
Qed.
Lemma srz_writev1_wall : forall regs pc mem rom model fd ch (b0 l0 : word) bs0 T,
AI segs H A model ->
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
ranges_avoid H (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12) [(b0, l0)] n)) ->
(forall n model', (1 <= n)%nat -> (n <= length bs0)%nat ->
AI segs H A model' -> same_but_materialized model model' ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model')
(t_emit (map (WriteEv ch) (skipn n bs0)) T)) ->
srealizes segs (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) bs0) T).
Proof.
intros regs pc mem rom model fd ch b0 l0 bs0 T HAI Hno Hfdc H32 Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hav Hc.
rewrite <- read_bytes_map_read_byte in Hbs0.
pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
pose proof (read_bytes_map_length _ _ _ _ Hbs0).
unfold MAX_RW_COUNT in Htot.
assert (Hnb : (1 <= length bs0)%nat) by lia.
eapply srz_conseq; [| apply (t_alt_wall' ch bs0 T Hnb)].
eapply (srz_writev_dep regs pc mem rom model fd ch [(b0, l0)] bs0
(fun n => t_emit (map (WriteEv ch) (skipn n bs0)) T) HAI Hno Hfdc H32 Hfd).
- rewrite Hcnt. reflexivity.
- rewrite Hcnt. cbv. discriminate.
- rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
apply copy_iovecs_1; try assumption; lia.
- rewrite Hcnt. exact Hiok.
- cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
- exact Hg.
- cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
- lia.
- exact Hav.
- exact Hc.
Qed.
End e.
Section f.
Variable W : world tfibsegs.
Local Notation HH := (w_H W).
Local Notation AIW md := (AI tfibsegs (w_H W) (w_A W) md).
Lemma fdchan_sbm : forall fd ch m m', fdchan fd ch m -> same_but_materialized m m' -> fdchan fd ch m'.
Proof.
intros fd ch m m' Hf Hs. unfold same_but_materialized in Hs. rewrite Hs.
destruct m as [fds [maps lazy mat] io fs proc lim tm sg sc]; exact Hf.
Qed.
Lemma mrestrict_vis : forall (m : word -> option byte) (x : word), HH x = false -> mrestrict HH m x = m x.
Proof. intros m x Hx. unfold mrestrict. rewrite Hx. reflexivity. Qed.
Lemma rdn_vis : forall (m : word -> option byte) (a : Z) (k : nat) bs,
0 <= a -> a + Z.of_nat k <= 2^64 ->
(forall x : word, a <= bv_unsigned x < a + Z.of_nat k -> HH x = false) ->
rdn tfibsegs m (Z_to_bv 64 a) k = Some bs -> rdn tfibsegs (mrestrict HH m) (Z_to_bv 64 a) k = Some bs.
Proof.
intros m a k bs Ha Hk Hv Hr. apply (rdn_agree (mrestrict HH m) m a k bs Ha Hk); [|exact Hr].
intros x Hx. apply mrestrict_vis. apply Hv. exact Hx.
Qed.
Lemma srz_msteps_r : forall ms msr' model T,
AIW model ->
msteps tfibsegs (restrict HH ms) msr' ->
(forall model', AIW model' -> same_but_materialized model model' ->
srealizes tfibsegs (mkCfg (unrestrict HH (ms_mem ms) msr') model') T) ->
srealizes tfibsegs (mkCfg ms model) T.
Proof.
intros ms msr' model T HAI Hms Hk.
apply (SRr_srealizes tfibsegs W (mkCfg ms model)
(fun W' c' => W' = W /\ exists model', same_but_materialized model model' /\ c' = mkCfg (unrestrict HH (ms_mem ms) msr') model') T).
- eapply (SRr_msteps tfibsegs Hwx_tfa); [exact Hms|]. intros model' Hsbm Hcl. apply SRr_ret. split; [reflexivity|]. exists model'. split; [exact Hsbm|reflexivity].
- exact HAI.
- intros W' c' _ HAI' (-> & model' & Hsbm & ->). cbn [cfg_model] in HAI'. apply (Hk model' HAI' Hsbm).
Qed.
Lemma srz_step_r : forall ms msr' model T,
AIW model ->
ms_svc_pending ms = None ->
RiscvSemantics.step tfibsegs (restrict HH ms) = MachineOk msr' ->
(forall model', AIW model' -> same_but_materialized model model' ->
srealizes tfibsegs (mkCfg (unrestrict HH (ms_mem ms) msr') model') T) ->
srealizes tfibsegs (mkCfg ms model) T.
Proof.
intros ms msr' model T HAI Hsvc Hst Hk.
apply (SRr_srealizes tfibsegs W (mkCfg ms model)
(fun W' c' => W' = W /\ exists model', same_but_materialized model model' /\ c' = mkCfg (unrestrict HH (ms_mem ms) msr') model') T).
- eapply (SRr_step tfibsegs Hwx_tfa); [exact Hsvc | exact Hst |]. intros model' Hsbm. apply SRr_ret. split; [reflexivity|]. exists model'. split; [exact Hsbm|reflexivity].
- exact HAI.
- intros W' c' _ HAI' (-> & model' & Hsbm & ->). cbn [cfg_model] in HAI'. apply (Hk model' HAI' Hsbm).
Qed.
Definition vis_range (lo hi : Z) : Prop := forall x : word, lo <= bv_unsigned x < hi -> HH x = false.
Lemma restrict_pend : forall regs pc (m rom : word -> option byte),
restrict HH (pend_at regs pc m rom) = pend_at regs pc (mrestrict HH m) rom.
Proof. intros. reflexivity. Qed.
Lemma unrestrict_pend : forall regs pc (m rom : word -> option byte),
unrestrict HH m (pend_at regs pc (mrestrict HH m) rom) = pend_at regs pc m rom.
Proof.
intros regs pc m rom. rewrite <- restrict_pend.
exact (unrestrict_restrict HH (pend_at regs pc m rom)).
Qed.
Lemma unrestrict_mkst_restricted : forall regs pc (m rom : word -> option byte),
unrestrict HH m (mkst regs pc (mrestrict HH m) rom) = mkst regs pc m rom.
Proof.
intros regs pc m rom. rewrite <- restrict_mkst_fx.
exact (unrestrict_restrict HH (mkst regs pc m rom)).
Qed.
Lemma unrestrict_mkst : forall regs pc (full m' rom : word -> option byte),
unrestrict HH full (mkst regs pc m' rom) = mkst regs pc (munrestrict HH full m') rom.
Proof. intros. reflexivity. Qed.
Lemma munrestrict_vis : forall (full m' : word -> option byte) (x : word),
HH x = false -> munrestrict HH full m' x = m' x.
Proof. intros full m' x Hx. unfold munrestrict. rewrite Hx. reflexivity. Qed.
Lemma munrestrict_hid : forall (full m' : word -> option byte) (x : word),
HH x = true -> munrestrict HH full m' x = full x.
Proof. intros full m' x Hx. unfold munrestrict. rewrite Hx. reflexivity. Qed.
Lemma store_ok_agree : forall (m m' : word -> option byte) (k : nat) (a : word),
bv_unsigned a + Z.of_nat k <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> m' x = m x) ->
store_ok tfibsegs m a k = true -> store_ok tfibsegs m' a k = true.
Proof.
intros m m' k; induction k as [|k IH]; intros a Hk Hag Hst; [reflexivity|].
cbn [store_ok] in Hst |- *. unfold wview in Hst |- *.
pose proof (u64_range a) as Hra.
rewrite (Hag a) by lia.
assert (Hstep : store_ok tfibsegs m (a + 1)%bv k = true -> store_ok tfibsegs m' (a + 1)%bv k = true).
{ intros Hs. destruct k as [|k']; [reflexivity|].
assert (Hu : bv_unsigned (a + 1)%bv = bv_unsigned a + 1).
{ rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
replace (bv_unsigned (1%bv : word)) with 1 by reflexivity. apply Z.mod_small. lia. }
apply IH; [rewrite Hu; lia | | exact Hs]. intros x Hx. apply Hag. rewrite Hu in Hx. lia. }
destruct (m a) as [b|]; [exact (Hstep Hst)|].
destruct (find_segment tfibsegs (bv_unsigned a) 1) as [seg|]; [|discriminate].
destruct (seg_writable seg); [|discriminate].
destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))); [|discriminate].
exact (Hstep Hst).
Qed.
Lemma store_ok_vis_w : forall (m : word -> option byte) (k : nat) (a : word),
bv_unsigned a + Z.of_nat k <= 2^64 ->
(forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> HH x = false) ->
store_ok tfibsegs m a k = true -> store_ok tfibsegs (mrestrict HH m) a k = true.
Proof.
intros m k; induction k as [|k IH]; intros a Hk Hv Hst; [reflexivity|].
cbn [store_ok] in Hst |- *. unfold wview in Hst |- *.
pose proof (u64_range a) as Hra.
rewrite (mrestrict_vis m a) by (apply Hv; lia).
assert (Hstep : store_ok tfibsegs m (a + 1)%bv k = true -> store_ok tfibsegs (mrestrict HH m) (a + 1)%bv k = true).
{ intros Hs. destruct k as [|k']; [reflexivity|].
assert (Hu : bv_unsigned (a + 1)%bv = bv_unsigned a + 1).
{ rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
replace (bv_unsigned (1%bv : word)) with 1 by reflexivity. apply Z.mod_small. lia. }
apply IH; [rewrite Hu; lia | | exact Hs]. intros x Hx. apply Hv. rewrite Hu in Hx. lia. }
destruct (m a) as [b|]; [exact (Hstep Hst)|].
destruct (find_segment tfibsegs (bv_unsigned a) 1) as [seg|]; [|discriminate].
destruct (seg_writable seg); [|discriminate].
destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))); [|discriminate].
exact (Hstep Hst).
Qed.
Lemma store_ok_vis : forall (m : word -> option byte) (a : Z) (k : nat),
0 <= a -> a + Z.of_nat k <= 2^64 -> vis_range a (a + Z.of_nat k) ->
store_ok tfibsegs m (Z_to_bv 64 a) k = true -> store_ok tfibsegs (mrestrict HH m) (Z_to_bv 64 a) k = true.
Proof.
intros m a k Ha Hk Hv Hst. destruct k as [|k]; [reflexivity|].
apply store_ok_vis_w; rewrite ?u_Z2bv by lia; [lia | | exact Hst]. intros x Hx. apply Hv. lia.
Qed.
Lemma range_avoids_of_vis : forall (a : word) (n : nat) lo hi,
vis_range lo hi -> lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= hi -> hi <= 2^64 ->
range_avoids HH a n.
Proof.
intros a n lo hi Hv Hlo Hhi Hmax k Hk. apply Hv. unfold woff.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range a). rewrite Z.mod_small by lia. lia.
Qed.
Lemma ranges_avoid_of_elems : forall l,
(forall a n, In (a, n) l -> range_avoids HH a n) -> ranges_avoid HH l.
Proof. intros l Hl a n Hin. exact (Hl a n Hin). Qed.
Lemma copy_iovecs_accesses_in : forall mp k (a b : word) n,
bv_unsigned a + 16 * Z.of_nat k <= 2^64 ->
In (b, n) (copy_iovecs_accesses mp a k) ->
n = 16%nat /\ exists i, (i < k)%nat /\ bv_unsigned b = bv_unsigned a + 16 * Z.of_nat i.
Proof.
intros mp k; induction k as [|k IH]; intros a b n Hk Hin; cbn in Hin; [destruct Hin|].
destruct Hin as [Heq | Hin].
- injection Heq as <- <-. split; [reflexivity|]. exists 0%nat. split; [lia|]. lia.
- destruct (read_iovec_entry mp a) as [? len| |]; [|destruct Hin|destruct Hin].
destruct k as [|k']; [cbn in Hin; destruct Hin|].
assert (Hu : bv_unsigned (a + 16)%bv = bv_unsigned a + 16).
{ rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
pose proof (u64_range a). replace (bv_unsigned (16%bv : word)) with 16 by reflexivity.
apply Z.mod_small. lia. }
destruct (IH (a + 16)%bv b n ltac:(rewrite Hu; lia) Hin) as [Hn [i [Hi Hb]]].
split; [exact Hn|]. exists (S i). split; [lia|]. rewrite Hb, Hu. lia.
Qed.
Lemma import_iovecs_accesses_in : forall mp (a b cnt : word) n,
(1 <= bv_unsigned cnt <= 2)%Z ->
bv_unsigned a + 16 * bv_unsigned cnt <= 2^64 ->
In (b, n) (import_iovecs_accesses mp a cnt) ->
n = 16%nat /\ exists i, (Z.of_nat i < bv_unsigned cnt)%Z /\ bv_unsigned b = bv_unsigned a + 16 * Z.of_nat i.
Proof.
intros mp a b cnt n Hc Ha Hin. unfold import_iovecs_accesses in Hin.
destruct (bv_eqb cnt (Z_to_bv 64 1)) eqn:E1.
- apply bv_eqb_eq in E1. destruct (negb (access_okb a 16)); [destruct Hin|].
destruct Hin as [Heq|[]]. injection Heq as <- <-. split; [reflexivity|]. exists 0%nat. split; [lia|lia].
- destruct (bv_eqb cnt (Z_to_bv 64 0)); [destruct Hin|].
destruct (IOV_MAX <? bv_unsigned cnt)%Z; [destruct Hin|].
destruct (negb (access_okb a (16 * bv_unsigned cnt))); [destruct Hin|].
assert (Hw : Z.of_nat (word_to_nat cnt) = bv_unsigned cnt) by (unfold word_to_nat; rewrite Z2Nat.id; [reflexivity|lia]).
destruct (copy_iovecs_accesses_in mp (word_to_nat cnt) a b n ltac:(rewrite Hw; lia) Hin) as [Hn [i [Hi Hb]]].
split; [exact Hn|]. exists i. split; [lia|exact Hb].
Qed.
Lemma iov_prefix_accesses_in : forall iovs left (b : word) m,
In (b, m) (iov_prefix_accesses iovs left) -> exists len, In (b, len) iovs /\ (m <= word_to_nat len)%nat.
Proof.
induction iovs as [|[base len] rest IH]; intros left b m Hin.
- destruct left; cbn in Hin; destruct Hin.
- destruct left as [|left']; [cbn in Hin; destruct Hin|]. cbn [iov_prefix_accesses] in Hin.
pose proof (word_to_nat_bounded_eq_min len (S left')) as Hmin.
set (n := word_to_nat_bounded len (S left')) in *.
destruct (Nat.eqb n 0) eqn:En.
+ destruct (IH _ _ _ Hin) as [len' [Hi Hm]]. exists len'. split; [right; exact Hi | exact Hm].
+ destruct Hin as [Heq | Hin].
* injection Heq as <- <-. exists len. split; [left; reflexivity|]. rewrite Hmin. apply Nat.le_min_l.
* destruct (IH _ _ _ Hin) as [len' [Hi Hm]]. exists len'. split; [right; exact Hi | exact Hm].
Qed.
End f.
Section g.
Variable W : world tfibsegs.
Local Notation HH := (w_H W).
Local Notation AIW md := (AI tfibsegs (w_H W) (w_A W) md).
Variables (fd ch : word).
Variable model0 : Model.
Hypothesis Hfdc0 : fdchan fd ch model0.
Hypothesis H32 : fd32 fd = fd.
Hypothesis Hfd31 : bv_unsigned fd < 2^31.
Variables (SP F : Z) (fdbs : list byte) (mem0 : word -> option byte) (regsK : bvmap 5 word) (T : TSet).
Hypothesis HSP : 0 <= SP /\ SP + 40 <= 2^47.
Hypothesis HF : 0 <= F /\ F + 124 <= 2^64.
Hypothesis HFW : F + 124 <= SP + 8 \/ SP + 40 <= F + 120.
Hypothesis Hfd : rdn tfibsegs mem0 (Z_to_bv 64 (F + 120)) 4 = Some fdbs.
Hypothesis Hfdv : bytes_le_to_Z fdbs = bv_unsigned fd.
Hypothesis HvisW : vis_range W (SP + 8) (SP + 40).
Hypothesis HvisF : vis_range W (F + 120) (F + 124).
Hypothesis HK : forall regs' mem' model',
(forall r, wl_kept r -> getr regs' r = getr regsK r) ->
getr regs' 17 = Z_to_bv 64 66 ->
(forall a, ~ inW SP a -> mem' a = mem0 a) ->
store_ok tfibsegs mem' (Z_to_bv 64 (SP + 8)) 32 = true ->
AIW model' -> same_but_materialized model0 model' ->
srealizes tfibsegs (mkCfg (mkst regs' (Z_to_bv 64 0x92d80) mem' (seg_rom tfibsegs)) model') T.
Let rom := seg_rom tfibsegs.
Definition wl_invR (ri : reg) (regs : bvmap 5 word) (mem : word -> option byte)
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
/\ store_ok tfibsegs mem (Z_to_bv 64 (SP + 8)) 32 = true
/\ iov_mem mem SP c b0 l0 b1 l1
/\ (c = 2 -> rdn tfibsegs mem0 (Z_to_bv 64 b0) (Z.to_nat l0) = Some bs0)
/\ rdn tfibsegs mem0 (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1
/\ Z.of_nat (length bs0) = (if c =? 2 then l0 else 0) /\ Z.of_nat (length bs1) = l1
/\ (c = 2 -> vis_range W b0 (b0 + l0)) /\ vis_range W b1 (b1 + l1).
Lemma wl_done_r : forall regs mem model (l : list byte) n,
(forall r, wl_kept r -> getr regs r = getr regsK r) -> getr regs 17 = Z_to_bv 64 66 ->
(forall a, ~ inW SP a -> mem a = mem0 a) -> store_ok tfibsegs mem (Z_to_bv 64 (SP + 8)) 32 = true ->
AIW model -> same_but_materialized model0 model ->
(length l <= n)%nat ->
srealizes tfibsegs (mkCfg (mkst regs (Z_to_bv 64 0x92d80) mem rom) model) (t_emit (map (WriteEv ch) (skipn n l)) T).
Proof.
intros regs mem model l n Hk H17 Hout Hst HAI Hfdc Hn.
pose proof (HK regs mem model Hk H17 Hout Hst HAI Hfdc) as HR.
rewrite skipn_all_nil by exact Hn. cbn [map].
eapply srz_conseq; [exact HR|]. apply t_eq_sym. apply t_emit_nil_eq. eapply srealizes_nonempty. exact HR.
Qed.
Lemma wl_copyins_avoid : forall ri regs mem pc c b0 l0 b1 l1 bs0 bs1 n,
wl_invR ri regs mem c b0 l0 b1 l1 bs0 bs1 ->
ranges_avoid HH (writev_copyins (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11) (getr regs 12)
(if c =? 2 then [(Z_to_bv 64 b0, Z_to_bv 64 l0); (Z_to_bv 64 b1, Z_to_bv 64 l1)]
else [(Z_to_bv 64 b1, Z_to_bv 64 l1)]) n).
Proof.
intros ri regs mem pc c b0 l0 b1 l1 bs0 bs1 n HI.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & Rri & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1 & Hv0 & Hv1).
pose proof (u64_range fd) as Hfdr.
unfold writev_copyins. apply ranges_avoid_app; apply ranges_avoid_of_elems; intros a m Hin.
- rewrite R12, R11 in Hin.
assert (Hcv : iovcnt32 (Z_to_bv 64 c) = Z_to_bv 64 c) by (destruct Hc12 as [-> | ->]; reflexivity).
rewrite Hcv in Hin.
assert (Hcu : (1 <= bv_unsigned (Z_to_bv 64 c) <= 2)%Z) by (rewrite u_Z2bv by lia; lia).
assert (Hnw : bv_unsigned (Z_to_bv 64 (SP + 40 - 16 * c)) + 16 * bv_unsigned (Z_to_bv 64 c) <= 2 ^ 64) by (rewrite !u_Z2bv by lia; lia).
destruct (import_iovecs_accesses_in _ _ _ _ _ Hcu Hnw Hin) as [-> [i [Hi Hb]]].
rewrite !u_Z2bv in Hi, Hb by lia.
apply (range_avoids_of_vis W a 16 (SP + 8) (SP + 40) HvisW); cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *; lia.
- destruct (iov_prefix_accesses_in _ _ _ _ Hin) as [len [Hil Hm]].
destruct (Nat.eq_dec m 0) as [-> | Hm0]; [intros k Hk; exfalso; lia|].
destruct Hc12 as [-> | ->]; cbn [Z.eqb Pos.eqb] in Hil, Hv0.
+ destruct Hil as [Heq | []]. injection Heq as E1 E2. subst a len.
rewrite word_to_nat_zv in Hm by lia.
apply (range_avoids_of_vis W _ m b1 (b1 + l1) Hv1); rewrite ?u_Z2bv by lia; lia.
+ destruct Hil as [Heq | [Heq | []]]; injection Heq as E1 E2; subst a len; rewrite word_to_nat_zv in Hm by lia.
* apply (range_avoids_of_vis W _ m b0 (b0 + l0) (Hv0 eq_refl)); rewrite ?u_Z2bv by lia; lia.
* apply (range_avoids_of_vis W _ m b1 (b1 + l1) Hv1); rewrite ?u_Z2bv by lia; lia.
Qed.
Ltac access_ok_tac :=
unfold access_okb, TASK_SIZE; rewrite ?u_Z2bv by lia;
apply andb_true_intro; split; apply Z.leb_le; lia.
Lemma wl_node_r : forall ri pc regs mem model c b0 l0 b1 l1 bs0 bs1,
AIW model -> same_but_materialized model0 model ->
wl_invR ri regs mem c b0 l0 b1 l1 bs0 bs1 ->
(forall n model', (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
AIW model' -> same_but_materialized model model' ->
srealizes tfibsegs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model')
(t_emit (map (WriteEv ch) (skipn n (bs0 ++ bs1))) T)) ->
srealizes tfibsegs (mkCfg (pend_at regs pc mem rom) model) (t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros ri pc regs mem model c b0 l0 b1 l1 bs0 bs1 HAI Hfdc HI Hc.
pose proof (fun n => wl_copyins_avoid ri regs mem pc c b0 l0 b1 l1 bs0 bs1 n HI) as Hav.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & Rri & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1 & Hv0 & Hv1).
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (Hrd1 : rdn tfibsegs mem (Z_to_bv 64 b1) (Z.to_nat l1) = Some bs1).
{ apply (rdn_agree mem mem0); [lia|lia| |exact Hbs1]. intros x Hx. apply Hout. unfold inW. lia. }
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0. cbn [Z.eqb Pos.eqb] in Hav. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
eapply (srz_writev1_wall tfibsegs (w_H W) (w_A W) regs pc mem rom model fd ch (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs1 T HAI).
+ rewrite R17. reflexivity.
+ exact (fdchan_sbm _ _ _ _ Hfdc0 Hfdc). + exact H32. + exact R10. + exact R12.
+ rewrite R11. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 1) with (SP + 24) by lia. exact Hm1.
+ rewrite R11, u_Z2bv by lia. apply ms_read_u64_of_rdn. replace (SP + 40 - 16 * 1 + 8) with (SP + 32) by lia. exact Hl1.
+ apply ms_read_bytes_of_rdn. rewrite word_to_nat_zv by lia. exact Hrd1.
+ rewrite R11. access_ok_tac.
+ access_ok_tac.
+ rewrite u_Z2bv by lia. unfold MAX_RW_COUNT. lia.
+ intros n _ _. exact (Hav n).
+ exact Hc.
- cbn in Hrem, R22, Hlen0. cbn [Z.eqb Pos.eqb] in Hav. destruct (Hiov0 eq_refl) as [Hm0 Hl0].
assert (Hrd0 : rdn tfibsegs mem (Z_to_bv 64 b0) (Z.to_nat l0) = Some bs0).
{ apply (rdn_agree mem mem0); [lia|lia| |exact (Hbs0 eq_refl)]. intros x Hx. apply Hout. unfold inW. lia. }
eapply (srz_writev2_wall tfibsegs (w_H W) (w_A W) regs pc mem rom model fd ch (Z_to_bv 64 b0) (Z_to_bv 64 l0) (Z_to_bv 64 b1) (Z_to_bv 64 l1) bs0 bs1 T HAI).
+ rewrite R17. reflexivity.
+ exact (fdchan_sbm _ _ _ _ Hfdc0 Hfdc). + exact H32. + exact R10. + exact R12.
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
+ intros n _ _. exact (Hav n).
+ exact Hc.
Qed.
Let INVR := wl_invR.
Lemma wl_loop2_r : forall k regs mem model c b0 l0 b1 l1 bs0 bs1,
(length (bs0 ++ bs1) <= k)%nat ->
AIW model -> same_but_materialized model0 model ->
INVR 20%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
srealizes tfibsegs (mkCfg (mkst regs (Z_to_bv 64 0x92dfc) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
induction k as [|k IH]; intros regs mem model c b0 l0 b1 l1 bs0 bs1 Hlen HAI Hfdc HI.
{ exfalso. rewrite length_app in Hlen.
destruct HI as (Hc12 & _ & _ & _ & _ & _ & _ & _ & _ & Hrem & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl0 & Hl1 & _ & _).
destruct Hc12 as [-> | ->]; cbn in Hrem, Hl0; lia. }
pose proof HI as HI'.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & R20 & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1 & Hv0 & Hv1).
replace (Z_to_bv 64 0x92dfc : word) with (0x92dfc%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (srz_step_r W); [exact HAI | reflexivity
| rewrite restrict_mkst_fx; apply (step_ecall _ _ _ _ _ _ F_17c1c eq_refl) |].
intros model1 HAI1 Hsbm1.
change (srealizes tfibsegs (mkCfg (unrestrict HH mem (pend_at regs (0x92dfc%bv : word) (mrestrict HH mem) rom)) model1)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T)).
rewrite (unrestrict_pend W).
eapply (wl_node_r 20%bv _ regs mem model1 c b0 l0 b1 l1 bs0 bs1 HAI1 (same_but_materialized_trans _ _ _ Hfdc Hsbm1) HI').
intros n model2 Hn1 Hn2 HAI2 Hsbm2.
replace (v_addi (0x92dfc%bv : word) 4) with (Z_to_bv 64 0x92e00 : word) by (apply bv_eq; vm_compute; reflexivity).
set (rem := (if c =? 2 then l0 else 0) + l1) in *.
assert (Hlenall : Z.of_nat (length (bs0 ++ bs1)) = rem) by (rewrite length_app; lia).
destruct (after_w2 (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (mrestrict HH mem) rom (Z.of_nat n) rem
ltac:(lia) ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; exact R22))
as (regs1 & Hms1 & R19a & R10a & Hfr1).
eapply (srz_msteps_r W); [exact HAI2 | rewrite restrict_mkst_fx; exact Hms1 |].
intros model3 HAI3 Hsbm3. cbn [ms_mem]. rewrite (unrestrict_mkst_restricted W).
assert (Hfdc3 : same_but_materialized model0 model3).
{ eapply same_but_materialized_trans; [| exact Hsbm3]. eapply same_but_materialized_trans; [| exact Hsbm2]. eapply same_but_materialized_trans; [exact Hfdc | exact Hsbm1]. }
destruct (Z.eqb_spec (Z.of_nat n) rem) as [Heq | Hne].
{
apply wl_done_r; [ | | exact Hout | exact Hst | exact HAI3 | exact Hfdc3 | lia].
- intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr.
- rewrite Hfr1 by reg_neq_tac. rewrite getr_other by reg_neq_tac. exact R17. }
assert (R2a : getr regs1 2 = Z_to_bv 64 SP) by (rewrite Hfr1 by reg_neq_tac; gr; exact R2).
assert (R9a : getr regs1 9 = Z_to_bv 64 F) by (rewrite Hfr1 by reg_neq_tac; gr; exact R9).
assert (R18a : getr regs1 18 = Z_to_bv 64 c) by (rewrite Hfr1 by reg_neq_tac; gr; exact R18).
assert (R19b : getr regs1 19 = Z_to_bv 64 (SP + 40 - 16 * c)) by (rewrite R19a; gr; exact R20).
assert (R22a : getr regs1 22 = Z_to_bv 64 rem) by (rewrite Hfr1 by reg_neq_tac; gr; exact R22).
assert (Hfd' : rdn tfibsegs (mrestrict HH mem) (Z_to_bv 64 (F + 120)) 4 = Some fdbs).
{ apply (rdn_vis W); [lia|cbn; lia| intros x Hx; apply HvisF; cbn in Hx; lia |].
apply (rdn_agree mem mem0); [lia|cbn; lia| |exact Hfd]. intros x Hx. apply Hout. unfold inW. cbn in Hx. lia. }
assert (Hkept1 : forall r, wl_kept r -> getr regs1 r = getr regsK r).
{ intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr. }
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (HstR : store_ok tfibsegs (mrestrict HH mem) (Z_to_bv 64 (SP + 8)) 32 = true).
{ apply (store_ok_vis W); [lia|cbn; lia| intros x Hx; apply HvisW; cbn in Hx; lia | exact Hst]. }
assert (HiovR : iov_mem (mrestrict HH mem) SP c b0 l0 b1 l1).
{ split; [intros Hc2; destruct (Hiov0 Hc2) as [Hm0 Hl0]; split|split];
(apply (rdn_vis W); [lia|cbn; lia| intros x Hx; apply HvisW; cbn in Hx; lia | assumption]). }
assert (OUT : forall mem2 : word -> option byte,
(forall a, ~ inW SP a -> mem2 a = mrestrict HH mem a) ->
forall a, ~ inW SP a -> munrestrict HH mem mem2 a = mem0 a).
{ intros mem2 Q a Ha. unfold munrestrict. destruct (HH a) eqn:Hh.
- apply Hout. exact Ha.
- rewrite (Q a Ha). rewrite (mrestrict_vis W) by exact Hh. apply Hout. exact Ha. }
assert (STO : forall mem2 : word -> option byte,
store_ok tfibsegs mem2 (Z_to_bv 64 (SP + 8)) 32 = true ->
store_ok tfibsegs (munrestrict HH mem mem2) (Z_to_bv 64 (SP + 8)) 32 = true).
{ intros mem2 Q. apply (store_ok_agree mem2); rewrite ?u_Z2bv by lia; [cbn; lia| |exact Q].
intros x Hx. apply (munrestrict_vis W). apply HvisW. cbn in Hx. lia. }
assert (RDW : forall (mem2 : word -> option byte) (a : Z) (bs : list byte),
SP + 8 <= a -> a + 8 <= SP + 40 ->
rdn tfibsegs mem2 (Z_to_bv 64 a) 8 = Some bs -> rdn tfibsegs (munrestrict HH mem mem2) (Z_to_bv 64 a) 8 = Some bs).
{ intros mem2 a bs Ha1 Ha2 Q. apply (rdn_agree (munrestrict HH mem mem2) mem2); [lia|cbn; lia| |exact Q].
intros x Hx. apply (munrestrict_vis W). apply HvisW. cbn in Hx. lia. }
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0, rem. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
assert (HP : body_pre regs1 (mrestrict HH mem) SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (body_C regs1 (mrestrict HH mem) rom SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl)
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (srz_msteps_r W); [exact HAI3 | rewrite restrict_mkst_fx; exact Hms2 |].
intros model4 HAI4 Hsbm4. cbn [ms_mem]. rewrite (unrestrict_mkst W).
change (skipn n bs1) with ([] ++ skipn n bs1).
apply (IH regs2 (munrestrict HH mem mem2) model4 1 0 0 (b1 + Z.of_nat n) (l1 - Z.of_nat n) [] (skipn n bs1)).
+ cbn [app]. rewrite length_skipn. lia.
+ exact HAI4.
+ eapply same_but_materialized_trans; [exact Hfdc3 | exact Hsbm4].
+ unfold INVR, wl_invR. cbn [Z.eqb Pos.eqb].
destruct Qiov as (Qiov0 & Qm1 & Ql1).
clear IH HI' HK.
set (MM := munrestrict HH mem mem2) in *. subst rem.
split; [ left; reflexivity |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ exact Q2 |].
split; [ exact Q9 |].
split; [ exact Q18 |].
split; [ exact Q12 |].
split; [ exact Q20 |].
split; [ exact Q11 |].
split; [ rewrite Q22; f_equal; lia |].
split; [ exact Q10 |].
split; [ exact Q17 |].
split; [ intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr |].
split; [ subst MM; exact (OUT mem2 Qout) |].
split; [ subst MM; exact (STO mem2 Qst) |].
split; [ subst MM; split; [intros HX; exfalso; lia | split; (apply (RDW mem2); [lia|lia|assumption])] |].
split; [ intros HX; exfalso; lia |].
split; [ apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] |].
split; [ reflexivity |].
split; [ rewrite length_skipn; lia |].
split; [ intros HX; exfalso; lia |].
intros x Hx; apply Hv1; lia.
-
cbn in Hrem, R22, Hlen0, rem.
assert (HP : body_pre regs1 (mrestrict HH mem) SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (Z_le_gt_dec (Z.of_nat n) l0) as [Hle | Hgt].
+
destruct (body_A regs1 (mrestrict HH mem) rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (srz_msteps_r W); [exact HAI3 | rewrite restrict_mkst_fx; exact Hms2 |].
intros model4 HAI4 Hsbm4. cbn [ms_mem]. rewrite (unrestrict_mkst W).
rewrite skipn_app. replace (n - length bs0)%nat with 0%nat by lia. cbn [skipn].
apply (IH regs2 (munrestrict HH mem mem2) model4 2 (b0 + Z.of_nat n) (l0 - Z.of_nat n) b1 l1 (skipn n bs0) bs1).
* rewrite length_app, length_skipn in *. lia.
* exact HAI4.
* eapply same_but_materialized_trans; [exact Hfdc3 | exact Hsbm4].
* unfold INVR, wl_invR. cbn [Z.eqb Pos.eqb].
destruct Qiov as (Qiov0 & Qm1 & Ql1).
clear IH HI' HK.
set (MM := munrestrict HH mem mem2) in *. subst rem.
split; [ right; reflexivity |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ exact Q2 |].
split; [ exact Q9 |].
split; [ exact Q18 |].
split; [ exact Q12 |].
split; [ exact Q20 |].
split; [ exact Q11 |].
split; [ rewrite Q22; f_equal; lia |].
split; [ exact Q10 |].
split; [ exact Q17 |].
split; [ intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr |].
split; [ subst MM; exact (OUT mem2 Qout) |].
split; [ subst MM; exact (STO mem2 Qst) |].
split; [ subst MM; split; [intros HX; destruct (Qiov0 HX) as [Qm0 Ql0]; split; (apply (RDW mem2); [lia|lia|assumption]) | split; (apply (RDW mem2); [lia|lia|assumption])] |].
split; [ intros HX; apply rdn_advance; [lia|lia|lia|lia| exact (Hbs0 eq_refl)] |].
split; [ exact Hbs1 |].
split; [ rewrite length_skipn; lia |].
split; [ lia |].
split; [ intros HX x Hx; apply (Hv0 eq_refl); lia |].
exact Hv1.
+
destruct (body_B regs1 (mrestrict HH mem) rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (srz_msteps_r W); [exact HAI3 | rewrite restrict_mkst_fx; exact Hms2 |].
intros model4 HAI4 Hsbm4. cbn [ms_mem]. rewrite (unrestrict_mkst W).
rewrite skipn_app. rewrite (skipn_all_nil n bs0) by lia. cbn [app].
change (skipn (n - length bs0) bs1) with ([] ++ skipn (n - length bs0) bs1).
apply (IH regs2 (munrestrict HH mem mem2) model4 1 0 0 (b1 + (Z.of_nat n - l0)) (l1 - (Z.of_nat n - l0)) [] (skipn (n - length bs0) bs1)).
* cbn [app]. rewrite length_app, length_skipn in *. lia.
* exact HAI4.
* eapply same_but_materialized_trans; [exact Hfdc3 | exact Hsbm4].
* unfold INVR, wl_invR. cbn [Z.eqb Pos.eqb].
destruct Qiov as (Qiov0 & Qm1 & Ql1).
clear IH HI' HK.
set (MM := munrestrict HH mem mem2) in *. subst rem.
split; [ left; reflexivity |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ exact Q2 |].
split; [ exact Q9 |].
split; [ exact Q18 |].
split; [ exact Q12 |].
split; [ exact Q20 |].
split; [ exact Q11 |].
split; [ rewrite Q22; f_equal; lia |].
split; [ exact Q10 |].
split; [ exact Q17 |].
split; [ intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr |].
split; [ subst MM; exact (OUT mem2 Qout) |].
split; [ subst MM; exact (STO mem2 Qst) |].
split; [ subst MM; split; [intros HX; exfalso; lia | split; (apply (RDW mem2); [lia|lia|assumption])] |].
split; [ intros HX; exfalso; lia |].
split; [ replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] |].
split; [ reflexivity |].
split; [ rewrite length_skipn; lia |].
split; [ intros HX; exfalso; lia |].
intros x Hx; apply Hv1; lia.
Qed.
Lemma wl_entry_pend_r : forall regs mem model c b0 l0 b1 l1 bs0 bs1,
AIW model -> same_but_materialized model0 model ->
INVR 19%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
srealizes tfibsegs (mkCfg (pend_at regs (Z_to_bv 64 0x92d74) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros regs mem model c b0 l0 b1 l1 bs0 bs1 HAI1 Hfdc1 HI.
pose proof HI as HI'.
destruct HI as (Hc12 & Hb0a & Hb0b & Hb0c & Hb0d & Hb1a & Hb1b & Hb1c & Hb1d & Hrem & R2 & R9 & R18 & R12 & R19 & R11
& R22 & R10 & R17 & Hkept & Hout & Hst & Hiov & Hbs0 & Hbs1 & Hlen0 & Hlen1 & Hv0 & Hv1).
eapply (wl_node_r 19%bv _ regs mem model c b0 l0 b1 l1 bs0 bs1 HAI1 Hfdc1 HI').
intros n model2 Hn1 Hn2 HAI2 Hsbm2.
replace (v_addi (Z_to_bv 64 0x92d74 : word) 4) with (Z_to_bv 64 0x92d78 : word) by (apply bv_eq; vm_compute; reflexivity).
set (rem := (if c =? 2 then l0 else 0) + l1) in *.
assert (Hlenall : Z.of_nat (length (bs0 ++ bs1)) = rem) by (rewrite length_app; lia).
destruct (after_w1 (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (mrestrict HH mem) rom (Z.of_nat n) rem
ltac:(lia) ltac:(lia) ltac:(gr; reflexivity) ltac:(gr; exact R22))
as (regs1 & Hms1 & R10a & Hfr1).
eapply (srz_msteps_r W); [exact HAI2 | rewrite restrict_mkst_fx; exact Hms1 |].
intros model3 HAI3 Hsbm3. cbn [ms_mem]. rewrite (unrestrict_mkst_restricted W).
assert (Hfdc3 : same_but_materialized model0 model3).
{ eapply same_but_materialized_trans; [| exact Hsbm3]. eapply same_but_materialized_trans; [exact Hfdc1 | exact Hsbm2]. }
assert (Hkept1 : forall r, wl_kept r -> getr regs1 r = getr regsK r).
{ intros r Hr. rewrite Hfr1 by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption).
rewrite getr_other by (destruct Hr as (?&?&?&?&?&?&?&?&?&?&?&?); assumption). apply Hkept. exact Hr. }
destruct (Z.eqb_spec (Z.of_nat n) rem) as [Heq | Hne].
{ apply wl_done_r; [ exact Hkept1 | | exact Hout | exact Hst | exact HAI3 | exact Hfdc3 | lia].
rewrite Hfr1 by reg_neq_tac. rewrite getr_other by reg_neq_tac. exact R17. }
assert (R2a : getr regs1 2 = Z_to_bv 64 SP) by (rewrite Hfr1 by reg_neq_tac; gr; exact R2).
assert (R9a : getr regs1 9 = Z_to_bv 64 F) by (rewrite Hfr1 by reg_neq_tac; gr; exact R9).
assert (R18a : getr regs1 18 = Z_to_bv 64 c) by (rewrite Hfr1 by reg_neq_tac; gr; exact R18).
assert (R19b : getr regs1 19 = Z_to_bv 64 (SP + 40 - 16 * c)) by (rewrite Hfr1 by reg_neq_tac; gr; exact R19).
assert (R22a : getr regs1 22 = Z_to_bv 64 rem) by (rewrite Hfr1 by reg_neq_tac; gr; exact R22).
assert (Hfd' : rdn tfibsegs (mrestrict HH mem) (Z_to_bv 64 (F + 120)) 4 = Some fdbs).
{ apply (rdn_vis W); [lia|cbn; lia| intros x Hx; apply HvisF; cbn in Hx; lia |].
apply (rdn_agree mem mem0); [lia|cbn; lia| |exact Hfd]. intros x Hx. apply Hout. unfold inW. cbn in Hx. lia. }
destruct Hiov as (Hiov0 & Hm1 & Hl1).
assert (HstR : store_ok tfibsegs (mrestrict HH mem) (Z_to_bv 64 (SP + 8)) 32 = true).
{ apply (store_ok_vis W); [lia|cbn; lia| intros x Hx; apply HvisW; cbn in Hx; lia | exact Hst]. }
assert (HiovR : iov_mem (mrestrict HH mem) SP c b0 l0 b1 l1).
{ split; [intros Hc2; destruct (Hiov0 Hc2) as [Hm0 Hl0]; split|split];
(apply (rdn_vis W); [lia|cbn; lia| intros x Hx; apply HvisW; cbn in Hx; lia | assumption]). }
assert (OUT : forall mem2 : word -> option byte,
(forall a, ~ inW SP a -> mem2 a = mrestrict HH mem a) ->
forall a, ~ inW SP a -> munrestrict HH mem mem2 a = mem0 a).
{ intros mem2 Q a Ha. unfold munrestrict. destruct (HH a) eqn:Hh.
- apply Hout. exact Ha.
- rewrite (Q a Ha). rewrite (mrestrict_vis W) by exact Hh. apply Hout. exact Ha. }
assert (STO : forall mem2 : word -> option byte,
store_ok tfibsegs mem2 (Z_to_bv 64 (SP + 8)) 32 = true ->
store_ok tfibsegs (munrestrict HH mem mem2) (Z_to_bv 64 (SP + 8)) 32 = true).
{ intros mem2 Q. apply (store_ok_agree mem2); rewrite ?u_Z2bv by lia; [cbn; lia| |exact Q].
intros x Hx. apply (munrestrict_vis W). apply HvisW. cbn in Hx. lia. }
assert (RDW : forall (mem2 : word -> option byte) (a : Z) (bs : list byte),
SP + 8 <= a -> a + 8 <= SP + 40 ->
rdn tfibsegs mem2 (Z_to_bv 64 a) 8 = Some bs -> rdn tfibsegs (munrestrict HH mem mem2) (Z_to_bv 64 a) 8 = Some bs).
{ intros mem2 a bs Ha1 Ha2 Q. apply (rdn_agree (munrestrict HH mem mem2) mem2); [lia|cbn; lia| |exact Q].
intros x Hx. apply (munrestrict_vis W). apply HvisW. cbn in Hx. lia. }
destruct Hc12 as [-> | ->].
-
cbn in Hrem, R22, Hlen0, rem. destruct bs0; [|cbn in Hlen0; lia]. cbn [app] in *.
assert (HP : body_pre regs1 (mrestrict HH mem) SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (body_C regs1 (mrestrict HH mem) rom SP F 1 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl)
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (srz_msteps_r W); [exact HAI3 | rewrite restrict_mkst_fx; exact Hms2 |].
intros model4 HAI4 Hsbm4. cbn [ms_mem]. rewrite (unrestrict_mkst W).
change (skipn n bs1) with ([] ++ skipn n bs1).
apply (wl_loop2_r (length bs1) regs2 (munrestrict HH mem mem2) model4 1 0 0 (b1 + Z.of_nat n) (l1 - Z.of_nat n) [] (skipn n bs1)).
+ cbn [app]. rewrite length_skipn. lia.
+ exact HAI4.
+ eapply same_but_materialized_trans; [exact Hfdc3 | exact Hsbm4].
+ unfold INVR, wl_invR. cbn [Z.eqb Pos.eqb].
destruct Qiov as (Qiov0 & Qm1 & Ql1).
clear HI' HK.
set (MM := munrestrict HH mem mem2) in *. subst rem.
split; [ left; reflexivity |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ exact Q2 |].
split; [ exact Q9 |].
split; [ exact Q18 |].
split; [ exact Q12 |].
split; [ exact Q20 |].
split; [ exact Q11 |].
split; [ rewrite Q22; f_equal; lia |].
split; [ exact Q10 |].
split; [ exact Q17 |].
split; [ intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr |].
split; [ subst MM; exact (OUT mem2 Qout) |].
split; [ subst MM; exact (STO mem2 Qst) |].
split; [ subst MM; split; [intros HX; exfalso; lia | split; (apply (RDW mem2); [lia|lia|assumption])] |].
split; [ intros HX; exfalso; lia |].
split; [ apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] |].
split; [ reflexivity |].
split; [ rewrite length_skipn; lia |].
split; [ intros HX; exfalso; lia |].
intros x Hx; apply Hv1; lia.
-
cbn in Hrem, R22, Hlen0, rem.
assert (HP : body_pre regs1 (mrestrict HH mem) SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs).
{ unfold body_pre. repeat match goal with |- _ /\ _ => split end; try assumption; try lia; subst rem; try reflexivity; try assumption. }
destruct (Z_le_gt_dec (Z.of_nat n) l0) as [Hle | Hgt].
+
destruct (body_A regs1 (mrestrict HH mem) rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (srz_msteps_r W); [exact HAI3 | rewrite restrict_mkst_fx; exact Hms2 |].
intros model4 HAI4 Hsbm4. cbn [ms_mem]. rewrite (unrestrict_mkst W).
rewrite skipn_app. replace (n - length bs0)%nat with 0%nat by lia. cbn [skipn].
apply (wl_loop2_r (length (bs0 ++ bs1)) regs2 (munrestrict HH mem mem2) model4 2 (b0 + Z.of_nat n) (l0 - Z.of_nat n) b1 l1 (skipn n bs0) bs1).
* rewrite !length_app, length_skipn in *. lia.
* exact HAI4.
* eapply same_but_materialized_trans; [exact Hfdc3 | exact Hsbm4].
* unfold INVR, wl_invR. cbn [Z.eqb Pos.eqb].
destruct Qiov as (Qiov0 & Qm1 & Ql1).
clear HI' HK.
set (MM := munrestrict HH mem mem2) in *. subst rem.
split; [ right; reflexivity |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ exact Q2 |].
split; [ exact Q9 |].
split; [ exact Q18 |].
split; [ exact Q12 |].
split; [ exact Q20 |].
split; [ exact Q11 |].
split; [ rewrite Q22; f_equal; lia |].
split; [ exact Q10 |].
split; [ exact Q17 |].
split; [ intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr |].
split; [ subst MM; exact (OUT mem2 Qout) |].
split; [ subst MM; exact (STO mem2 Qst) |].
split; [ subst MM; split; [intros HX; destruct (Qiov0 HX) as [Qm0 Ql0]; split; (apply (RDW mem2); [lia|lia|assumption]) | split; (apply (RDW mem2); [lia|lia|assumption])] |].
split; [ intros HX; apply rdn_advance; [lia|lia|lia|lia| exact (Hbs0 eq_refl)] |].
split; [ exact Hbs1 |].
split; [ rewrite length_skipn; lia |].
split; [ lia |].
split; [ intros HX x Hx; apply (Hv0 eq_refl); lia |].
exact Hv1.
+
destruct (body_B regs1 (mrestrict HH mem) rom SP F 2 b0 l0 b1 l1 rem (Z.of_nat n) fd fdbs HP eq_refl ltac:(lia))
as (regs2 & mem2 & Hms2 & Q2 & Q9 & Q18 & Q12 & Q20 & Q11 & Q22 & Q10 & Q17 & Qkept & Qout & Qst & Qiov).
eapply (srz_msteps_r W); [exact HAI3 | rewrite restrict_mkst_fx; exact Hms2 |].
intros model4 HAI4 Hsbm4. cbn [ms_mem]. rewrite (unrestrict_mkst W).
rewrite skipn_app. rewrite (skipn_all_nil n bs0) by lia. cbn [app].
change (skipn (n - length bs0) bs1) with ([] ++ skipn (n - length bs0) bs1).
apply (wl_loop2_r (length bs1) regs2 (munrestrict HH mem mem2) model4 1 0 0 (b1 + (Z.of_nat n - l0)) (l1 - (Z.of_nat n - l0)) [] (skipn (n - length bs0) bs1)).
* cbn [app]. rewrite length_skipn. lia.
* exact HAI4.
* eapply same_but_materialized_trans; [exact Hfdc3 | exact Hsbm4].
* unfold INVR, wl_invR. cbn [Z.eqb Pos.eqb].
destruct Qiov as (Qiov0 & Qm1 & Ql1).
clear HI' HK.
set (MM := munrestrict HH mem mem2) in *. subst rem.
split; [ left; reflexivity |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ lia |].
split; [ exact Q2 |].
split; [ exact Q9 |].
split; [ exact Q18 |].
split; [ exact Q12 |].
split; [ exact Q20 |].
split; [ exact Q11 |].
split; [ rewrite Q22; f_equal; lia |].
split; [ exact Q10 |].
split; [ exact Q17 |].
split; [ intros r Hr; rewrite (Qkept r Hr); apply Hkept1; exact Hr |].
split; [ subst MM; exact (OUT mem2 Qout) |].
split; [ subst MM; exact (STO mem2 Qst) |].
split; [ subst MM; split; [intros HX; exfalso; lia | split; (apply (RDW mem2); [lia|lia|assumption])] |].
split; [ intros HX; exfalso; lia |].
split; [ replace (Z.of_nat n - l0) with (Z.of_nat (n - length bs0)) by lia; apply rdn_advance; [lia|lia|lia|lia| exact Hbs1] |].
split; [ reflexivity |].
split; [ rewrite length_skipn; lia |].
split; [ intros HX; exfalso; lia |].
intros x Hx; apply Hv1; lia.
Qed.
Lemma wl_entry_r : forall regs mem model c b0 l0 b1 l1 bs0 bs1,
AIW model -> same_but_materialized model0 model ->
INVR 19%bv regs mem c b0 l0 b1 l1 bs0 bs1 ->
srealizes tfibsegs (mkCfg (mkst regs (Z_to_bv 64 0x92d74) mem rom) model)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T).
Proof.
intros regs mem model c b0 l0 b1 l1 bs0 bs1 HAI Hfdc HI.
replace (Z_to_bv 64 0x92d74 : word) with (0x92d74%bv : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (srz_step_r W); [exact HAI | reflexivity
| rewrite restrict_mkst_fx; apply (step_ecall _ _ _ _ _ _ F_17b94 eq_refl) |].
intros model1 HAI1 Hsbm1.
change (srealizes tfibsegs (mkCfg (unrestrict HH mem (pend_at regs (0x92d74%bv : word) (mrestrict HH mem) rom)) model1)
(t_emit (map (WriteEv ch) (bs0 ++ bs1)) T)).
rewrite (unrestrict_pend W).
replace (0x92d74%bv : word) with (Z_to_bv 64 0x92d74 : word) by (apply bv_eq; vm_compute; reflexivity).
apply (wl_entry_pend_r regs mem model1 c b0 l0 b1 l1 bs0 bs1 HAI1 (same_but_materialized_trans _ _ _ Hfdc Hsbm1) HI).
Qed.
End g.
End d.
