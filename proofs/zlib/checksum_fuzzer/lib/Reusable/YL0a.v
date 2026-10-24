(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Uaccess.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK0s YK15 YM06 YM02 YK0p YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import
YP0m YP0e YP09 YP0l YP06 YP03 YP04 YP05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YN03 YL07 YL01.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma file_read_length : forall data (off count : word),
Z.of_nat (length (file_read data off count)) = Z.min (bv_unsigned count) (Z.max 0 (Z.of_nat (length data) - bv_unsigned off)).
Proof.
intros data off count. rewrite file_read_unguarded. rewrite length_firstn, length_skipn.
unfold word_to_nat. pose proof (u64_range count). pose proof (u64_range off). lia.
Qed.
Lemma file_read_all : forall data (count : word),
Z.of_nat (length data) <= bv_unsigned count -> file_read data (Z_to_bv 64 0) count = data.
Proof.
intros data count H. rewrite file_read_unguarded. unfold word_to_nat. rewrite Z_to_bv_unsigned.
change (bv_wrap 64 0) with 0. cbn [Z.to_nat skipn]. apply firstn_all2. lia.
Qed.
Lemma file_read_eof : forall data (off count : word),
Z.of_nat (length data) <= bv_unsigned off -> file_read data off count = [].
Proof.
intros data off count H. rewrite file_read_unguarded. rewrite skipn_all2 by (unfold word_to_nat; lia).
apply firstn_nil.
Qed.
Section e.
Variable segs : list Segment.
Lemma mem_ok_ext_same : forall E (m m' : word -> option byte) rs,
mem_ok segs E m rs ->
(forall r x, In r rs -> base_val E (r_base r) + r_lo r <= x < base_val E (r_base r) + r_hi r ->
m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
mem_ok segs E m' rs.
Proof.
intros E m m' rs (Hwf & Hok & Hpd) Hsame. split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hr. destruct (Hok r Hr) as (H1 & H2 & H3 & H4).
pose proof (regions_wf_In _ _ Hwf Hr) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hw & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. specialize (H3 o Ho). unfold writable_at, wview in *.
rewrite (Hsame r) by (try exact Hr; lia). exact H3.
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
unfold mbyte in *. rewrite (Hsame r) by (try exact Hr; lia). exact Hb2.
Qed.
End e.
Lemma read_mem_wbytes : forall mem (a : word) bs,
match bs with [] => mem | _ :: _ => write_to_mem mem a bs end = wbytes mem a bs.
Proof. intros mem a [|b bs]; [reflexivity| apply write_to_mem_wbytes]. Qed.
Lemma wbytes_inside' : forall bs m (a x : word),
bv_unsigned a + Z.of_nat (length bs) <= 2^64 ->
bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs) ->
wbytes m a bs x = Some (nth (Z.to_nat (bv_unsigned x - bv_unsigned a)) bs (Z_to_bv 8 0)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; cbn [length] in *; [lia|].
cbn [wbytes].
destruct rest as [|b' rest'].
- cbn [wbytes length] in *.
replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with 0%nat by lia. reflexivity.
- cbn [length] in *.
assert (Hu1 : bv_unsigned (a + 1) = bv_unsigned a + 1).
{ rewrite bv_add_unsigned. change (bv_unsigned (1:word)) with 1. unfold bv_wrap. change (bv_modulus 64) with (2^64).
apply Z.mod_small. pose proof (u64_range a). lia. }
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
+ rewrite wbytes_below by (cbn [length]; rewrite ?Hu1; lia).
replace (bv_eqb x a) with true by (symmetry; unfold bv_eqb; apply Z.eqb_eq; lia).
rewrite Heq, Z.sub_diag. reflexivity.
+ rewrite IH by (cbn [length]; rewrite Hu1; lia).
rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Section f.
Variable B : malloc_syms.
Variable MR : MR_t.
Hypothesis LAWS : MR_laws B MR.
Hypothesis AX : AllocExtra B MR.
Let segs := ms_segs B.
Lemma rz_read_block : forall E ss ms model fd pth off data bs L A p sz (a cnt : Z) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17%bv)) = 63 ->
sv_denot E (sr_get (ss_regs ss) 10%bv) = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile pth off) ->
fs_lookup (m_fs model) pth = Some data ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 11%bv)) = a ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 12%bv)) = cnt -> 0 < cnt <= 65536 ->
file_read data off (sv_denot E (sr_get (ss_regs ss) 12%bv)) = bs ->
MR L A (ms_mem ms) model -> In (p, sz) (user_blocks A) ->
ptr_addr L p <= a -> a + cnt <= ptr_addr L p + sz ->
(forall regs,
regs_ok E (ss_regs ss) regs ->
facts_ok E (ss_facts ss) ->
mem_ok segs E (ms_mem ms) (ss_mem ss) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (a + i) = nth_error bs (Z.to_nat i)) ->
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x ->
wbytes (ms_mem ms) (Z_to_bv 64 a) bs x = ms_mem ms x) ->
Z.of_nat (length bs) <= cnt ->
realizes segs (mkCfg (mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4)
(wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFile pth (off + len_word bs))) model)) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd pth off data bs L A p sz a cnt T Hh Hlz HS Hrv H17 H10 H32 Hlk Hfs H11 H12 Hcnt Hbs HMR Hin Hlo Hhi Hk.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in HMR, Hk.
pose proof (mr_blocks B MR LAWS L A mem model p sz) as HB.
destruct (HB 0 HMR Hin ltac:(lia)) as (_ & Hplo & Hphi & _).
assert (Hac : alloc_ceiling < 2 ^ 63) by (pose proof YM05.alloc_ceiling_val; lia).
assert (Hlen : Z.of_nat (length bs) <= cnt).
{ rewrite <- Hbs. rewrite file_read_length. rewrite H12. lia. }
assert (HA : sv_denot E (sr_get (ss_regs ss) 11%bv) = Z_to_bv 64 a).
{ rewrite <- H11. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
destruct (read_dest_ok segs mem (Z_to_bv 64 a) bs) as [w Hw].
{ intros i Hi. rewrite Hau. destruct (HB (a - ptr_addr L p + i) HMR Hin ltac:(lia)) as ([b Hb] & _).
replace (ptr_addr L p + (a - ptr_addr L p + i)) with (a + i) in Hb by lia. rewrite Hb. discriminate. }
eapply (rz_read_file segs regs _ mem (seg_rom segs) model fd pth off data bs w T Hh Hlz).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- exact Hfs.
- rewrite (Hregs 12%bv). unfold modeled_rw_count. apply Z.leb_le. rewrite H12.
assert (X : rw_bytes_max = 2 ^ 17) by reflexivity. rewrite X. lia.
- rewrite (Hregs 12%bv). exact Hbs.
- rewrite (Hregs 11%bv), HA. exact Hw.
-
rewrite (Hregs 11%bv), (Hregs 12%bv), HA, H12. unfold access_okb, TASK_SIZE. rewrite Hau.
pose proof YM05.alloc_ceiling_val. apply andb_true_intro; split; apply Z.leb_le; lia.
- rewrite read_mem_wbytes, (Hregs 11%bv), HA.
apply Hk.
+ exact Hregs.
+ exact HG.
+ exact Hmem.
+ intros i Hi. unfold mbyte.
rewrite (wbytes_inside' bs mem (Z_to_bv 64 a) (Z_to_bv 64 (a + i))) by (rewrite ?Hau, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite ?Z.mod_small by lia; lia).
rewrite Hau. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
replace (a + i - a) with i by lia. symmetry. apply nth_error_nth'. lia.
+ intros x [Hx|Hx]; [apply wbytes_below; rewrite Hau; lia | apply wbytes_above; rewrite Hau; lia].
+ exact Hlen.
Qed.
End f.
Section g.
Variable segs : list Segment.
Definition abs_dest_check (rs : smem) (a n : Z) : bool :=
existsb (fun r => obase_eqb (r_base r) None && (r_wlo r <=? a) && (a + n <=? r_whi r) &&
forallb (fun c => (c_off c + c_len c <=? a) || (a + n <=? c_off c)) (r_chunks r)) rs.
Lemma abs_dest_check_sound : forall rs a n,
abs_dest_check rs a n = true ->
exists r, In r rs /\ r_base r = None /\ r_wlo r <= a /\ a + n <= r_whi r /\
(forall c, In c (r_chunks r) -> c_off c + c_len c <= a \/ a + n <= c_off c).
Proof.
intros rs a n H. unfold abs_dest_check in H. apply existsb_In in H as (r & Hr & H).
apply andb_prop in H as [H Hcs]. apply andb_prop in H as [H H2]. apply andb_prop in H as [Hb H1].
apply obase_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists r. repeat (split; [assumption|]). intros c Hc.
pose proof (forallb_In _ _ c Hcs Hc) as Hcc. apply orb_prop in Hcc as [Hcc|Hcc]; apply Z.leb_le in Hcc; lia.
Qed.
Lemma mem_ok_abs_window : forall E m m' rs a n,
mem_ok segs E m rs -> abs_dest_check rs a n = true -> 0 <= n ->
(forall x : word, ~ (a <= bv_unsigned x < a + n) -> m' x = m x) ->
(forall x, a <= x < a + n -> writable_at segs m' x) ->
mem_ok segs E m' rs.
Proof.
intros E m m' rs a n HM Hck Hn Hout Hin.
destruct (abs_dest_check_sound rs a n Hck) as (r & Hr & Hb & Hwlo & Hwhi & Hcs).
destruct HM as (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [|exact Hpd].
pose proof (regions_wf_In rs r Hwf Hr) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hwr & Hci).
pose proof (proj1 (Forall_forall _ _) Hok r Hr) as (Hr0 & Hr1 & Hrw & Hrc). rewrite Hb in Hr0, Hr1, Hrw, Hrc. cbn [base_val] in Hr0, Hr1, Hrw, Hrc.
assert (Hwin : forall x, a <= x < a + n -> r_lo r <= x < r_hi r) by (intros x Hx; lia).
rewrite Forall_forall in Hok |- *. intros r' Hin'.
destruct (Hok r' Hin') as (Hc0 & Hc1 & Hw' & Hcs').
assert (Hwf' : region_wf r' = true) by (apply (regions_wf_In rs); assumption).
apply region_wf_facts in Hwf' as (Hlohi' & Hwr' & Hcin').
assert (Hcase : r' = r \/ extent_disjoint E r r').
{ destruct (in_split _ _ Hr) as (l1 & l2 & Hsplit).
assert (Hdis : Forall (extent_disjoint E r) (l1 ++ l2)).
{ rewrite Hsplit in Hpd. exact (pairwise_disjoint_split E _ r _ Hpd). }
rewrite Hsplit in Hin'. apply in_app_iff in Hin'. destruct Hin' as [H|[H|H]].
- right. apply (proj1 (Forall_forall _ _) Hdis). apply in_app_iff. auto.
- left. symmetry. exact H.
- right. apply (proj1 (Forall_forall _ _) Hdis). apply in_app_iff. auto. }
split; [exact Hc0|]. split; [exact Hc1|]. split.
- intros o Ho. pose proof (Hw' o Ho) as W. unfold writable_at, wview in W |- *.
destruct (Z_le_dec a (base_val E (r_base r') + o)) as [L1|L1];
[destruct (Z_lt_dec (base_val E (r_base r') + o) (a + n)) as [L2|L2]|].
+ exact (Hin (base_val E (r_base r') + o) ltac:(lia)).
+ rewrite (Hout (Z_to_bv 64 (base_val E (r_base r') + o))) by (rewrite u_Z2bv by lia; lia). exact W.
+ rewrite (Hout (Z_to_bv 64 (base_val E (r_base r') + o))) by (rewrite u_Z2bv by lia; lia). exact W.
- rewrite Forall_forall in Hcs' |- *. intros c Hc i Hi.
destruct (Hcs' c Hc i Hi) as (bt & Hb1 & Hb2). exists bt. split; [exact Hb1|].
pose proof (proj1 (forallb_forall _ _) Hcin' c Hc) as Hcc. apply chunk_inside_facts in Hcc.
unfold mbyte in *. rewrite (Hout (Z_to_bv 64 (base_val E (r_base r') + c_off c + i))) by
(rewrite u_Z2bv by lia;
destruct Hcase as [-> | Hd];
[ rewrite Hb; cbn [base_val]; pose proof (Hcs c Hc); lia
| unfold extent_disjoint in Hd; rewrite Hb in Hd; cbn [base_val] in Hd; lia ]).
exact Hb2.
Qed.
Lemma read_dest_ok_w : forall mem (buf : word) (bs : list byte),
(forall i, 0 <= i < Z.of_nat (length bs) -> wview segs mem (Z_to_bv 64 (bv_unsigned buf + i)) <> None) ->
exists w, read_bytes_map (wview segs mem) buf (len_word bs) = Some w.
Proof.
intros mem buf bs Hdef. rewrite read_bytes_map_eq.
apply read_bytes_aux_defined. intros i Hi.
assert (Hlen : Z.of_nat (word_to_nat (len_word bs)) <= Z.of_nat (length bs)).
{ unfold word_to_nat, len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
pose proof (Z.mod_le (Z.of_nat (length bs)) (2 ^ 64) ltac:(lia) ltac:(lia)).
rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). lia. }
apply Hdef. lia.
Qed.
Lemma rz_read_abs : forall E ss ms model fd pth off data bs (a cnt : Z) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17%bv)) = 63 ->
sv_denot E (sr_get (ss_regs ss) 10%bv) = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile pth off) ->
fs_lookup (m_fs model) pth = Some data ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 11%bv)) = a ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 12%bv)) = cnt -> 0 < cnt <= 65536 ->
file_read data off (sv_denot E (sr_get (ss_regs ss) 12%bv)) = bs ->
abs_dest_check (ss_mem ss) a 65536 = true -> a + 65536 <= 2 ^ 47 ->
(forall regs,
regs_ok E (ss_regs ss) regs -> facts_ok E (ss_facts ss) ->
mem_ok segs E (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (ss_mem ss) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (a + i) = nth_error bs (Z.to_nat i)) ->
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x ->
wbytes (ms_mem ms) (Z_to_bv 64 a) bs x = ms_mem ms x) ->
frame_of E (ss_mem ss) (ms_mem ms) (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) ->
Z.of_nat (length bs) <= cnt ->
realizes segs (mkCfg (mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4)
(wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFile pth (off + len_word bs))) model)) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd pth off data bs a cnt T Hh Hlz HS Hrv H17 H10 H32 Hlk Hfs H11 H12 Hcnt Hbs Hck Ha47 Hk.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in Hk.
destruct (abs_dest_check_sound _ _ _ Hck) as (r & Hr & Hb & Hwlo & Hwhi & Hcs).
pose proof (mem_ok_region segs E mem (ss_mem ss) r Hmem Hr) as (Hr0 & Hr1 & Hrw & _).
rewrite Hb in Hr0, Hr1, Hrw. cbn [base_val] in Hr0, Hr1, Hrw.
pose proof (regions_wf_In _ r (proj1 Hmem) Hr) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hwr & _).
pose proof (u64_range (sv_denot E (sr_get (ss_regs ss) 11%bv))) as Ra. rewrite H11 in Ra.
assert (Hlen : Z.of_nat (length bs) <= cnt).
{ rewrite <- Hbs. rewrite file_read_length. rewrite H12. lia. }
assert (HA : sv_denot E (sr_get (ss_regs ss) 11%bv) = Z_to_bv 64 a).
{ rewrite <- H11. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
assert (Hww : forall x, a <= x < a + 65536 -> wview segs mem (Z_to_bv 64 x) <> None).
{ intros x Hx. pose proof (Hrw (x - 0) ltac:(lia)) as W. unfold writable_at in W.
replace (0 + (x - 0)) with x in W by lia. exact W. }
destruct (read_dest_ok_w mem (Z_to_bv 64 a) bs) as [w Hw].
{ intros i Hi. rewrite Hau. apply Hww. lia. }
eapply (rz_read_file segs regs _ mem (seg_rom segs) model fd pth off data bs w T Hh Hlz).
- rewrite (Hregs 17%bv). exact H17.
- rewrite (Hregs 10%bv). exact H10.
- exact H32.
- exact Hlk.
- exact Hfs.
- rewrite (Hregs 12%bv). unfold modeled_rw_count. apply Z.leb_le. rewrite H12.
assert (X : rw_bytes_max = 2 ^ 17) by reflexivity. rewrite X. lia.
- rewrite (Hregs 12%bv). exact Hbs.
- rewrite (Hregs 11%bv), HA. exact Hw.
- rewrite (Hregs 11%bv), (Hregs 12%bv), HA, H12. unfold access_okb, TASK_SIZE. rewrite Hau.
apply andb_true_intro; split; apply Z.leb_le; lia.
- rewrite read_mem_wbytes, (Hregs 11%bv), HA.
assert (Hout : forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x ->
wbytes mem (Z_to_bv 64 a) bs x = mem x).
{ intros x [Hx|Hx]; [apply wbytes_below; rewrite Hau; lia | apply wbytes_above; rewrite Hau; lia]. }
apply Hk.
+ exact Hregs.
+ exact HG.
+ apply (mem_ok_abs_window E mem _ (ss_mem ss) a 65536 Hmem Hck ltac:(lia)).
* intros x Hx. apply Hout. lia.
* intros x Hx. unfold writable_at, wview.
destruct (Z_lt_dec x (a + Z.of_nat (length bs))) as [L|L].
-- rewrite (wbytes_inside' bs mem (Z_to_bv 64 a) (Z_to_bv 64 x)) by (rewrite ?Hau, ?u_Z2bv by lia; lia). discriminate.
-- rewrite Hout by (rewrite u_Z2bv by lia; lia). fold (wview segs mem (Z_to_bv 64 x)). exact (Hww x Hx).
+ intros i Hi. unfold mbyte.
rewrite (wbytes_inside' bs mem (Z_to_bv 64 a) (Z_to_bv 64 (a + i))) by (rewrite ?Hau, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite ?Z.mod_small by lia; lia).
rewrite Hau. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
replace (a + i - a) with i by lia. symmetry. apply nth_error_nth'. lia.
+ exact Hout.
+ intros x Hnw. apply Hout.
destruct (Z_lt_dec (bv_unsigned x) a) as [L|L]; [left; exact L|right].
destruct (Z_le_dec (a + Z.of_nat (length bs)) (bv_unsigned x)) as [L2|L2]; [exact L2|].
exfalso. apply Hnw. exists r. split; [exact Hr|]. rewrite Hb. cbn [base_val]. lia.
+ exact Hlen.
Qed.
End g.
End d.
