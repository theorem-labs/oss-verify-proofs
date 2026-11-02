(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0b.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0p.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0n.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP08.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP05.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL0a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable segs : list Segment.
Definition win_region_ok (a n : Z) (r : region) : bool :=
obase_eqb (r_base r) None && (r_lo r <=? a) && (a + n <=? r_hi r) && (r_whi r <=? r_wlo r) &&
match r_chunks r with [] => true | _ => false end.
Definition win_check (rs : smem) (a n : Z) : bool := existsb (win_region_ok a n) rs.
Definition seg_win_check (a : Z) (n : nat) : bool :=
zallb (fun x => match wview segs (fun _ => None) (Z_to_bv 64 x) with Some _ => true | None => false end) a n.
Lemma win_region_ok_sound : forall a n r,
win_region_ok a n r = true ->
r_base r = None /\ r_lo r <= a /\ a + n <= r_hi r /\ r_whi r <= r_wlo r /\ r_chunks r = [].
Proof.
intros a n r H. unfold win_region_ok in H.
apply andb_prop in H as [H Hc]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [Hb H1].
apply obase_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct (r_chunks r); [| discriminate]. repeat split; assumption.
Qed.
Lemma win_check_sound : forall rs a n,
win_check rs a n = true ->
exists rw, In rw rs /\ r_base rw = None /\ r_lo rw <= a /\ a + n <= r_hi rw /\ r_whi rw <= r_wlo rw /\ r_chunks rw = [].
Proof.
intros rs a n H. unfold win_check in H. apply existsb_In in H as (r & Hr & H).
exists r. split; [exact Hr|]. apply win_region_ok_sound. exact H.
Qed.
Lemma seg_win_wview : forall a n m x,
seg_win_check a (Z.to_nat n) = true -> 0 <= n -> a <= x < a + n -> wview segs m (Z_to_bv 64 x) <> None.
Proof.
intros a n m x H Hn Hx. unfold seg_win_check in H.
pose proof (zallb_sound _ _ _ x H ltac:(rewrite Z2Nat.id by lia; lia)) as Hw. cbn beta in Hw.
unfold wview in *. destruct (m (Z_to_bv 64 x)); [discriminate|].
destruct (find_segment segs (bv_unsigned (Z_to_bv 64 x)) 1) as [sg|]; [|discriminate].
destruct (seg_writable sg); [|discriminate].
destruct (segment_byte_at (seg_bytes sg) _); [discriminate | discriminate].
Qed.
Lemma pairwise_In2 : forall E rs r1 r2,
pairwise_disjoint E rs -> In r1 rs -> In r2 rs -> r1 = r2 \/ extent_disjoint E r1 r2.
Proof.
intros E rs. induction rs as [|r rs IH]; intros r1 r2 Hpd H1 H2; [destruct H1|].
cbn [pairwise_disjoint] in Hpd. destruct Hpd as [Hall Hpd].
destruct H1 as [E1|H1]; destruct H2 as [E2|H2].
- left. congruence.
- right. subst r. exact (all_disjoint_In E r1 rs r2 Hall H2).
- right. subst r. pose proof (all_disjoint_In E r2 rs r1 Hall H1) as D. unfold extent_disjoint in *. lia.
- apply IH; assumption.
Qed.
Lemma region_ok_ext : forall E (m m' : word -> option byte) r,
region_wf r = true -> region_ok segs E m r ->
(forall x, 0 <= x < 2 ^ 64 -> base_val E (r_base r) + r_lo r <= x < base_val E (r_base r) + r_hi r -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
region_ok segs E m' r.
Proof.
intros E m m' r Hwf (H1 & H2 & H3 & H4) Hsame.
apply region_wf_facts in Hwf as (Hlohi & Hw & Hci).
split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. specialize (H3 o Ho). unfold writable_at, wview in *.
rewrite (Hsame (base_val E (r_base r) + o)) by lia. exact H3.
- rewrite Forall_forall in H4 |- *. intros c Hc i Hi.
destruct (H4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
pose proof (chunk_inside_facts r c (proj1 (forallb_forall _ _) Hci c Hc)) as (Hc1 & Hc2 & Hc3).
unfold mbyte in *. rewrite (Hsame (base_val E (r_base r) + c_off c + i)) by lia. exact Hb2.
Qed.
Lemma region_ok_win : forall E (m m' : word -> option byte) r,
region_ok segs E m r -> r_whi r <= r_wlo r -> r_chunks r = [] -> region_ok segs E m' r.
Proof.
intros E m m' r (H1 & H2 & H3 & H4) Hw Hc. split; [exact H1|]. split; [exact H2|]. split.
- intros o Ho. lia.
- rewrite Hc. constructor.
Qed.
Theorem mem_ok_win : forall E (m m' : word -> option byte) rs a n,
mem_ok segs E m rs -> win_check rs a n = true ->
(forall x, 0 <= x < 2 ^ 64 -> ~ (a <= x < a + n) -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
mem_ok segs E m' rs.
Proof.
intros E m m' rs a n HM Hck Hout. destruct (win_check_sound rs a n Hck) as (rw & Hrw & Hb & Hlo & Hhi & Hw & Hc).
destruct HM as (Hwf & Hok & Hpd). split; [exact Hwf|]. split; [|exact Hpd].
rewrite Forall_forall in Hok |- *. intros r Hr.
destruct (pairwise_In2 E rs r rw Hpd Hr Hrw) as [-> | Hd].
- apply (region_ok_win E m m' rw (Hok rw Hrw) Hw Hc).
- apply (region_ok_ext E m m' r (regions_wf_In rs r Hwf Hr) (Hok r Hr)).
intros x Hx64 Hx. apply Hout; [exact Hx64|]. intros Hxa. unfold extent_disjoint in Hd. rewrite Hb in Hd. cbn [base_val] in Hd. lia.
Qed.
Theorem win_not_wrange : forall E m rs a n x,
mem_ok segs E m rs -> win_check rs a n = true -> a <= x < a + n -> ~ in_wrange E rs x.
Proof.
intros E m rs a n x HM Hck Hx (r & Hr & Hxr). destruct (win_check_sound rs a n Hck) as (rw & Hrw & Hb & Hlo & Hhi & Hw & Hc).
destruct HM as (Hwf & Hok & Hpd).
pose proof (regions_wf_In rs r Hwf Hr) as Hrwf. apply region_wf_facts in Hrwf as (Hlohi & Hwr & _).
destruct (pairwise_In2 E rs r rw Hpd Hr Hrw) as [-> | Hd]; [lia|].
unfold extent_disjoint in Hd. rewrite Hb in Hd. cbn [base_val] in Hd. lia.
Qed.
Corollary mbyte_win_after_frame : forall E m m' rs a n,
mem_ok segs E m rs -> win_check rs a n = true -> frame_of E rs m m' -> 0 <= a -> a + n <= 2 ^ 64 ->
forall x, a <= x < a + n -> mbyte segs m' x = mbyte segs m x.
Proof.
intros E m m' rs a n HM Hck HF Ha Han x Hx. unfold mbyte. rewrite (HF (Z_to_bv 64 x)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
eapply win_not_wrange; eassumption.
Qed.
Theorem rz_read_win : forall E ss ms model fd pth off data bs (a cnt : Z) T,
m_halted model = None -> m_vm_lazy model = [] ->
st_ok_ecall segs E ss ms -> ss_resv ss = None ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 17%bv)) = 63 ->
sv_denot E (sr_get (ss_regs ss) 10%bv) = fd -> fd32 fd = fd ->
fd_lookup (m_fds model) fd = Some (FdFile pth off) ->
fs_lookup (m_fs model) pth = Some data ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 11%bv)) = a ->
bv_unsigned (sv_denot E (sr_get (ss_regs ss) 12%bv)) = cnt -> 0 < cnt <= 65536 ->
file_read data off (sv_denot E (sr_get (ss_regs ss) 12%bv)) = bs ->
win_check (ss_mem ss) a 65536 = true -> seg_win_check a (Z.to_nat 65536) = true -> 0 <= a -> a + 65536 <= 2 ^ 47 ->
(forall regs,
regs_ok E (ss_regs ss) regs -> facts_ok E (ss_facts ss) ->
mem_ok segs E (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (ss_mem ss) ->
(forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs (wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (a + i) = nth_error bs (Z.to_nat i)) ->
(forall x : word, bv_unsigned x < a \/ a + Z.of_nat (length bs) <= bv_unsigned x ->
wbytes (ms_mem ms) (Z_to_bv 64 a) bs x = ms_mem ms x) ->
Z.of_nat (length bs) <= cnt ->
realizes segs (mkCfg (mkst (regupd regs 10%bv (len_word bs)) (v_addi (Z_to_bv 64 (ss_pc ss)) 4)
(wbytes (ms_mem ms) (Z_to_bv 64 a) bs) (seg_rom segs))
(with_fds (fd_insert (m_fds model) fd (FdFile pth (off + len_word bs))) model)) T) ->
realizes segs (mkCfg ms model) T.
Proof.
intros E ss ms model fd pth off data bs a cnt T Hh Hlz HS Hrv H17 H10 H32 Hlk Hfs H11 H12 Hcnt Hbs Hck Hseg Ha0 Ha47 Hk.
destruct (st_ok_ecall_shape segs E ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
subst ms. cbn [ms_mem pend_at] in Hk.
pose proof (u64_range (sv_denot E (sr_get (ss_regs ss) 11%bv))) as Ra. rewrite H11 in Ra.
assert (Hlen : Z.of_nat (length bs) <= cnt).
{ rewrite <- Hbs. rewrite file_read_length. rewrite H12. lia. }
assert (HA : sv_denot E (sr_get (ss_regs ss) 11%bv) = Z_to_bv 64 a).
{ rewrite <- H11. rewrite Z_to_bv_bv_unsigned. reflexivity. }
assert (Hau : bv_unsigned (Z_to_bv 64 a) = a).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
destruct (read_dest_ok_w segs mem (Z_to_bv 64 a) bs) as [w Hw].
{ intros i Hi. rewrite Hau. apply (seg_win_wview a 65536 mem); [exact Hseg | lia | lia]. }
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
+ apply (mem_ok_win E mem _ (ss_mem ss) a 65536 Hmem Hck).
intros x Hx64 Hx. apply Hout. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
+ intros i Hi. unfold mbyte.
rewrite (wbytes_inside' bs mem (Z_to_bv 64 a) (Z_to_bv 64 (a + i))) by (rewrite ?Hau, ?Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite ?Z.mod_small by lia; lia).
rewrite Hau. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
replace (a + i - a) with i by lia. symmetry. apply nth_error_nth'. lia.
+ exact Hout.
+ exact Hlen.
Qed.
End e.
End d.
