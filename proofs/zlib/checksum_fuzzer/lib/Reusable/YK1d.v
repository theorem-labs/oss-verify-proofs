(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK16 YK0n YK0i YK1i.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope bv_scope.
Lemma in_arg1_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma syscall_spec_read : forall segs ms x8 model o,
bv_unsigned x8 = 63%Z ->
(syscall_spec (sys_input segs ms x8) model o
<-> read_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(sys_input segs ms x8) model o).
Proof.
intros segs ms x8 model o Hno.
unfold syscall_spec, dispatch.
change (in_sysno (sys_input segs ms x8)) with x8.
rewrite Hno. reflexivity.
Qed.
Lemma in_arg2_sys_input : forall segs ms x8,
in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_wmem_sys_input : forall segs ms x8,
in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.
Lemma band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof.
apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.
Lemma m_fs_with_stdin : forall s m, m_fs (with_stdin s m) = m_fs m.
Proof. reflexivity. Qed.
Lemma m_halted_with_stdin : forall s m, m_halted (with_stdin s m) = m_halted m.
Proof. reflexivity. Qed.
Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.
Lemma m_vm_lazy_with_stdin : forall s m,
m_vm_lazy (with_stdin s m) = m_vm_lazy m.
Proof. reflexivity. Qed.
Definition M_loop (model : Model) : Prop :=
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) /\
fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) /\
m_halted model = None /\
m_vm_lazy model = [].
Lemma init_M_loop : forall reserved brk0 mb sp lim inp,
M_loop (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp. repeat split. Qed.
Lemma M_loop_take : forall k model,
M_loop model ->
M_loop (with_stdin (snd (stream_take (m_stdin model) k)) model).
Proof. intros k model (H0 & H1 & Hh & Hlazy). repeat split; assumption. Qed.
Lemma M_loop_fd1chan : forall model, M_loop model -> fd1chan model.
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.
Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
match n with
| O => true
| S n' =>
match find_segment segs (bv_unsigned a) 1 with
| Some seg =>
(seg_writable seg
&& match segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
| Some _ => true
| None => false
end
&& wseg_ok segs (a + 1) n')%bool
| None => false
end
end.
Lemma wseg_ok_read_aux : forall segs n a ms,
wseg_ok segs a n = true ->
exists w, read_bytes_aux (ms_writable_byte segs ms) a n = Some w.
Proof.
intros segs n; induction n as [|n IH]; intros a ms H.
- exists []. reflexivity.
- cbn [wseg_ok] in H.
destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
apply andb_true_iff in H as [H Hrec].
apply andb_true_iff in H as [Hwr Hbyte].
destruct (segment_byte_at (seg_bytes seg)
(Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
[|discriminate].
destruct (IH (a + 1) ms Hrec) as [w Hw].
cbn [read_bytes_aux].
assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
{ unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
- eexists; reflexivity.
- rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.
Lemma wseg_ok_wdef : forall segs (a len : word) ms,
wseg_ok segs a (word_to_nat len) = true ->
exists w, read_bytes_map (ms_writable_byte segs ms) a len = Some w.
Proof.
intros segs a len ms H. rewrite read_bytes_map_eq.
apply wseg_ok_read_aux. exact H.
Qed.
Lemma read0_wmem1 : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 w,
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
exists w1, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
(Z_to_bv 64 1) = Some w1.
Proof.
intros cnt Hcnt segs ms x8 w Hw. rewrite in_wmem_sys_input.
eexists. apply (read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w);
[rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; lia | exact Hw].
Qed.
Lemma read0_wmem_need : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 w s,
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
exists wn, read_bytes_map (in_wmem (sys_input segs ms x8)) (ms_gpr ms 1)
(len_word (fst (stream_take_z s (rw_count_clamp cnt)))) = Some wn.
Proof.
intros cnt Hcnt segs ms x8 w s Hw. rewrite in_wmem_sys_input.
eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
rewrite stream_take_z_eq.
pose proof (stream_take_length (Z.to_nat (rw_count_clamp cnt)) s) as Hlen.
pose proof (rw_count_clamp_range cnt) as Hcl.
unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
unfold bv_modulus, MAX_RW_COUNT in *; cbn [Z.of_N] in *;
[ | pose proof (bv_unsigned_in_range 64 cnt) ]; unfold rw_count_clamp in *; lia.
Qed.
Lemma read0_check_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
m_stdin model = IEof ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
check_read (sys_input segs ms x8)
(fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(mkEffect (Z_to_bv 64 0) [] []) model
= CheckOk model [].
Proof.
intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
unfold check_read.
rewrite Hg0; norm_fd32; rewrite Hfd.
cbv beta iota.
change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
rewrite Hg2, Haok.
cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
rewrite Heof. cbv beta iota.
unfold check_ret_only. rewrite bv_eqb_refl. reflexivity.
Qed.
Lemma read0_check_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 model w bs,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take (m_stdin model) (length bs)) = bs ->
check_read (sys_input segs ms x8)
(fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
(mkEffect (len_word bs) [(ms_gpr ms 1, bs)] []) model
= CheckOk (with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
(map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
unfold check_read.
rewrite Hg0; norm_fd32; rewrite Hfd.
cbv beta iota.
change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
rewrite Hg2, Haok.
cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
destruct (m_stdin model) as [|b0 s0] eqn:Hs.
{ exfalso. rewrite stream_take_nil_of_eof in Hpre. subst bs. cbn in Hlo. lia. }
cbv beta iota.
rewrite Hw1. cbv beta iota.
rewrite Hwn. cbv beta iota.
rewrite !bv_eqb_refl.
rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length bs))) Hlo).
rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)).
rewrite (proj2 (Z.leb_le (Z.of_nat (length bs)) (bv_unsigned cnt)) Hhi).
rewrite (proj2 (listN_eqb_eq _ _) Hpre).
rewrite <- (in_wmem_sys_input segs ms x8) in Hw.
assert (Hlek : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
{ unfold len_word. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hhi | lia]. }
rewrite (wmem_ok_of_full _ _ _ _ _ Hw Hlek).
reflexivity.
Qed.
Lemma read0_ok_eof : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
m_stdin model = IEof ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (Z_to_bv 64 0) [] []) model []).
Proof.
intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
apply check_read_sound_ok. eapply read0_check_eof; eassumption.
Qed.
Lemma read0_ok_bytes : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 model w bs,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
(1 <= Z.of_nat (length bs))%Z -> (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take (m_stdin model) (length bs)) = bs ->
syscall_spec (sys_input segs ms x8) model
(Ok (mkEffect (len_word bs) [(ms_gpr ms 1, bs)] [])
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model)
(map (ReadEv (Z_to_bv 64 0)) bs)).
Proof.
intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
apply check_read_sound_ok. eapply read0_check_bytes; eassumption.
Qed.
Lemma read0_ok_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 model buf w eff model' evs,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
access_okb buf (bv_unsigned cnt) = true ->
syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
(m_stdin model = IEof /\ eff = mkEffect (Z_to_bv 64 0) [] [] /\
model' = model /\ evs = [])
\/ (exists bs,
(1 <= Z.of_nat (length bs))%Z /\
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
fst (stream_take (m_stdin model) (length bs)) = bs /\
eff = mkEffect (len_word bs) [(buf, bs)] [] /\
model' = with_stdin (snd (stream_take (m_stdin model) (length bs))) model /\
evs = map (ReadEv (Z_to_bv 64 0)) bs).
Proof.
intros cnt Hcnt segs ms x8 model buf w eff model' evs
Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec.
destruct (read0_wmem1 cnt Hcnt segs ms x8 w) as [w1 Hw1];
[rewrite Hg1; exact Hw|].
rewrite Hg1 in Hw1.
destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model)) as [wn Hwn];
[rewrite Hg1; exact Hw|].
rewrite Hg1 in Hwn.
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
apply check_read_complete_ok in Hspec.
unfold check_read in Hspec.
rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
cbv beta iota in Hspec.
change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
cbv beta iota in Hspec.
rewrite Hg1, Hg2, Haok in Hspec.
cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
-
apply check_ret_only_ok_iff in Hspec.
destruct Hspec as (-> & -> & ->). left. auto.
-
rewrite Hw1 in Hspec. cbv beta iota in Hspec.
rewrite Hwn in Hspec. cbv beta iota in Hspec.
destruct eff as [ret ws zs us cs copyins].
destruct ws as [|[a bs] [|w2 ws]]; [discriminate| |discriminate].
destruct zs as [|z zs]; [|discriminate].
destruct us as [|u us]; [|discriminate].
destruct cs as [|c cs]; [|discriminate].
destruct copyins as [|copyin copyins]; [|discriminate].
destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
&& (1 <=? Z.of_nat (length bs))%Z
&& (Z.of_nat (length bs) <=? rw_count_clamp cnt)%Z
&& listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
&& wmem_ok (sys_input segs ms x8) buf (len_word bs)) eqn:Hb;
try rewrite Hb in Hspec; [|discriminate].
inversion Hspec; subst.
apply andb_true_iff in Hb as [Hb _].
apply andb_true_iff in Hb as [Hb HE].
apply andb_true_iff in Hb as [Hb HD].
apply andb_true_iff in Hb as [Hb HC].
apply andb_true_iff in Hb as [HA HB].
apply bv_eqb_eq in HA; subst a.
apply bv_eqb_eq in HB; subst ret.
apply Z.leb_le in HC. apply Z.leb_le in HD.
rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)) in HD.
apply listN_eqb_eq in HE.
right. exists bs. repeat split; try assumption; reflexivity.
Qed.
Lemma read0_no_unmodeled : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms x8 model w,
bv_unsigned x8 = 63%Z ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) cnt = Some w ->
access_okb (ms_gpr ms 1) (bv_unsigned cnt) = true ->
~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
intros cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok Hspec.
destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
apply (check_read_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
in Hspec.
unfold check_read in Hspec.
rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
cbv beta iota in Hspec.
change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
cbv beta iota in Hspec.
rewrite Hg2, Haok in Hspec.
cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
{ now apply check_ret_only_no_unmodeled in Hspec. }
rewrite Hw1 in Hspec. cbv beta iota in Hspec.
rewrite Hwn in Hspec. cbv beta iota in Hspec. discriminate.
Qed.
Lemma sstep_read_inv : forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall segs ms model buf x8 w evs st,
m_halted model = None ->
m_vm_lazy model = [] ->
fd_lookup (m_fds model) (Z_to_bv 64 0) = Some (FdChannel (Z_to_bv 64 0)) ->
ms_svc_pending ms = Some x8 ->
bv_unsigned x8 = 63%Z ->
ms_gpr ms 0 = Z_to_bv 64 0 -> ms_gpr ms 1 = buf -> ms_gpr ms 2 = cnt ->
read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w ->
access_okb buf (bv_unsigned cnt) = true ->
sstep segs (mkCfg ms model) evs st ->
(m_stdin model = IEof /\ evs = [] /\
st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model))
\/ (exists bs,
(1 <= Z.of_nat (length bs))%Z /\
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
fst (stream_take (m_stdin model) (length bs)) = bs /\
evs = map (ReadEv (Z_to_bv 64 0)) bs /\
st = SNext (mkCfg
(advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))
(with_stdin (snd (stream_take (m_stdin model) (length bs)))
model))).
Proof.
intros cnt Hcnt segs ms model buf x8 w evs st
Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss.
inversion Hss; subst; try congruence.
-
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(Hs & Heff & Hm & Hevs) | (bs & Hlo & Hhi & Hpre & Heff & Hm & Hevs)];
subst eff model' evs0
end.
+ match goal with
| Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
inversion Hmat; subst model''
end.
left. rewrite apply_effect_no_write.
split; [exact Hs | split; reflexivity].
+ match goal with
| Hmat : materialize_model_accesses
(with_stdin ?s model) _ = Some ?model'' |- _ =>
rewrite (materialize_model_accesses_no_lazy (with_stdin s model) _)
in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy);
inversion Hmat; subst model''
end.
right. exists bs. repeat split; try assumption; reflexivity.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
Hmat : materialize_model_accesses ?model' _ = None |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
subst model';
[ rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat
| rewrite (materialize_model_accesses_no_lazy
(with_stdin (snd (stream_take (m_stdin model) (length bs))) model) _)
in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy) ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_halted ?model' = Some ?code |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
subst model'; [|rewrite m_halted_with_stdin in H6]; congruence
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
H6 : m_killed ?model' = Some ?sig |- _ =>
assert (Hx : x = x8) by congruence; subst x;
destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
subst model';
[ rewrite (m_killed_of_m_halted_none model Hh) in H6
| rewrite (m_killed_of_m_halted_none _
(eq_trans (m_halted_with_stdin _ model) Hh)) in H6 ];
discriminate
end.
-
exfalso.
match goal with
| H2 : ms_svc_pending ms = Some ?x,
H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
assert (Hx : x = x8) by congruence; subst x;
exact (read0_no_unmodeled _ Hcnt segs ms x8 model w Hno Hfd Hg0 eq_refl Hw
Haok H3)
end.
Qed.
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
fst (stream_take s (length bs)) = bs ->
chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
chunks cnt s (bs :: blocks) s''.
Lemma chunks_app : forall cnt s l1 s1 l2 s2,
chunks cnt s l1 s1 -> chunks cnt s1 l2 s2 -> chunks cnt s (l1 ++ l2) s2.
Proof.
intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
intros l2 s2 H2; cbn [app]; [exact H2|].
eapply chunks_cons; eauto.
Qed.
Lemma chunks_split : forall cnt l1 l2 s s2,
chunks cnt s (l1 ++ l2) s2 ->
exists s1, chunks cnt s l1 s1 /\ chunks cnt s1 l2 s2.
Proof.
intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
- exists s. split; [constructor | exact H].
- inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.
Lemma chunks_single_inv : forall cnt s bs s',
chunks cnt s [bs] s' ->
(1 <= Z.of_nat (length bs))%Z /\
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z /\
fst (stream_take s (length bs)) = bs /\
s' = snd (stream_take s (length bs)).
Proof.
intros cnt s bs s' H.
inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
inversion HC; subst.
repeat split; assumption || reflexivity.
Qed.
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.
Definition iter_ev (bs : list byte) : list event :=
iter_ev_ch (Z_to_bv 64 0) bs.
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
match s with
| IEof => [ExitEv (Z_to_bv 64 0) fs]
| ICons _ _ => []
end.
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
(s : InputStream) (tr : list event) : Prop :=
exists blocks s',
chunks cnt s blocks s' /\
is_prefix tr (flat_map (iter_ev_ch rch) blocks ++ eof_tail s' fs).
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
(tr : list event) : Prop :=
stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.
Lemma stream_traces_ch_prefix_closed : forall rch cnt fs s tr tr',
stream_traces_ch rch cnt fs s tr -> is_prefix tr' tr ->
stream_traces_ch rch cnt fs s tr'.
Proof.
intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.
Lemma stream_traces_prefix_closed : forall cnt fs s tr tr',
stream_traces cnt fs s tr -> is_prefix tr' tr -> stream_traces cnt fs s tr'.
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.
Section d.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.
Definition lh_next (ms : machine_state) : Prop :=
exists ms', msteps segs ms ms' /\ LH ms'.
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
(1 <= length bs)%nat /\
to_wall segs (Z_to_bv 64 1) ms bs lh_next.
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_wr bs ms' -> to_wr bs ms.
Definition ReadPend (ms : machine_state) : Prop :=
exists buf x8,
ms_svc_pending ms = Some x8 /\
bv_unsigned x8 = 63%Z /\
ms_gpr ms 0 = Z_to_bv 64 0 /\
ms_gpr ms 1 = buf /\
ms_gpr ms 2 = cnt /\
(exists w, read_bytes_map (ms_writable_byte segs ms) buf cnt = Some w) /\
access_okb buf (bv_unsigned cnt) = true /\
to_exit segs (Z_to_bv 64 0) (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) /\
(forall bs,
(1 <= Z.of_nat (length bs))%Z ->
(Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
to_wr bs (advance_past_svc (apply_effect ms
(mkEffect (len_word bs) [(buf, bs)] [])))).
Lemma msteps_to_wr : forall bs ms ms',
msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
intros bs ms ms' H; induction H; [auto|].
intro Hwr. eapply twr_step; eauto.
Qed.
Lemma to_wr_wall_tail : forall bs ms,
to_wr bs ms -> to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next.
Proof.
intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
- destruct HWP as [Hnb Hw]. apply twt_more; assumption.
- eapply twt_step; eauto.
Qed.
Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
to_rd ms' -> to_rd ms.
Lemma msteps_to_rd : forall ms ms',
msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
intros ms ms' H; induction H; [auto|].
intro Hrd. eapply trd_step; eauto.
Qed.
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.
Lemma lh_next_to_rd : forall ms, lh_next ms -> to_rd ms.
Proof.
intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.
Lemma to_rd_star : forall ms model,
m_halted model = None -> m_vm_lazy model = [] -> to_rd ms ->
exists msR, ReadPend msR /\
star segs (mkCfg ms model) [] (mkCfg msR model).
Proof.
intros ms model Hh Hlazy Hrd.
induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
- exists ms. split; [exact HRP | apply star_refl].
- destruct IH as (msR & HRP & Hstar).
exists msR. split; [exact HRP|].
change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma to_wr_star : forall bs ms model,
m_halted model = None -> m_vm_lazy model = [] -> to_wr bs ms ->
exists msW, WrPend bs msW /\
star segs (mkCfg ms model) [] (mkCfg msW model).
Proof.
intros bs ms model Hh Hlazy Hwr.
induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
- exists ms. split; [exact HWP | apply star_refl].
- destruct IH as (msW & HWP & Hstar).
exists msW. split; [exact HWP|].
change ([] : list event) with (([] : list event) ++ []).
eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
try assumption.
rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.
Lemma stream_star_admits : forall s blocks s',
chunks cnt s blocks s' ->
forall ms model,
M_loop model -> m_stdin model = s -> to_rd ms ->
exists c, star segs (mkCfg ms model)
(flat_map iter_ev blocks ++ eof_tail s' (m_fs model)) c.
Proof.
intros s blocks s' HC.
induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
intros ms model HM Hst Hrd; pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
-
cbn [flat_map app].
destruct s as [|b0 s0] eqn:Hs.
+
destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & _).
destruct (to_exit_star_admits segs (Z_to_bv 64 0)
(advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex)
as [c Hstar2].
exists c.
assert (HssE : sstep segs (mkCfg msR model) []
(SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
model))).
{ rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
model model []);
[exact Hh | exact Hsvc | | exact Hh |].
- rewrite <- Hg1 in Hw, Haok. eapply (read0_ok_eof cnt Hcnt); eassumption.
- rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
cbn [eof_tail].
replace [ExitEv (Z_to_bv 64 0) (m_fs model)]
with (([] : list event)
++ ([] ++ [ExitEv (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255))
(m_fs model)]))
by (rewrite band0_255; reflexivity).
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssE | exact Hstar2].
+
cbn [eof_tail app]. exists (mkCfg ms model). apply star_refl.
-
destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
pose proof (Hbytes bs Hlo Hhi) as Hwr.
set (advB := advance_past_svc (apply_effect msR
(mkEffect (len_word bs) [(buf, bs)] []))) in *.
set (model' := with_stdin (snd (stream_take s (length bs))) model).
assert (Hh' : m_halted model' = None) by exact Hh.
assert (HM' : M_loop model')
by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
(SNext (mkCfg advB model'))).
{ apply (sstep_syscall segs msR model x8
(mkEffect (len_word bs) [(buf, bs)] []) model' model'
(map (ReadEv (Z_to_bv 64 0)) bs));
[exact Hh | exact Hsvc | | exact Hh' |].
- unfold model'. rewrite <- Hst. rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
eapply (read0_ok_bytes cnt Hcnt); try eassumption.
rewrite Hst. exact Hpre.
- rewrite (materialize_model_accesses_no_lazy model' _ (proj2 (proj2 (proj2 HM')))).
reflexivity. }
assert (Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model')
by (apply fd1chan_fdchan; exact Hfd1).
assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
by reflexivity.
assert (Hcont : forall ms', lh_next ms' ->
exists c, star segs (mkCfg ms' model')
(flat_map iter_ev blocks ++ eof_tail s'' (m_fs model')) c).
{ intros ms' Hlh.
apply (IH ms' model' HM' Hst' (lh_next_to_rd ms' Hlh)). }
destruct (to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1)
fd32_1 advB bs lh_next (to_wr_wall_tail bs advB Hwr) Hbmbs
model' _ Hh' (proj2 (proj2 (proj2 HM'))) Hfdc' Hcont) as [c Hstar1].
exists c.
change (m_fs model') with (m_fs model) in Hstar1.
cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
rewrite <- !app_assoc.
replace (map (ReadEv (Z_to_bv 64 0)) bs
++ map (WriteEv (Z_to_bv 64 1)) bs
++ flat_map iter_ev blocks ++ eof_tail s'' (m_fs model))
with (([] : list event)
++ (map (ReadEv (Z_to_bv 64 0)) bs
++ (map (WriteEv (Z_to_bv 64 1)) bs
++ (flat_map iter_ev blocks
++ eof_tail s'' (m_fs model)))))
by reflexivity.
eapply star_trans; [exact Hstar0|].
eapply star_step; [exact HssR | exact Hstar1].
Qed.
Lemma star_loop_only : forall c0 tr c', star segs c0 tr c' ->
forall ms model, c0 = mkCfg ms model -> M_loop model ->
(to_rd ms ->
exists blocks s', chunks cnt (m_stdin model) blocks s' /\
is_prefix tr (flat_map iter_ev blocks ++ eof_tail s' (m_fs model)))
/\ (forall bs, (1 <= length bs)%nat -> buf_modeled bs ->
to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next ->
exists blocks s',
chunks cnt (m_stdin model) blocks s' /\
is_prefix tr (map (WriteEv (Z_to_bv 64 1)) bs
++ flat_map iter_ev blocks
++ eof_tail s' (m_fs model))).
Proof.
intros c0 tr c' Hstar.
induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
intros ms model Heq HM; subst.
-
split.
+ intros _. exists [], (m_stdin model).
split; [constructor | apply is_prefix_nil].
+ intros bs _ _ _. exists [], (m_stdin model).
split; [constructor | apply is_prefix_nil].
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
split.
+
intro Hrd. destruct Hrd as [ms (buf & x8 & HRP) | ms ms' Hsvc Hstep Hrd'].
*
destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
--
destruct (to_exit_star_only segs (Z_to_bv 64 0)
(advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
Hh Hlazy Hex tr2 c3 Hstar) as [-> | ->].
++ exists [], (m_stdin model).
split; [constructor | apply is_prefix_nil].
++ exists [], (m_stdin model).
split; [constructor|].
rewrite Hs, band0_255. cbn [flat_map app eof_tail].
apply is_prefix_refl.
--
assert (Hnb : (1 <= length bs)%nat) by lia.
assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
destruct (proj2 (IH _ _ eq_refl (M_loop_take (length bs) model HM)) bs
Hnb Hbmbs (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)))
as (blocks & s' & HCb & Hp).
exists (bs :: blocks), s'.
split; [eapply chunks_cons; eassumption|].
cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
rewrite <- !app_assoc.
apply is_prefix_app_mono. exact Hp.
*
destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
inversion Hc2; subst.
exact (proj1 (IH _ model eq_refl HM) Hrd').
+
intros bs Hnb Hbm Hwt.
inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl | msS msS' restS kS HsvcS HstepS Hwt']; subst.
*
cbn in Hnb. lia.
*
destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs lh_next model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss)
as (n & Hn1 & Hn2 & Hevs & Hc2 & Hwt2).
inversion Hc2; subst.
set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
--
rewrite skipn_all in Hwt2.
destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
as (msL & HmL & HlhL).
destruct (proj1 (IH _ model eq_refl HM)
(msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)))
as (blocks & s' & HCb & Hp).
exists blocks, s'. split; [exact HCb|].
rewrite firstn_all.
apply is_prefix_app_mono. exact Hp.
--
assert (Hnb' : (1 <= length (skipn n bs))%nat)
by (rewrite length_skipn; lia).
destruct (proj2 (IH _ model eq_refl HM) (skipn n bs) Hnb'
(buf_modeled_skipn n bs Hbm) Hwt2)
as (blocks & s' & HCb & Hp).
exists blocks, s'. split; [exact HCb|].
rewrite <- (firstn_skipn n bs) at 2.
rewrite map_app, <- app_assoc.
apply is_prefix_app_mono. exact Hp.
*
destruct (sstep_instr_inv segs ms model msS' evs (SNext c2)
Hlazy HsvcS HstepS Hss) as [Hevs Hc2].
inversion Hc2; subst.
exact (proj2 (IH _ model eq_refl HM) bs Hnb Hbm Hwt').
Qed.
Definition sinv (c : config) : Prop :=
(M_loop (cfg_model c) /\
(to_rd (cfg_ms c)
\/ exists bs, (1 <= length bs)%nat /\ buf_modeled bs /\
to_wall_tail segs (Z_to_bv 64 1) (cfg_ms c) bs lh_next))
\/ on_path segs (Z_to_bv 64 0) c.
Lemma sinv_step : forall c evs c',
sinv c -> sstep segs c evs (SNext c') -> sinv c'.
Proof.
intros [ms model] evs [ms' model'] Hinv Hss.
destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
+ destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
* destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs
(SNext (mkCfg ms' model'))
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
inversion Hc2; subst.
-- right. left. cbn. split; [exact Hh|].
split; [exact Hlazy | exact Hex].
-- left. cbn. split; [apply M_loop_take; exact HM|].
right. exists bs. split; [lia|].
split; [unfold buf_modeled; lia|].
exact (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)).
* destruct (sstep_instr_inv segs ms model ms1 evs
(SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
inversion Hc2; subst.
left. cbn. split; [exact HM | left; exact Hrd'].
+ inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
| msS msS' restS kS HsvcS HstepS Hwt']; subst.
*
cbn in Hnb. lia.
*
destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs lh_next model evs (SNext (mkCfg ms' model'))
Hh Hlazy Hfdc Hbm Hwl Hss)
as (n & Hn1 & Hn2 & _ & Hc2 & Hwt2).
inversion Hc2; subst.
set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
--
rewrite skipn_all in Hwt2.
destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
as (msL & HmL & HlhL).
left. cbn. split; [exact HM|].
left. exact (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)).
--
left. cbn. split; [exact HM|].
right. exists (skipn n bs).
split; [rewrite length_skipn; lia|].
split; [apply buf_modeled_skipn; exact Hbm | exact Hwt2].
* destruct (sstep_instr_inv segs ms model msS' evs
(SNext (mkCfg ms' model')) Hlazy HsvcS HstepS Hss) as [_ Hc2].
inversion Hc2; subst.
left. cbn. split; [exact HM|].
right. exists bs.
split; [exact Hnb | split; [exact Hbm | exact Hwt']].
- right. eapply on_path_step; eauto.
Qed.
Lemma sinv_no_error : forall c evs, sinv c -> ~ sstep segs c evs SError.
Proof.
intros [ms model] evs Hinv Hss.
destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
- pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
by (apply fd1chan_fdchan; exact Hfd1).
destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
+ destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
* destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
* destruct (sstep_instr_inv segs ms model ms1 evs SError
Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
+ inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
| msS msS' restS kS HsvcS HstepS Hwt']; subst.
* cbn in Hnb. lia.
* exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
ms bs lh_next model evs Hh Hlazy Hfdc Hbm Hwl Hss).
* destruct (sstep_instr_inv segs ms model msS' evs SError
Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
- eapply on_path_no_error; eauto.
Qed.
Lemma star_sinv : forall c tr c', sinv c -> star segs c tr c' -> sinv c'.
Proof. exact (star_inv segs sinv sinv_step). Qed.
Lemma to_rd_no_error : forall ms model,
M_loop model -> to_rd ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
intros ms model HM Hrd.
apply (inv_no_reaches_error segs sinv sinv_step sinv_no_error).
left; cbn; auto.
Qed.
Lemma stream_obs_iff : forall pc ph sp brk0 mb rnd lim inp,
to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
forall tr, obs_trace segs (init_config segs pc ph sp brk0 mb rnd lim inp) tr
<-> stream_traces cnt (in_fs inp) (in_stdin inp) tr.
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd tr.
set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
unfold init_config.
set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
split.
- intros (tr' & c & Hstar & Hp).
destruct (proj1 (star_loop_only _ _ _ Hstar ms0 model0 eq_refl HM0) Hrd)
as (blocks & s' & HC & Hp').
rewrite Hst0 in HC. rewrite Hfs0 in Hp'.
apply (stream_traces_prefix_closed cnt fs0 stdin0 tr'); [|exact Hp].
exists blocks, s'. split; assumption.
- intros (blocks & s' & HC & Hp).
destruct (stream_star_admits stdin0 blocks s' HC ms0 model0 HM0 Hst0 Hrd)
as [c Hstar].
rewrite Hfs0 in Hstar.
exists (flat_map iter_ev blocks ++ eof_tail s' fs0), c.
split; assumption.
Qed.
Lemma stream_no_error : forall pc ph sp brk0 mb rnd lim inp,
to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp).
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd.
apply to_rd_no_error; [apply init_M_loop | exact Hrd].
Qed.
Lemma to_rd_coexec : forall ms model,
M_loop model -> to_rd ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
intros ms model HM Hrd.
apply (inv_coexec segs sinv sinv_step sinv_no_error). left; cbn; auto.
Qed.
Lemma stream_omni_corun : forall pc ph sp brk0 mb rnd lim inp,
to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_corun]. unfold init_config.
apply to_rd_coexec; [apply init_M_loop | exact Hrd].
Qed.
Lemma stream_omni_cosafe : forall pc ph sp brk0 mb rnd lim inp,
to_rd (init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_cosafe (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
(stream_traces cnt (in_fs inp) (in_stdin inp)).
Proof.
intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_cosafe].
apply cosafe_obs_iff.
- intros t t' Ht Hp. eapply stream_traces_prefix_closed; eauto.
- intros tr Hobs. apply (stream_obs_iff pc ph sp brk0 mb rnd lim inp Hrd). exact Hobs.
Qed.
End d.
Lemma stream_omni_strong_equiv :
forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd inp,
(forall ms, rLH ms -> to_rd source_segs rLH cnt ms) ->
(forall ms, aLH ms -> to_rd target_segs aLH cnt ms) ->
to_rd source_segs rLH cnt (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_rd target_segs aLH cnt (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
(mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
inp HrLH HaLH Hr Ha.
split.
{ cbn [img_segments].
eapply coexec_conseq;
[exact (stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
source_alloc_limit inp Hr) | apply never_errors_covered]. }
right. split.
- apply trace_equiv_iff_omni. intro tr. cbn.
rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr tr).
rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha tr).
reflexivity.
- exact (stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha).
Qed.
Lemma stream_strong_equiv :
forall cnt : word, (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
forall source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim inp,
(forall ms, rLH ms -> to_rd source_segs rLH cnt ms) ->
(forall ms, aLH ms -> to_rd target_segs aLH cnt ms) ->
to_rd source_segs rLH cnt (init_machine_state source_segs rpc rph rsp rrnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
to_rd target_segs aLH cnt (init_machine_state target_segs apc aph asp arnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) ->
Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
(run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
inp HrLH HaLH Hr Ha.
split.
{ apply no_error_run_modeled.
apply (stream_no_error source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr). }
right. split.
- intro tr. cbn.
rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr tr).
rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha tr).
reflexivity.
- cbn. apply (stream_no_error target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha).
Qed.
