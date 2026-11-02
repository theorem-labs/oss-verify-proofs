(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL08.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0h.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK1a.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0m.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YP0e.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP0l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP04.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3v.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN3l.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YL07.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section g.
Variable segs : list Segment.
Definition img_covered (rs : smem) (a n : Z) : bool :=
existsb (fun r => obase_eqb (r_base r) None &&
existsb (fun c => match c_val c with
| CImg _ => (c_off c <=? a) && (a + n <=? c_off c + c_len c)
| _ => false
end) (r_chunks r)) rs.
Lemma img_covered_sound : forall E m rs a n,
mem_ok segs E m rs -> img_covered rs a n = true ->
forall x, a <= x < a + n -> mbyte segs m x = seg_rom segs (Z_to_bv 64 x).
Proof.
intros E m rs a n HM H x Hx. unfold img_covered in H.
apply existsb_In in H as (r & Hr & H). apply andb_prop in H as [Hb H].
apply obase_eqb_eq in Hb.
apply existsb_In in H as (c & Hc & H).
pose proof (region_ok_chunk segs E m r c (mem_ok_region segs E m rs r HM Hr) Hc) as Hck.
rewrite Hb in Hck. cbn [base_val] in Hck.
destruct (c_val c) as [| | l |] eqn:Hv; try discriminate.
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
destruct (Hck (x - c_off c)) as (b & Hb1 & Hb2); [lia|].
rewrite Hv in Hb1. cbn [cbyte] in Hb1. unfold img_byte in Hb1.
replace (0 + c_off c + (x - c_off c)) with x in * by lia. rewrite Hb2, Hb1. reflexivity.
Qed.
Definition zero_check (rs : smem) (vb : sv) (n : nat) : bool :=
match lit_buf segs rs vb n with Some zs => forallb (Z.eqb 0) zs | None => false end.
Lemma zero_check_sound : forall E m rs vb n,
mem_ok segs E m rs -> zero_check rs vb n = true ->
forall i, 0 <= i < Z.of_nat n -> mbyte segs m (bv_unsigned (sv_denot E vb) + i) = Some (Z_to_bv 8 0).
Proof.
intros E m rs vb n HM H i Hi. unfold zero_check in H.
destruct (lit_buf segs rs vb n) as [zs|] eqn:Hl; [|discriminate].
pose proof (lit_buf_sound segs E m rs vb n zs HM Hl) as Hr.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E vb)) in Hr.
apply rdn_mbytes in Hr as [Hlen Hb].
rewrite <- (Z2Nat.id i) by lia. rewrite (Hb (Z.to_nat i)) by lia.
rewrite length_map in Hlen.
destruct (nth_error zs (Z.to_nat i)) as [z|] eqn:Hz.
- pose proof (forallb_In _ _ z H ltac:(eapply nth_error_In; eauto)) as Hz0. apply Z.eqb_eq in Hz0. subst z.
erewrite map_nth_error by exact Hz. reflexivity.
- apply nth_error_None in Hz. lia.
Qed.
Definition word_check (rs : smem) (vb : sv) (v : Z) : bool :=
match lit_buf segs rs vb 8 with
| Some zs => zlist_eqb zs (map (fun k => le_byte v 8 k) (seq 0 8))
| None => false
end.
Lemma word_check_sound : forall E m rs vb v,
mem_ok segs E m rs -> word_check rs vb v = true ->
word_mem segs m (bv_unsigned (sv_denot E vb)) v.
Proof.
intros E m rs vb v HM H k Hk. unfold word_check in H.
destruct (lit_buf segs rs vb 8) as [zs|] eqn:Hl; [|discriminate].
apply zlist_eqb_eq in H. subst zs.
pose proof (lit_buf_sound segs E m rs vb 8 _ HM Hl) as Hr.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E vb)) in Hr.
apply rdn_mbytes in Hr as [Hlen Hb].
rewrite (Hb k Hk). rewrite nth_error_map.
rewrite nth_error_map. rewrite (nth_error_nth' _ 0%nat) by (rewrite length_seq; exact Hk).
rewrite seq_nth by exact Hk. reflexivity.
Qed.
Definition svword_at (rs : smem) (b : option nat) (off : Z) : option sv :=
match find_region rs b off 8 with
| Some r =>
match find_chunk (r_chunks r) off 8 with
| Some c => match c_val c with
| CVal 8 v => if c_off c =? off then Some v else None
| _ => None
end
| None => None
end
| None => None
end.
Lemma le_byte_of_word : forall (w : word) k, (k < 8)%nat ->
Z_to_bv 8 (le_byte (bv_unsigned w) 8 k) = byte_of_word w (Z.of_nat k).
Proof.
intros w k Hk. unfold le_byte, byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned.
pose proof (u64_range w).
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small (bv_unsigned w)) by lia.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma svword_at_sound : forall E m rs b off v,
mem_ok segs E m rs -> svword_at rs b off = Some v ->
word_mem segs m (base_val E b + off) (bv_unsigned (sv_denot E v)).
Proof.
intros E m rs b off v HM H k Hk. unfold svword_at in H.
destruct (find_region rs b off 8) as [r|] eqn:Hr; [|discriminate].
destruct (find_chunk (r_chunks r) off 8) as [c|] eqn:Hc; [|discriminate].
apply find_region_sound in Hr as (Hin & Hb & _ & _).
apply find_chunk_sound in Hc as (Hcin & Hlo & Hhi).
pose proof (region_ok_chunk segs E m r c (mem_ok_region segs E m rs r HM Hin) Hcin) as Hck. rewrite Hb in Hck.
destruct (c_val c) as [w v'| | |] eqn:Hv; try discriminate.
destruct w as [|p]; try discriminate. do 4 (destruct p as [p|p|]; try discriminate).
destruct (Z.eqb_spec (c_off c) off); [|discriminate]. injection H as <-. subst off.
destruct (Hck (Z.of_nat k)) as (bt & H1 & H2); [unfold c_len; rewrite Hv; cbn; lia|].
rewrite Hv in H1. cbn [cbyte] in H1. injection H1 as <-. rewrite H2. f_equal. symmetry. apply le_byte_of_word. exact Hk.
Qed.
Definition sdata_at (rs : smem) (b : option nat) (off : Z) : bool :=
match find_region rs b off 8 with
| Some r =>
match find_chunk (r_chunks r) off 8 with
| Some c => match c_val c with CData _ _ _ => true | _ => false end
| None => false
end
| None => false
end.
Lemma nth_map_seq : forall {A} (f : nat -> A) k n d, (k < n)%nat -> nth k (map f (seq 0 n)) d = f k.
Proof.
intros A f k n d Hk. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
Lemma le_byte_bytes_le_to_Z : forall (bs : list byte) k,
length bs = 8%nat -> (k < 8)%nat ->
le_byte (bytes_le_to_Z bs) 8 k = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
intros bs k Hlen Hk. pose proof (bytes_le_to_Z_range bs Hlen) as Hr.
unfold le_byte. replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity.
rewrite (Z.mod_small (bytes_le_to_Z bs) (2 ^ 64)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite <- (zb_of_bytes bs k) by lia. unfold HZ.zb. reflexivity.
Qed.
Lemma sdata_at_sound : forall E m rs b off,
mem_ok segs E m rs -> sdata_at rs b off = true ->
exists v, 0 <= v < 2 ^ 64 /\ word_mem segs m (base_val E b + off) v.
Proof.
intros E m rs b off HM H. unfold sdata_at in H.
destruct (find_region rs b off 8) as [r|] eqn:Hr; [|discriminate].
destruct (find_chunk (r_chunks r) off 8) as [c|] eqn:Hc; [|discriminate].
apply find_region_sound in Hr as (Hin & Hb & _ & _).
apply find_chunk_sound in Hc as (Hcin & Hlo & Hhi).
pose proof (region_ok_chunk segs E m r c (mem_ok_region segs E m rs r HM Hin) Hcin) as Hck. rewrite Hb in Hck.
destruct (c_val c) as [w v'| | |d s len] eqn:Hv; try discriminate.
set (byte_at := fun k : nat => match nth_error (ed E d) (Z.to_nat (s + (off - c_off c + Z.of_nat k))) with
| Some bt => bt | None => Z_to_bv 8 0 end).
set (bs := map byte_at (seq 0 8)).
assert (Hlen : length bs = 8%nat) by (subst bs; rewrite length_map, length_seq; reflexivity).
exists (bytes_le_to_Z bs). split; [apply bytes_le_to_Z_range; exact Hlen|].
intros k Hk. rewrite (le_byte_bytes_le_to_Z bs k Hlen Hk).
destruct (Hck (off - c_off c + Z.of_nat k)) as (bt & H1 & H2); [unfold c_len; rewrite Hv; cbn [cv_len]; unfold c_len in Hhi; rewrite Hv in Hhi; cbn [cv_len] in Hhi; lia|].
rewrite Hv in H1. cbn [cbyte] in H1.
replace (base_val E b + c_off c + (off - c_off c + Z.of_nat k)) with (base_val E b + off + Z.of_nat k) in H2 by lia.
rewrite H2. f_equal.
assert (Hnth : nth k bs (Z_to_bv 8 0) = bt).
{ subst bs. rewrite (nth_map_seq byte_at k 8 _ Hk). subst byte_at. cbn beta. rewrite H1. reflexivity. }
rewrite Hnth. symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. pose proof (u8_range bt).
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.
End g.
Section h.
Variable B : malloc_syms.
Let segs := ms_segs B.
Definition pristine_check (rs : smem) : bool :=
zero_check segs rs (SLit (ms_ctx B)) (Z.to_nat CTX_SIZE) &&
zero_check segs rs (SLit (ms_lock B)) 4 &&
zero_check segs rs (SLit (ms_libc B + 3)) 1 &&
word_check segs rs (SLit (ms_libc B + 48)) 4096 &&
word_check segs rs (SLit (ms_got_guard B)) (ms_guard B) &&
match svword_at rs None (ms_guard B) with Some _ => true | None => false end &&
img_covered rs (ms_debruijn B - 108) 140 && img_covered rs (ms_size_classes B) 96 &&
img_covered rs (ms_small_cnt B) 27 && img_covered rs (ms_med_cnt B) 4 &&
(0 <=? ms_ctx B) && (ms_ctx B + CTX_SIZE <=? 2 ^ 64) && (0 <=? ms_lock B) && (ms_lock B + 4 <=? 2 ^ 64) &&
(0 <=? ms_libc B) && (ms_libc B + 56 <=? 2 ^ 64) && (0 <=? ms_got_guard B) && (ms_got_guard B <? 2 ^ 64) &&
(0 <=? ms_guard B) && (ms_guard B <? 2 ^ 64).
Lemma unsigned_slit : forall E a, 0 <= a < 2 ^ 64 -> bv_unsigned (sv_denot E (SLit a)) = a.
Proof.
intros E a Ha. cbn [sv_denot]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. exact Ha.
Qed.
Theorem heap_pristine_intro : forall E m rs md,
mem_ok segs E m rs -> pristine_check rs = true ->
vm_maps (m_vmmaps md) = [] -> vm_noaccess (m_vmmaps md) = [] ->
vm_brk (m_vmmaps md) = vm_start_brk (m_vmmaps md) ->
valid_brk segs (vm_brk (m_vmmaps md)) ->
bv_unsigned (vm_brk (m_vmmaps md)) + 2 * 4096 <= alloc_ceiling ->
vm_reserved (m_vmmaps md) = segments_reserved segs ->
SRC_LIM_MIN <= vm_limit (m_vmmaps md) ->
vm_backing_used md <= 0 ->
m_halted md = None -> m_vm_lazy md = [] -> m_vm_materialized md = [] ->
YM05.ceil_of_top (alloc_top (m_vmmaps md)) ->
heap_pristine B m md.
Proof.
intros E m rs md HM Hck V1 V2 V3 V4 V5 V6 V7 V8 M1 M2 M3 HC.
unfold pristine_check in Hck.
repeat match type of Hck with _ && _ = true => apply andb_prop in Hck as [Hck ?X] end.
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H end.
constructor.
- intros i Hi. rewrite <- (unsigned_slit E (ms_ctx B)) by lia.
apply (zero_check_sound segs E m rs _ (Z.to_nat CTX_SIZE) HM Hck). unfold CTX_SIZE in *. lia.
- intros k Hk. rewrite <- (unsigned_slit E (ms_lock B)) by lia.
apply (zero_check_sound segs E m rs _ 4 HM); [assumption | lia].
- rewrite <- (Z.add_0_r (ms_libc B + 3)). rewrite <- (unsigned_slit E (ms_libc B + 3)) by lia.
apply (zero_check_sound segs E m rs _ 1 HM); [assumption | lia].
- rewrite <- (unsigned_slit E (ms_libc B + 48)) by lia. eapply word_check_sound; eassumption.
- rewrite <- (unsigned_slit E (ms_got_guard B)) by lia. eapply word_check_sound; eassumption.
- match goal with H : match svword_at rs None (ms_guard B) with _ => _ end = true |- _ =>
destruct (svword_at rs None (ms_guard B)) as [gv|] eqn:Hgv; [|discriminate];
exists (bv_unsigned (sv_denot E gv));
pose proof (svword_at_sound segs E m rs None (ms_guard B) gv HM Hgv) as W; cbn [base_val] in W; rewrite Z.add_0_l in W; exact W
end.
- intros a [Ha|[Ha|[Ha|Ha]]];
repeat match goal with
| H : img_covered rs ?lo ?n = true |- _ =>
first [ exact (img_covered_sound segs E m rs lo n HM H a ltac:(lia)) | clear H ]
end.
- exact (conj V1 (conj V2 (conj V3 (conj V4 (conj V5 (conj V6 (conj V7 V8))))))).
- exact (conj M1 (conj M2 M3)).
- exact HC.
Qed.
Definition auxv_check (rs : smem) (G : facts) (na nr : nat) : bool :=
match svword_at rs None (ms_libc B + 8) with Some v => sv_eqb v (SOff na 0) | None => false end &&
forallb (fun k => word_check segs rs (SOff na (16 * Z.of_nat k)) (nth k AUXV_TYPES 0)) (seq 0 10) &&
match svword_at rs (Some na) 136 with Some v => sv_eqb v (SOff nr 0) | None => false end &&
sdata_at rs (Some nr) 8 &&
match fact_of (f_atoms G) na, fact_of (f_atoms G) nr with
| Some fa, Some fr => (4096 <=? af_lo fa) && (af_hi fa + 160 <=? 2 ^ 63) && (4096 <=? af_lo fr) && (af_hi fr + 16 <=? 2 ^ 63)
| _, _ => false
end.
Theorem auxv_pre_intro : forall E m rs G na nr lo,
mem_ok segs E m rs -> facts_ok E G -> auxv_check rs G na nr = true ->
lo <= bv_unsigned (ew E na) -> lo <= bv_unsigned (ew E nr) ->
exists sec, 0 <= sec < 2 ^ 64 /\ auxv_pre B sec lo m.
Proof.
intros E m rs G na nr lo HM HG Hck Hlo1 Hlo2. unfold auxv_check in Hck.
repeat match type of Hck with _ && _ = true => apply andb_prop in Hck as [Hck ?X] end.
destruct (fact_of (f_atoms G) na) as [fa|] eqn:Hfa; [|discriminate].
destruct (fact_of (f_atoms G) nr) as [fr|] eqn:Hfr; [|discriminate].
pose proof (fact_of_sound E _ na fa (proj1 HG) Hfa) as (Ba & _). pose proof (fact_of_sound E _ nr fr (proj1 HG) Hfr) as (Br & _).
repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [H ?Y] end.
repeat match goal with H : (_ <=? _) = true |- _ => apply Z.leb_le in H end.
destruct (svword_at rs None (ms_libc B + 8)) as [v|] eqn:Hv; [|discriminate]. apply sv_eqb_eq in Hck. subst v.
destruct (svword_at rs (Some na) 136) as [v|] eqn:Hv2; [|discriminate].
match goal with H : sv_eqb v _ = true |- _ => apply sv_eqb_eq in H; subst v end.
match goal with H : sdata_at rs (Some nr) 8 = true |- _ =>
destruct (sdata_at_sound segs E m rs (Some nr) 8 HM H) as (sec & Hsec & Wsec) end.
cbn [base_val] in Wsec.
exists sec. split; [exact Hsec|].
exists (bv_unsigned (ew E na)), (bv_unsigned (ew E nr)).
assert (Dna : forall o, 0 <= o -> o <= 160 -> bv_unsigned (sv_denot E (SOff na o)) = bv_unsigned (ew E na) + o).
{ intros o Ho Ho'. cbn [sv_denot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_small. lia. }
split; [| split; [| split; [| split; [exact Wsec | lia]]]].
- pose proof (svword_at_sound segs E m rs None _ _ HM Hv) as W. cbn [base_val] in W. rewrite Z.add_0_l in W.
rewrite <- (Z.add_0_r (bv_unsigned (ew E na))). rewrite <- (Dna 0) by lia. exact W.
- intros k Hk. rewrite <- (Dna (16 * Z.of_nat k)) by lia.
eapply word_check_sound; [exact HM|].
match goal with H : forallb _ (seq 0 10) = true |- _ => exact (forallb_In _ _ k H ltac:(apply in_seq; lia)) end.
- pose proof (svword_at_sound segs E m rs (Some na) 136 _ HM Hv2) as W. cbn [base_val] in W.
replace (bv_unsigned (ew E na) + 16 * 8 + 8) with (bv_unsigned (ew E na) + 136) by lia.
replace (bv_unsigned (ew E nr)) with (bv_unsigned (sv_denot E (SOff nr 0)));
[exact W | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
Qed.
End h.
End e.
