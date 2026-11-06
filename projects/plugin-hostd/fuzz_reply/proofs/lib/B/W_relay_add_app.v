(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the APP segment of the image-B walk of fuzz_reply's relay_add
   (lib/B/W_relay_add_cut.v ra_app_stmt): from the cut RAA (0x82b90, the table at T1 with the entry's es, the lock
   held) to the cut RAU (0x82c04, the entry ra_new fd appended).

   The stretch (fuzz_reply.asan-ubsan), and how each of its five trap edges (all to `unimp` 0x82c80) is closed:
     0x82b90  s5 = g_nsrc (lw through A_HI 28), s4 = g_src (ld through A_HI 30), s1 = s4 + 56 s5
     0x82bb0  TRAP `snez a0,s4; seqz a1,s1; beq a0,a1` (null consistency): decided inside the run (snez = 1 from
              atom 33 = T1 >= 4096, seqz = 0 from atom 34 = the slot >= 4096).
     0x82bc4  TRAP `slti a0,s5,0; sltu a1,s1,s4; xor; xori 1; beqz` (pointer overflow): left open by the runner (the
              slot and T1 are distinct atoms); the taken arm is refuted by W_traps.v trap_ptr_sovf (slti folded to 0
              from atom 32's range [0, 3], sltu s1,s4 = 0 by trap_U_sltu_ge: T1 <= T1 + 56 |es|).
     0x82bd4  __asan_memset (s1, 0, 56) (AMEMSET, through W_sites.v aj_gx_entry_at; Wr = the slot's 56 bytes)
     0x82bdc  TRAP `addiw a0,s5,1; blt a0,s5` (int32 + 1 overflow): decided inside the run (a0 = atom 32 + 1 against
              atom 32, range [0, 3]).
     0x82be0  g_nsrc = |es| + 1 (sw through A_HI 28)
     0x82be4  TRAP `beqz s4` (null): decided inside the run (atom 33 >= 4096).
     0x82bec  TRAP `andi a0,s1,7; bnez` (alignment): decided inside the run (atom 34 8-aligned).
     0x82bf0  the shadow check of s1: decided by the shadow entry over the slot (the slow path 0x82c84 and the error
              path 0x82c90 are not reached)
     0x82c00  `sw s0,0(s1)`: the new entry's fd
   The seat holds g_nsrc and g_src read-only (both are only loaded before the call); after the call the region the
   store `sw a0,484(s3)` needs is seated at the auipc atom A_HI 28 (offset 484), and the new slot's first 4 bytes
   (the fd store) at the slot atom.  The old entries keep their bytes across the memset by W_relay_add_sep.v
   ra_efp_off_slot (no old entry reads the new slot).  errno's view (ALIVE's aerrno_kept) is carried from RAA: errno is
   an image byte outside RA_G, so neither run nor the memset writes it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_syms W_listing W_pl W_kit W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal W_sites W_rep W_img W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_frame W_traps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_add_cut W_relay_add_sep.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope bv_scope.
Local Open Scope Z_scope.
Local Notation le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Local Notation le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.

(* ------------------------------------------------------------------ byte lists *)
Lemma ra_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
Lemma ra_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
intros e P1 P2. unfold entry_bytes.
rewrite !length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, P1, P2. reflexivity.
Qed.
Lemma ra_concat_len : forall l, Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof.
induction l as [|e l IH]; intros HF; [reflexivity|].
apply Forall_cons_iff in HF as [[P1 P2] HF]. cbn [map concat length]. rewrite length_app, (ra_eb_len e P1 P2), (IH HF). lia.
Qed.
Lemma ra_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
(* the new entry's 56 bytes: fd, then 52 zero bytes *)
Lemma ra_new_bytes : forall fd,
  map bz (entry_bytes (ra_new fd)) = map bz (le4 (Z_to_bv 64 fd)) ++ repeat 0 52.
Proof.
intros fd. unfold entry_bytes, ra_new, re_nheld.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 re_keys length].
rewrite map_app. f_equal; try (vm_compute; reflexivity).
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ------------------------------------------------------------------ memory helpers *)
Lemma ra_le_garr8 : forall m a n z, val_mem SEGS m a n z -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS m a (bzs (Z_to_le_bytes n z)).
Proof.
intros m a n z Hv Hz j Hj. unfold bzs in Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hj).
rewrite map_nth, ra_nth_le_bytes by exact Hj. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256.
split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma ra_le4_bytes : forall z, 0 <= z < 2 ^ 64 -> le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof.
intros z Hz. unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma ra_garr8_kept : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
(* one visible byte is a one-byte val_mem *)
Lemma ra_vm1 : forall H (m : word -> option byte) a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Eb; cbn in Hv; [|discriminate].
injection Hv as <-. try rewrite Eb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256) by lia. reflexivity.
Qed.
Lemma ra_garr8_zeros : forall H (m : word -> option byte) a n,
(forall j, 0 <= j < Z.of_nat n -> aview SEGS H m (a + j) = Some 0) -> garr8 SEGS (mrestrict H m) a (repeat 0 n).
Proof.
intros H m a n Hz j Hj. rewrite repeat_length in Hj. rewrite nth_repeat.
split; [apply ra_vm1; apply Hz; lia | lia].
Qed.
(* A byte a reader sees, off the read-only segments, is writable (W_gestures_end.v gse_writable_view). *)
Lemma ra_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
unfold seg_rom, memory_read in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
change (Z.of_N 1) with 1 in Ef. rewrite Ef.
destruct (seg_readable sg); [|discriminate].
destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
destruct (seg_writable sg) eqn:Ew.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb; [discriminate|].
  exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv. discriminate Hv.
- exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
(* abyte_kept from the view, for a byte seen before and off the read-only segments *)
Lemma ra_abyte_kept : forall (W W' : world SEGS) m m' a, 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a -> aview SEGS (w_H W) m a <> None -> ~ in_rom SEGS a ->
abyte_kept W m W' m' a.
Proof.
intros W W' m m' a Ha He Hs Hr. split; [exact He|]. intros _. unfold arm.
destruct (aview SEGS (w_H W) m a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
exact (ra_writable_view (w_H W') m' a v Ha He Hr).
Qed.
Lemma ra_view_some : forall H (m : word -> option byte) a n v k, val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma ra_new_ok : forall B ly S W mem fd, 0 <= fd < 2 ^ 31 -> aentry_ok B ly S W mem (ra_new fd).
Proof.
intros B ly S W mem fd Hfd. unfold aentry_ok, ra_new, re_nheld.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_kh re_pad2 re_keys re_U re_junk length].
split; [left; reflexivity|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Hfd|]. split; [left; reflexivity|]. split; [reflexivity|]. split; [unfold APARTIAL; lia|].
split; [intros []|]. split; [left; split; [reflexivity | split; reflexivity]|]. split; [lia|].
split; [left; split; reflexivity|]. split; [constructor|]. split; [constructor | constructor].
Qed.

(* ------------------------------------------------------------------ the seat at 0x82b90 *)
(* s2 = the shadow offset (atom 18); s3 / s4 the auipc images, pinned to SOff (A_HI 28) 0 / SOff (A_HI 30) 0 (the form
   PLdHi's `is_hi` test wants); every other register its own atom.  Extra atoms: 32 = |es|, 33 = the table T1,
   34 = the new entry's slot T1 + 56 |es| (the alias makes the computed s1 that atom).  The two globals are read-only
   here: the stretch to the call only loads them. *)
Definition Bx : sv := SOff 18 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition PTRF (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition ra_app_regs : list sv :=
sr_set (sr_set sr_atoms 19%bv (SOff (A_HI 28) 0)) 20%bv (SOff (A_HI 30) 0).
Definition ra_nsrc_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))].
Definition ra_src_region : YP09.region :=
YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition ra_app_regions : smem := [ra_nsrc_region; ra_src_region].
Definition ra_app_facts : facts :=
mkFacts [ (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 3 0); (33%nat, PTRF 4); (34%nat, PTRF 3);
          (A_HI 28, mkAF 0 6275072 0) ] []
  [ (SAlu ALU_ADD (SMd M_MUL (SOff 32 0) (SLit 56)) (SOff 33 0), SOff 34 0) ].
Definition ss_ra_app : sstate := mkSS A_ra_app ra_app_regs ra_app_regions None ra_app_facts.
Definition ra_app_SH : list shent := [ mkSHE 34 0 8 ].
Definition ra_app_extra (n T1 : Z) : list word := map (Z_to_bv 64) [n; T1; T1 + AENT * n].
(* after the call: g_nsrc's 4 bytes at the auipc atom 308 = A_HI 28 (offset 484, the store's form), and the slot's
   fd field at the slot atom *)
Definition ra_nsrc_w : YP09.region := YP09.mkRegion (Some 308%nat) 484 488 484 488 [].
Definition ra_slot_w : YP09.region := YP09.mkRegion (Some 34%nat) 0 4 0 4 [].
(* a run over read-only regions leaves the memory as it was (B_rr_scan.v rrs_mem) *)
Ltac ra_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable RG : rep_globals.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B (RA_G RG).
Hypothesis HWK : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Hypothesis HNROM : forall a, inG (RA_G RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (RA_G RG).
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
Hypothesis HV3 : VAL (A_OBJ 3) = rg_lock RG.
Hypothesis HV4 : VAL (A_OBJ 4) = rg_nsrc RG.
Hypothesis HV5 : VAL (A_OBJ 5) = rg_src RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_capsrc RG.
Hypothesis HH28 : VAL (A_HI 28) + RA_HI_NSRC = rg_nsrc RG.
Hypothesis HH29 : VAL (A_HI 29) + RA_HI_CAPSRC = rg_capsrc RG.
Hypothesis HH30 : VAL (A_HI 30) + RA_HI_SRC = rg_src RG.
Hypothesis HRGA : ra_aligned RG.
Hypothesis HRGP : ra_apart (ra_cells RG).
Hypothesis HMMAX : ATABLE < MMAX.
Hypothesis ALOCK : alock_realizes B (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes B (SIGMA WS_pthread_mutex_unlock).
Hypothesis AREALLOC : arealloc_cf_rule_c SEGS B MT MMAX CTX (SIGMA WS_realloc).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA WS_asan_memset).
Hypothesis WAKE : wk_spec B RG (BASE + AF_fr_wake).
Let RUN := paj_run_x B LAWS (RA_G RG) HG 0 [].
Let RUNTO := paj_run_to_x B LAWS (RA_G RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ------------------------------------------------------------------ blocks and entries *)
Lemma ra_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (al_sep _ _ LAWS ly S W mem md HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _].
assert (Hpos : Forall (fun b => 0 < req_size (snd b)) (ablocks B ly S)).
{ apply Forall_forall. intros [p n] Hin. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
  cbn [snd]. pose proof (req_size_pos n ltac:(lia)). lia. }
induction (ablocks B ly S) as [|b l IH]; [apply List.NoDup_nil|].
cbn [map pairwise] in Hp. destruct Hp as [Hf Hp]. inversion Hpos as [|? ? Hb Hl]; subst.
apply List.NoDup_cons; [|exact (IH Hp Hl)].
intros Hin. rewrite Forall_forall in Hf. specialize (Hf (fst b, req_size (snd b)) (in_map _ _ _ Hin)).
unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
Qed.
(* every byte an entry's predicate reads lies in one of its live blocks *)
Lemma ra_efp_in_block : forall ly S W mem e, aentry_ok B ly S W mem e ->
forall r a, In r (aentry_fp e) -> fst r <= a < snd r ->
exists p m, In (p, m) (ablocks B ly S) /\ p <= a < p + req_size m.
Proof.
intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) r a Hr Ha.
unfold aentry_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc | Hc]; [destruct Hr|]. destruct Hr as [<- | []].
  destruct H10 as [(Hc0 & _) | (Hcp & Hin & Hj & _)]; [lia|].
  exists (re_buf e), (re_cap e). split; [exact Hin|]. unfold gfp in Ha. cbn [fst snd] in Ha.
  unfold bzs in Ha. rewrite length_map, length_app in Ha.
  assert (Hrq : req_size (re_cap e) = re_cap e) by (unfold req_size; destruct (Z.eqb_spec (re_cap e) 0); lia). lia.
- destruct Hr as [<- | Hr].
  + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, ra_key_ptrs_len in Ha.
    destruct H12 as [(Hz & Hk) | (Hz & Hin & Hk1 & Hk2 & _)].
    * rewrite Hk in Ha. cbn [length] in Ha. lia.
    * exists (re_hp e), (re_kh e). split; [exact Hin|]. unfold re_nheld in Hk1.
      assert (Hrq : req_size (re_kh e) = re_kh e) by (unfold req_size; destruct (Z.eqb_spec (re_kh e) 0); lia). lia.
  + apply in_map_iff in Hr as (k & <- & Hk). rewrite Forall_forall in H15. destruct (H15 k Hk) as (K1 & _ & _ & K4).
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split; [exact K1|]. unfold gfp in Ha. cbn [fst snd] in Ha.
    unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha.
    assert (Hrq : req_size (Z.of_nat (length (key_text k)) + 1) = Z.of_nat (length (key_text k)) + 1)
      by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (key_text k)) + 1) 0); lia). lia.
Qed.
Lemma ra_eblks_in : forall ly S W mem e, aentry_ok B ly S W mem e -> forall b, In b (aentry_blks e) -> In b (ablocks B ly S).
Proof.
intros ly S W mem e (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15) b Hb.
unfold aentry_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
- destruct (Z.eqb_spec (re_cap e) 0); [destruct Hb|]. destruct Hb as [<- | []].
  destruct H10 as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
- apply in_app_or in Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_hp e) 0) as [Hz | Hz]; [destruct Hb|]. destruct Hb as [<- | []].
    destruct H12 as [(Hz0 & _) | (_ & Hin & _)]; [exfalso; exact (Hz Hz0) | exact Hin].
  + apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in H15. exact (proj1 (H15 k Hk)).
Qed.

Lemma ra_app_seat : forall (W1 : world SEGS) (regs1 : bvmap 5 word) m1 T1 (n : Z),
getr regs1 18 = w64 SHADOW_OFF ->
getr regs1 19 = w64 (rg_nsrc RG - RA_HI_NSRC) ->
getr regs1 20 = w64 (rg_src RG - RA_HI_SRC) ->
0 <= n <= 3 ->
4096 <= T1 -> T1 mod 16 = 0 -> T1 + ATABLE <= 140737479966720 -> in_app T1 896 ->
val_mem SEGS (arm W1 m1) (rg_nsrc RG) 4 n ->
val_mem SEGS (arm W1 m1) (rg_src RG) 8 T1 ->
range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (T1 + AENT * n) 8 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 (ra_app_extra n T1))) ss_ra_app
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_ra_app)) m1 (seg_rom SEGS)))
/\ sh_ok SEGS Bx ra_app_SH (Eimg (Ereg regs1 (ra_app_extra n T1))) (mrestrict (w_H W1) m1).
Proof.
intros W1 regs1 m1 T1 n R18 R19 R20 Hn HT0 HT16 HTC HTA Mn Ms RA. unfold ATABLE in HTC.
pose proof pa_B_ok as HBASE. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pa_obj_img 4 ltac:(lia)) as HI4. rewrite HV4 in HI4.
pose proof (pa_obj_img 5 ltac:(lia)) as HI5. rewrite HV5 in HI5.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs1 (ra_app_extra n T1))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 n)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 T1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (T1 + AENT * n))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
assert (E245 : ew E (A_OBJ 4) = Z_to_bv 64 (rg_nsrc RG))
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite HV4; reflexivity).
assert (E246 : ew E (A_OBJ 5) = Z_to_bv 64 (rg_src RG))
  by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite HV5; reflexivity).
assert (E308 : ew E (A_HI 28) = Z_to_bv 64 (VAL (A_HI 28)))
  by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (E310 : ew E (A_HI 30) = Z_to_bv 64 (VAL (A_HI 30)))
  by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (HX8 : (T1 + AENT * n) mod 8 = 0).
{ unfold AENT. replace (T1 + 56 * n) with ((T1 / 16 * 2 + 7 * n) * 8) by
    (pose proof (Z.div_mod T1 16 ltac:(lia)); lia). apply Z_mod_mult. }
split.
- unfold ss_ra_app, ra_app_regs. apply pa_entry_st_ok_full.
  + apply regs_ok_pin;
    [apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |] | intros X; discriminate X |].
    * cbn [sv_denot]. rewrite E308, Z.add_0_r, Z_to_bv_bv_unsigned, R19. unfold w64. f_equal. unfold RA_HI_NSRC in *. lia.
    * cbn [sv_denot]. rewrite E310, Z.add_0_r, Z_to_bv_bv_unsigned, R20. unfold w64. f_equal. unfold RA_HI_SRC in *. lia.
  + vm_compute. reflexivity.
  + unfold ra_app_regions, ra_nsrc_region, ra_src_region.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite E245, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_nsrc RG) 0 4 (SOff 32 0) n);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mn.
    * cbn [base_val]. rewrite E246, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (rg_src RG) 0 8 (SOff 33 0) T1);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Ms.
  + apply pairwise_disjoint_of_extents.
    unfold ra_app_regions, ra_nsrc_region, ra_src_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite E245, E246, !unsigned_lit_small by lia.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    ra_pick HRGP 3%nat 5%nat D35.
    revert D35. clear. intros. repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [ra_app_facts f_atoms atoms_ok]. unfold afact_ok, PTRF. cbn [af_lo af_hi af_al2].
      pose proof (pa_val_range (A_HI 28)) as HR28.
      rewrite E18, E32, E33, E34, E308, !unsigned_lit_small by (unfold SB, SHADOW_OFF, AENT, RA_HI_NSRC in *; lia).
      change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      revert Hn HT0 HT16 HTC HI4 HX8 HH28. unfold AENT, SB, SHADOW_OFF, RA_HI_NSRC. clear. intros.
      repeat match goal with |- _ /\ _ => split end; try lia; try reflexivity.
    * cbn [ra_app_facts f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
      rewrite (U_atom E 32 n E32), (U_atom E 33 T1 E33), (U_atom E 34 (T1 + AENT * n) E34)
        by (unfold AENT in *; lia).
      rewrite (zcanon_id 56) by (unfold M64; lia).
      rewrite (zcanon_id (n * 56)) by (unfold M64; lia).
      unfold AENT in *. rewrite (zcanon_id (n * 56 + T1)) by (unfold M64; lia). lia.
- assert (HBx : U E Bx = SHADOW_OFF)
    by (unfold Bx; rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
  unfold sh_ok, ra_app_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) m1 E Bx 34 (T1 + AENT * n) 8 (T1 + AENT * n) 0 8 RA HBx);
  [rewrite (U_atom E 34 (T1 + AENT * n) E34) by (unfold AENT in *; lia); reflexivity
  | lia | lia |].
  intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia.
Qed.

Theorem pb_ra_app : ra_app_stmt B MT G RG CTX.
Proof.
intros cx W1 c1 HB HA KU.
destruct HA as (regs1 & ly1 & S1 & m1 & md1 & k1 & T1 & -> & HRH & R19 & R20 & Hfd & HAL & HREL & HML & HBLK).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HAL as (HJ & HROM1 & HPK1 & HSV & HLK & HWAKE & HFR & HERR1).
pose proof HRH as (HRB & R8 & R18).
pose proof HREL as (Ms & Ws & Mn & Wn & Mc & Wc & Hlen16 & HTin & (tail & Htab) & Hents & HNDfd & HNOTAB).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 T1 ATABLE HAR HTin)
  as (HT16 & HT4096 & HTceil & HTapp & HTpres & _ & _).
change (req_size ATABLE) with 896 in HTceil, HTpres, HTapp.
pose proof HB as (HPRE & Hal32 & HCNT & H10 & Hfdr & HLOCK0 & HWAKE0 & HROM0 & HREL0 & HNEW & HGin & HGerr & HLIVE & HCTX & HMOK).
destruct (HNEW Hfd) as (Hlt4 & HnotIn).
set (n := Z.of_nat (length (axes cx))) in *.
assert (Hn03 : 0 <= n <= 3) by (unfold n; lia).
assert (RA : range_addressable (aview SEGS (w_H W1) m1) SHADOW_OFF (T1 + AENT * n) 8).
{ apply (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 T1 ATABLE (T1 + AENT * n) 8 HAR HTin);
  change (req_size ATABLE) with 896; unfold AENT, ATABLE in *; lia. }
destruct (ra_app_seat W1 regs1 m1 T1 n R18 R19 R20 Hn03 HT4096 HT16
  ltac:(unfold ATABLE in *; lia) HTapp Mn Ms RA) as [HS SHOK].
remember (Eimg (Ereg regs1 (ra_app_extra n T1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (ra_app_extra n T1)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr).
{ intros m rr Hm. rewrite HE. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew E 2 = getr regs1 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = getr regs1 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs1 4) by exact (EEo 4%nat 4%bv eq_refl).
assert (E8 : ew E 8 = w64 (axfd cx)) by (rewrite (EEo 8%nat 8%bv eq_refl); exact R8).
assert (E18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact R18).
assert (E32 : ew E 32 = Z_to_bv 64 n)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 T1)
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (T1 + AENT * n))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 2)).
clear HE EEo.
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal160 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
pose proof HRB as (HspR & HgpR & HtpR & H23 & H24 & H25 & H26 & H27).
pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 T1 ATABLE HAR HTin) as HToff.
change (req_size ATABLE) with 896 in HToff.
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in HToff.
set (X := T1 + AENT * n) in *.
assert (HXv : X = T1 + 56 * n) by reflexivity.
unfold cfg_at. change (w64 (BASE + A_ra_app)) with (Z_to_bv 64 (BASE + A_ra_app)).
(* ---- 0x82b90 -> the trap edge 0x82bc4.  The loads s5 = |es| (atom 32: its range [0, 3] makes the lw's sign
   extension the identity) and s4 = T1 (atom 33); s1 = s4 + 56 s5 is atom 34 by the seat's alias.  TRAP 0x82bb0
   (`snez a0,s4; seqz a1,s1; beq a0,a1`) is decided inside this run: snez = 1 (atom 33 >= 4096), seqz = 0 (atom 34
   >= 4096). *)
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
ra_mem Em1.
(* TRAP 0x82bc4 (`slti a0,s5,0; sltu a1,s1,s4; xor; xori 1; beqz`, pointer overflow): left open by the runner (s1 and
   s4 are distinct atoms); the taken arm is refuted by W_traps.v trap_ptr_sovf, both compares 0: slti (folded to 0
   by the runner from atom 32's range) and sltu s1,s4 (trap_U_sltu_ge: T1 <= T1 + 56 |es|). *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite (trap_ptr_sovf E (SAlu ALU_SLTU (SOff 34 0) (SOff 33 0)) (SLit 0) 0) in Hc; [discriminate Hc | |].
  - apply (trap_U_sltu_ge E (SOff 33 0) (SOff 34 0) T1 X);
    [apply (U_atom E 33 T1 E33) | apply (U_atom E 34 X E34) |]; unfold AENT in *; lia.
  - rewrite U_SLit. reflexivity. }
(* ---- -> the call to __asan_memset (s1, 0, 56) at 0x82bd4 *)
paj_run_tok RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
ra_mem Em2. rewrite Em1 in Em2. rewrite Em2 in HJ.
pmkst HS. rewrite Em2.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
lazymatch type of HS with context [restrict _ ?m] => set (msA := m) in * end.
assert (HSP1 : spZ (ms_regs msA) = asp0 cx + -64).
{ change (spZ (ms_regs msA)) with (bv_unsigned (getr (ms_regs msA) 2)). rewrite P2, E2.
  change (bv_unsigned (getr regs1 2)) with (spZ regs1). rewrite HspR. unfold RA_FRAME. lia. }
assert (HSTKX : alloc_ceiling + RA_STK <= asp0 cx) by (unfold asp0; lia).
unfold RA_STK, RA_FRAME, ASTACK in HSTKX.
(* the slot's 56 bytes: in the table's block, a byte the journal may write (the footprint ra_FP when the table
   existed at the entry, else a block the entry did not have) *)
assert (AWRB : forall a, X <= a < X + 56 ->
  awr_byte RA_STK (asp0 cx) (aFP cx) (ablocks B (axly cx) (axS cx)) (ablocks B ly1 S1) ly1 [] a).
{ intros a Ha. unfold awr_byte.
  destruct HBLK as [(HT0 & HPm) | (HT0 & HT1e & HBe)].
  - right; right; left. exists T1, ATABLE. split; [exact HTin|].
    split; [|change (req_size ATABLE) with 896; unfold AENT in *; lia].
    intros Hin0. pose proof (ra_nodup ly1 S1 W1 m1 md1 HAR) as ND.
    apply (Permutation_NoDup HPm) in ND. inversion ND as [|? ? Hni _]. exact (Hni Hin0).
  - right; left. split.
    + unfold aFP, ra_FP. rewrite (proj2 (Z.eqb_neq _ 0) HT0).
      exists (axT cx + AENT * n, axT cx + AENT * (n + 1)).
      split; [left; reflexivity | cbn [fst snd]; rewrite <- HT1e; unfold AENT in *; lia].
    + exists T1, ATABLE. split; [exact HTin | change (req_size ATABLE) with 896; unfold AENT in *; lia]. }
assert (HDEST : dest_ok SEGS B ly1 S1 W1 (ms_regs msA) m1 X 56).
{ intros a Ha. destruct (HTpres a ltac:(unfold AENT in *; lia)) as [Hp Hno].
  split; [exact (apresent_writable SEGS (w_H W1) m1 a Hp)|]. split; [exact Hno|].
  rewrite HSP1. unfold ESTACK, AENT in *. lia. }
assert (HAMR : amem_range X 56).
{ unfold amem_range. unfold in_app in HTapp. unfold kLowShadowBeg, ASAN_CEIL in HTapp.
  rewrite C3, C4, C5. rewrite C3 in HTapp. unfold AENT in *. lia. }
pose proof (range_addressable_of_block SEGS B LAWS ly1 S1 W1 m1 md1 T1 ATABLE X 56 HAR HTin
  ltac:(unfold AENT in *; lia) ltac:(change (req_size ATABLE) with 896; unfold AENT in *; lia)) as HRAX.
pose proof (shadow_hull_vis_of_block SEGS B LAWS ly1 S1 W1 m1 md1 T1 ATABLE X 56 HAR HTin
  ltac:(unfold AENT in *; lia) ltac:(change (req_size ATABLE) with 896; unfold AENT in *; lia) ltac:(lia)) as HHULL.
(* __asan_memset (s1, 0, 56): AMEMSET through aj_gx_entry_at, 64 bytes below the entry sp, returning to 0x82bd8
   (listing offset 2196) *)
eapply SRr_bind.
{ apply (aj_gx_entry_at B LAWS (RA_G RG) 0 [] ESTACK (SIGMA WS_asan_memset) (fun a => X <= a < X + 56)
    (fun _ mem' => forall i, 0 <= i < 56 -> aview SEGS (w_H W1) mem' (X + i) = Some 0)
    W1 (ms_regs msA) m1 RA_STK (asp0 cx) (aFP cx) (axly cx) (axS cx) (axW cx) (axmem cx) (axmd cx) []
    ly1 S1 _ k1 (-64) (Z_to_bv 64 (BASE + 2196)) HG eq_refl HJ HSP1 eq_refl ltac:(lia) ltac:(unfold ESTACK; lia)
    ltac:(unfold RA_STK, RA_FRAME, ASTACK, ESTACK; lia)).
  - rewrite P3, E3, HgpR. exact Hgp0.
  - rewrite P4, E4, HtpR. exact Htp0.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_le_gt_dec X a) as [H1 | H1];
    [destruct (Z_lt_ge_dec a (X + 56)) as [H2 | H2]; [left; lia | right; lia] | right; lia].
  - intros a Ha Hga. exfalso. pose proof (pa_img_range a (proj1 (HG a Hga))). unfold AENT in *. lia.
  - intros a Ha _. split; [exact (AWRB a Ha) | lia].
  - intros HPREc _. eapply SRr_mono.
    { exact (AMEMSET ly1 S1 W1 (ms_regs msA) m1 _ X 0 56 HPREc
        ltac:(rewrite P10, E34; reflexivity) ltac:(rewrite P11; reflexivity) ltac:(rewrite P12; reflexivity)
        ltac:(lia) ltac:(unfold AENT in *; lia) ltac:(unfold AENT in *; lia) HDEST HAMR HRAX (fun _ => HHULL) I). }
    cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HAR' & HP' & Hs' & _ & Hset & Hfr & Hpr).
    split; [reflexivity|]. exists regs', mem', md'. split; [reflexivity|]. split; [exact HAR'|]. split; [exact HP'|].
    split; [exact Hs'|]. split; [intros i Hi; rewrite (Hset i Hi); reflexivity|]. split; [exact Hfr | exact Hpr]. }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HZ2 & HFR2 & HPR2).
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
(* ---- back at 0x82bd8: a fresh symbolic memory (the two loads are done); the callee-saved registers kept *)
jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall i, (i < 35)%nat -> ew Ea i = ew E i)
  by (intros i Hi; rewrite HEa; apply YN3v.ew_havoc_old; exact Hi).
assert (HAEa : env_agree 32 (Ereg regs1 (ra_app_extra n T1)) Ea)
  by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (U34a : bv_unsigned (ew Ea 34) = X)
  by (rewrite OLDa by lia; rewrite E34; apply unsigned_lit_small; unfold AENT in *; lia).
assert (U308a : bv_unsigned (ew Ea 308) = rg_nsrc RG - 484).
{ rewrite (HEIa 308%nat ltac:(cbv; lia)). change (A_HI 28) with 308%nat in HH28. unfold RA_HI_NSRC in HH28. lia. }
pose proof (pa_obj_img 4 ltac:(lia)) as HI4. rewrite HV4 in HI4.
(* what memset kept: the globals (image bytes, off the slot and off its scratch) *)
assert (GIMG : forall a, inG (RA_G RG) a -> 0x10000 <= a < 0x5fc000)
  by (intros a Ha; exact (pa_img_range a (proj1 (HG a Ha)))).
assert (GKM : forall a, inG (RA_G RG) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) m1 a).
{ intros a Ha. pose proof (GIMG a Ha). apply HFR2; [lia | unfold AENT in *; lia | unfold ESTACK in *; lia]. }
assert (WN2 : forall o, 0 <= o < 4 -> writable_at SEGS (mrestrict (w_H W1) mem2) (rg_nsrc RG + o)).
{ intros o Ho. pose proof (ra_nsrc_in RG (rg_nsrc RG + o) ltac:(lia)) as Hin. pose proof (GIMG _ Hin).
  destruct (aview SEGS (w_H W1) m1 (rg_nsrc RG + o)) as [v|] eqn:Ev;
  [| exfalso; exact (ra_view_some (w_H W1) m1 (rg_nsrc RG) 4 n o Mn ltac:(cbn; lia) Ev)].
  apply (ra_writable_view (w_H W1) mem2 (rg_nsrc RG + o) v ltac:(lia));
  [rewrite (GKM _ Hin); exact Ev | exact (HNROM _ Hin)]. }
(* the two cells the stretch stores to: g_nsrc through the auipc atom (offset 484), the slot's fd field *)
assert (RN : region_ok SEGS Ea (mrestrict (w_H W1) mem2) ra_nsrc_w).
{ unfold region_ok, ra_nsrc_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U308a. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. replace (rg_nsrc RG - 484 + o) with (rg_nsrc RG + (o - 484)) by lia. apply WN2. lia. }
pose proof (st_ok_pi_add_region Ea _ _ ra_nsrc_w HS ltac:(vm_compute; reflexivity) RN I) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
assert (RS : region_ok SEGS Ea (mrestrict (w_H W1) mem2) ra_slot_w).
{ unfold region_ok, ra_slot_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U34a. split; [unfold AENT in *; lia|]. split; [unfold AENT in *; lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply HPR2. apply HTpres. unfold AENT in *. lia. }
assert (RSD : extent_disjoint Ea ra_slot_w ra_nsrc_w).
{ unfold extent_disjoint, ra_slot_w, ra_nsrc_w. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U34a, U308a. unfold AENT in *. lia. }
pose proof (st_ok_pi_add_region Ea _ _ ra_slot_w HS ltac:(vm_compute; reflexivity) RS (conj RSD I)) as HS3.
clear HS. rename HS3 into HS. norm_ss HS.
assert (SHOK2 : sh_ok SEGS Bx ra_app_SH Ea (mrestrict (w_H W1) mem2)).
{ assert (HBxa : U Ea Bx = SHADOW_OFF)
    by (unfold Bx; rewrite (U_atom Ea 18 SHADOW_OFF ltac:(rewrite OLDa by lia; exact E18)) by (unfold SHADOW_OFF; lia);
        reflexivity).
  unfold sh_ok, ra_app_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ea Bx 34 X 8 X 0 8
    (range_addressable_of_block SEGS B LAWS ly1 S1 W1 mem2 md2 T1 ATABLE X 8 HAR2 HTin
      ltac:(unfold AENT in *; lia) ltac:(change (req_size ATABLE) with 896; unfold AENT in *; lia)) HBxa);
  [rewrite (U_atom Ea 34 X ltac:(rewrite OLDa by lia; exact E34)) by (unfold AENT in *; lia); reflexivity | lia | lia |].
  intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, AENT in *. lia. }
(* ---- 0x82bd8 -> 0x82c04 in one run.  TRAP 0x82bdc (`addiw a0,s5,1; blt a0,s5`) is decided inside it (a0 = atom 32
   plus 1 against atom 32, range [0, 3]); `sw a0,484(s3)`: g_nsrc = |es| + 1; TRAP 0x82be4 (`beqz s4`) decided (atom 33
   >= 4096); TRAP 0x82bec (`andi a0,s1,7; bnez`) decided (atom 34 8-aligned); the shadow check of s1 decided by the
   shadow entry over the slot (its slow path 0x82c84 and the error path 0x82c90 are not reached); `sw s0,0(s1)`. *)
paj_run_to_tok RUNTO HS HJ2 SHOK2 Bspan A_ra_unlock.
{ apply awr_ok_x_cons.
  - intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U34a in Ha.
    left. split; [exact (AWRB a ltac:(unfold AENT in *; lia)) | lia].
  - apply awr_ok_x_cons_g; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U308a in Ha.
    apply (ra_nsrc_in RG). lia. }
lazymatch type of HS with context [restrict _ ?m] => set (msC := m) in * end.
lazymatch goal with Hx : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem msC)) |- _ => rename Hx into HFrC end.
lazymatch goal with Hx : mem_grows (mrestrict _ mem2) (mrestrict _ (ms_mem msC)) |- _ => rename Hx into HGrC end.
pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HARC.
assert (Hn' : n = Z.of_nat (length (axes cx))) by reflexivity.
(* what the run kept: every byte off its two store cells *)
assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (X <= a < X + 4) ->
  aview SEGS (w_H W1) (ms_mem msC) a = aview SEGS (w_H W1) mem2 a).
{ intros a Ha H1 H2. apply (aview_kept_out Ea _ (w_H W1) mem2 (ms_mem msC) HFrC a Ha).
  intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U34a, ?U308a in Hr; lia | ]).
  destruct Hin. }
(* ... and from RAA: every byte off g_nsrc, the slot and memset's scratch *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> ~ (X <= a < X + 56) ->
  ~ (asp0 cx + -64 - ESTACK <= a < asp0 cx + -64) ->
  aview SEGS (w_H W1) (ms_mem msC) a = aview SEGS (w_H W1) m1 a).
{ intros a Ha H1 H2 H3. rewrite (KR2 a Ha H1 ltac:(lia)). exact (HFR2 a Ha H2 H3). }
assert (GW : forall a, inG (RA_G RG) a -> ~ (rg_nsrc RG <= a < rg_nsrc RG + 4) -> aview SEGS (w_H W1) m1 a <> None ->
  abyte_kept W1 m1 W1 (ms_mem msC) a).
{ intros a Hg Hn Hv. pose proof (GIMG a Hg).
  apply ra_abyte_kept; [lia | | exact Hv | exact (HNROM a Hg)].
  apply KALL; [lia | exact Hn | intros Hs; destruct HToff; unfold AENT in *; lia | unfold ESTACK in *; lia]. }
assert (KTB : forall b, T1 <= b < T1 + 896 -> ~ (X <= b < X + 56) ->
  aview SEGS (w_H W1) (ms_mem msC) b = aview SEGS (w_H W1) m1 b).
{ intros b Hb Hs. apply KALL; [lia | intros Hn; destruct HToff; lia | exact Hs | unfold ESTACK in *; lia]. }
assert (KBK : forall p mm b, In (p, mm) (ablocks B ly1 S1) -> p <= b < p + req_size mm -> ~ (X <= b < X + 56) ->
  aview SEGS (w_H W1) (ms_mem msC) b = aview SEGS (w_H W1) m1 b).
{ intros p mm b Hpm Hb Hs.
  destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p mm HAR Hpm) as (_ & Hp4 & Hpc & _).
  pose proof (blk_off_imgP B ly1 S1 W1 m1 md1 p mm HAR Hpm) as Hpo.
  unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.off_img in Hpo.
  apply KALL; [lia | intros Hn; destruct Hpo; lia | exact Hs | unfold ESTACK in *; lia]. }
(* the two stores, read back from the run's regions *)
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRGs.
pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HRGn.
cbn [ms_mem restrict] in HRGs, HRGn.
assert (VFD : val_mem SEGS (mrestrict (w_H W1) (ms_mem msC)) X 4 (axfd cx)).
{ pose proof (field_of_region Ea _ 34%nat X _ 0 4 0 4 0 4%N (SOff 8 0) (axfd cx) HRGs U34a (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite OLDa by lia; rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (VNS : val_mem SEGS (mrestrict (w_H W1) (ms_mem msC)) (rg_nsrc RG) 4 (n + 1)).
{ pose proof (field_of_region Ea _ 308%nat (rg_nsrc RG - 484) _ 484 488 484 488 484 4%N (SOff 32 1) (n + 1) HRGn U308a
    (or_introl eq_refl)
    ltac:(cbn [sv_denot]; rewrite OLDa by lia; rewrite E32, unsigned_lit_small by lia; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv.
  replace (rg_nsrc RG - 484 + 484) with (rg_nsrc RG) in Hv by lia. exact Hv. }
assert (WNC : awr W1 (ms_mem msC) (rg_nsrc RG) 4).
{ pose proof HRGn as HRGn'. unfold region_ok in HRGn'.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HRGn'.
  destruct HRGn' as (_ & _ & HWn & _). rewrite U308a in HWn.
  intros i Hi. unfold arm. replace (rg_nsrc RG + i) with (rg_nsrc RG - 484 + (484 + i)) by lia. apply HWn. lia. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ [2; 3; 4; 8; 18; 23; 24; 25; 26; 27]%bv HS HAEa
  ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W1) m1 a <> None).
{ intros a Ha. destruct HLK as (V0 & V4 & V8 & _).
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [|destruct (Z_lt_ge_dec a (rg_lock RG + 8))].
  - replace a with (rg_lock RG + (a - rg_lock RG)) by lia.
    exact (ra_view_some _ _ (rg_lock RG) 4 _ (a - rg_lock RG) V0 ltac:(cbn; lia)).
  - replace a with (rg_lock RG + 4 + (a - rg_lock RG - 4)) by lia.
    exact (ra_view_some _ _ (rg_lock RG + 4) 4 _ (a - rg_lock RG - 4) V4 ltac:(cbn; lia)).
  - replace a with (rg_lock RG + 8 + (a - rg_lock RG - 8)) by lia.
    exact (ra_view_some _ _ (rg_lock RG + 8) 4 _ (a - rg_lock RG - 8) V8 ltac:(cbn; lia)). }
(* ---- RAU at 0x82c04 *)
pmkst HS.
apply KU. unfold RAU.
exists (ms_regs msC), ly1, S1, (ms_mem msC). eexists. exists k1, T1.
split; [reflexivity|].
split; [unfold aregs_held, aregs_base, spZ; rewrite !HK by (cbv; tauto); exact HRH|].
split; [exact Hfd|].
split.
{ split; [exact HJ2|].
  split; [eapply ajournal_gx_rom_view; first [exact HJ2 | exact HROMO | exact HROM0 | exact LAWS | exact pa_segs_low]|].
  split; [intros a Hi Ho He Hp; apply (apresent_grows _ _ _ a HGrC); apply HPR2; exact (HPK1 a Hi Ho He Hp)|].
  split.
  { intros i Hi. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem msC) _ 8 _); [|exact (HSV i Hi)].
    intros kk Hk. cbn in Hk. apply KALL; unfold asp0, RA_FRAME, ESTACK, AENT in *; lia. }
  split.
  { apply (alock_at_kept RG W1 m1 W1 (ms_mem msC) true HLK).
    intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    apply GW; [exact (ra_lock_in RG a Ha) | ra_pick HRGP 2%nat 3%nat D23; lia | exact (LKV a Ha)]. }
  split.
  { unfold awake_at. apply (val_mem_kept SEGS (w_H W1) (w_H W1) m1 (ms_mem msC) _ 4 _); [|exact HWAKE].
    intros kk Hk. cbn in Hk. destruct (HWK (rg_wake RG + 4 + kk) ltac:(lia)) as (Hi & _).
    pose proof (pa_img_range _ Hi). ra_pick HRGP 3%nat 6%nat D36.
    apply KALL; [lia | lia | intros Hs; destruct HToff; unfold AENT in *; lia | unfold asp0, ESTACK in *; lia]. }
  split; [exact HFR|].
  (* errno's four bytes: image bytes below kLowMemEnd, none of RA_G (so not g_nsrc), off the heap slot and below
     memset's scratch: kept by both runs and by the memset *)
  eapply ra_errno_step; [exact HERR1|]. intros i Hi.
  assert (EL : 0 <= as_errno B + i < kLowMemEnd /\ in_img SEGS (as_errno B + i)) by (eapply ra_errno_low; eassumption).
  assert (EN : ~ inG (RA_G RG) (as_errno B + i)) by (eapply ra_errno_notG; eassumption).
  destruct EL as [_ Himg]. pose proof (pa_img_range _ Himg).
  apply KALL; [lia | intros Hn; exact (EN (ra_nsrc_in RG _ Hn)) | intros Hs; destruct HToff; unfold AENT in *; lia
    | unfold asp0, ESTACK in *; lia]. }
split.
{ assert (KS : forall x, rg_src RG <= x < rg_src RG + Z.of_nat 8 -> abyte_kept W1 m1 W1 (ms_mem msC) x).
  { intros x Hx. cbn in Hx. apply GW; [exact (ra_src_in RG x Hx) | ra_pick HRGP 3%nat 5%nat D35; lia |].
    replace x with (rg_src RG + (x - rg_src RG)) by lia.
    exact (ra_view_some _ _ (rg_src RG) 8 _ (x - rg_src RG) Ms ltac:(cbn; lia)). }
  assert (KC : forall x, rg_capsrc RG <= x < rg_capsrc RG + Z.of_nat 4 -> abyte_kept W1 m1 W1 (ms_mem msC) x).
  { intros x Hx. cbn in Hx. apply GW; [exact (ra_capsrc_in RG x Hx) | ra_pick HRGP 3%nat 4%nat D34; lia |].
    replace x with (rg_capsrc RG + (x - rg_capsrc RG)) by lia.
    exact (ra_view_some _ _ (rg_capsrc RG) 4 _ (x - rg_capsrc RG) Mc ltac:(cbn; lia)). }
  assert (HPADS : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (axes cx)).
  { eapply Forall_impl; [|exact Hents]. intros e (_ & _ & EP1 & EP2 & _). split; assumption. }
  assert (HPADS2 : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat)
    (axes cx ++ [ra_new (axfd cx)])).
  { apply Forall_app. split; [exact HPADS | constructor; [split; reflexivity | constructor]]. }
  pose proof (ra_concat_len _ HPADS) as HCL.
  destruct Htab as (Tl1 & Tl2 & Tg). unfold ATABLE, AENT in Tl1.
  assert (HTL : (56 <= length tail)%nat) by lia.
  rewrite <- (firstn_skipn 56 tail) in Tg. unfold bzs in Tg. rewrite !map_app in Tg.
  apply garr8_app in Tg as [GCE Tg]. apply garr8_app in Tg as [_ GTL].
  rewrite !length_map, HCL, length_firstn in GTL.
  replace (T1 + Z.of_nat (56 * length (axes cx)) + Z.of_nat (Nat.min 56 (length tail))) with (X + 56) in GTL by lia.
  unfold arelay_at.
  split; [exact (akept_vm W1 m1 W1 (ms_mem msC) (rg_src RG) 8 T1 KS Ms)|].
  split; [exact (akept_awr W1 m1 W1 (ms_mem msC) (rg_src RG) 8 (fun x Hx => KS x ltac:(cbn; lia)) Ws)|].
  split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact VNS|].
  split; [exact WNC|].
  split; [exact (akept_vm W1 m1 W1 (ms_mem msC) (rg_capsrc RG) 4 16 KC Mc)|].
  split; [exact (akept_awr W1 m1 W1 (ms_mem msC) (rg_capsrc RG) 4 (fun x Hx => KC x ltac:(cbn; lia)) Wc)|].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [exact HTin|].
  split.
  { exists (skipn 56 tail). unfold atable_at.
    split; [rewrite length_skipn, length_app; cbn [length]; unfold ATABLE, AENT; lia|].
    split; [rewrite length_app, (ra_concat_len _ HPADS2), length_skipn, length_app; cbn [length]; unfold ATABLE; lia|].
    rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r.
    unfold bzs. rewrite !map_app, <- app_assoc.
    apply garr8_app. split.
    { apply (ra_garr8_kept (w_H W1) (w_H W1) m1 (ms_mem msC) T1 _ GCE).
      intros b Hb. rewrite length_map, HCL in Hb. apply KTB; lia. }
    rewrite length_map, HCL. replace (T1 + Z.of_nat (56 * length (axes cx))) with X by lia.
    apply garr8_app. split.
    { rewrite ra_new_bytes. apply garr8_app. split.
      - rewrite ra_le4_bytes by lia. exact (ra_le_garr8 _ X 4 (axfd cx) VFD ltac:(cbn; lia)).
      - rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4.
        apply ra_garr8_zeros. intros j Hj. cbn in Hj.
        rewrite (KR2 (X + Z.of_nat 4 + j) ltac:(lia) ltac:(intros Hs; destruct HToff; lia) ltac:(lia)).
        replace (X + Z.of_nat 4 + j) with (X + (4 + j)) by lia. apply HZ2. lia. }
    rewrite length_map, (ra_eb_len (ra_new (axfd cx)) eq_refl eq_refl).
    replace (X + Z.of_nat 56) with (X + 56) by lia.
    apply (ra_garr8_kept (w_H W1) (w_H W1) m1 (ms_mem msC) (X + 56) _ GTL).
    intros b Hb. rewrite length_map, length_skipn in Hb. apply KTB; lia. }
  split.
  { apply Forall_app. split.
    - rewrite Forall_forall in Hents |- *. intros e He.
      apply (aentry_ok_kept B ly1 S1 W1 m1 ly1 S1 W1 (ms_mem msC) e (Hents e He)).
      + intros r Hr a Ha.
        destruct (ra_efp_in_block ly1 S1 W1 m1 e (Hents e He) r a Hr Ha) as (p & mm & Hpm & Hpa).
        pose proof (ra_efp_off_slot B RG LAWS ly1 S1 W1 m1 md1 T1 (axes cx) HAR HREL ltac:(lia) e r a He Hr Ha) as Hsl.
        change (Z.of_nat (length (axes cx))) with n in Hsl.
        split; [apply (KBK p mm a Hpm Hpa); unfold AENT in *; lia|].
        intros _. destruct (al_blocks _ _ LAWS ly1 S1 W1 (ms_mem msC) _ p mm HARC Hpm) as (_ & _ & _ & _ & HpC & _).
        exact (apresent_writable SEGS _ _ a (proj1 (HpC a Hpa))).
      + exact (ra_eblks_in ly1 S1 W1 m1 e (Hents e He)).
    - constructor; [apply ra_new_ok; lia | constructor]. }
  split.
  { rewrite map_app. cbn [map re_fd ra_new]. apply NoDup_ListNoDup.
    apply (Permutation_NoDup (Permutation_app_comm [axfd cx] (map re_fd (axes cx)))).
    cbn [app]. constructor; [exact HnotIn | apply NoDup_ListNoDup; exact HNDfd]. }
  (* arelay_at's 12th conjunct (W_rep.v:170, no entry's block is the table block): the old entries by RAA's arelay_at
     at the same table T1 (HNOTAB), the new entry owns no block (ra_new: cap 0, held array 0, no keys) *)
  apply Forall_app. split; [exact HNOTAB|].
  constructor; [|constructor]. intros b Hb. cbn in Hb. destruct Hb. }
split; [exact HML | exact HBLK].
Qed.
End c.
End b.
End a.
