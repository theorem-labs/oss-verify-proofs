(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: the generic helpers of proofs/libreac/fuzz_decode/lib/A/Prog/YC1g.v (st_ok_pi_set_reg, st_ok_pi_region_nth, ew_Eimg_Ereg_nat), YC4b.v (PTR, Bspan, st_ok_region_nth, field_of_region, awr_ok_cons_gen, writable_kept, region_kept_aview, kept_of_frame), LLVMFuzzerTestOneInput_seg_entry.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved, garr8_kept, rdword_kept, saved_slot) and LLVMFuzzerTestOneInput_seg_exit_tail.v (t_fp_token, t_journal_io), gathered in one file for reac-repacer/fuzz_uci's image-A walks; the listing is uci_listing over usym (lib/A/Prog/UciPList.v), the sink head the core's AE2k.tfib_sink_head; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/LLVMFuzzerTestOneInput_seg_lib.v, with its module paths changed; 9 of its 191 lines of code are new or changed and 6 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_lib: the helpers every image-B walk of fuzz_wire.asan-ubsan uses with the Pa engine
   (the image-generic lib/A/Prog/PaRun.v, PaShadow.v, PaStep.v, at image B's listing lib/B/Prog/WirePPa.v, WirePImg.v,
   WirePPaLib.v and journal lib/B/Prog/PaJournal.v), apart from any one function: reading a register or a region of a
   symbolic state, the write rights of a run, what a run keeps, words and byte arrays read through the image view, and
   the two journal facts the slot post reads: fuzz_uci's image-A helpers (its lib/A/Prog/LLVMFuzzerTestOneInput_seg_lib.v)
   at image B's modules (the B core's lib/B/YCbq.v / YC5d.v journal). No statement about LLVMFuzzerTestOneInput is made
   here. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B Require Import YCbq YC5d.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YI16.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import PaRun PaShadow.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.B.Prog Require Import PaJournal WirePSyms WirePList WirePAddr WirePPa
  WirePPaLib WirePImg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The shadow base, the pointer fact of an application address, and the span of the shadow band the token engine
   checks (YC4b.v). *)
Definition SBv : Z := 0x7fff8000.
Lemma SBv_SHADOW_OFF : SBv = SHADOW_OFF.
Proof. reflexivity. Qed.
Definition PTR (al : Z) : afact := mkAF 4096 140737479966720 al.
Definition Bspan : Z * Z := (SBv, SBv + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ------------------------------------------------------------------ *)
(* 1. Symbolic states                                                   *)
(* ------------------------------------------------------------------ *)

Section s.
Context {segs : list Segment}.
Lemma st_ok_region_nth : forall E ss ms i r,
  st_ok segs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok segs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok segs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma field_of_region : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem segs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok segs E m b od w e v Hck He Hv Hw).
Qed.
Lemma writable_kept : forall H (m m2 : word -> option byte) a,
  (apresent H m a -> apresent H m2 a) -> writable_at segs (mrestrict H m) a -> writable_at segs (mrestrict H m2) a.
Proof.
intros H m m2 a Hp Hw. unfold writable_at, wview, mrestrict in *. revert Hw.
destruct (H (Z_to_bv 64 a)) eqn:EH; intros Hw; [exact Hw|].
destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
- destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
- destruct (m2 (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma region_kept_aview : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview segs H m2 a = aview segs H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  region_kept segs E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- apply writable_kept. apply Hp.
Qed.
Lemma kept_of_frame : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of segs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
End s.

Section f.
Context {L : ptable wsym} {PL : PAListing L} {PI : PAImg L}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation VAL := (pa_val).
#[local] Abbreviation BASE := (pa_val A_TEXT).
Lemma st_ok_pi_set_reg : forall E ss ms (r : bv 5) e,
  st_ok_pi SEGS VAL E ss ms -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
  st_ok_pi SEGS VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr He. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
exact (st_ok_set_reg SEGS E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms r e HS Hr He).
Qed.
Lemma st_ok_pi_region_nth : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth E (abs_ss VAL ss) ms i r HS ltac:(destruct ss; exact Hi)). Qed.
Lemma ew_Eimg_Ereg_nat : forall (regs : bvmap 5 word) extra n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof.
intros regs extra n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma ew_Eimg_Ereg_extra : forall (regs : bvmap 5 word) extra j,
  ew (Eimg (Ereg regs extra)) (32 + j) = nth j extra (Z_to_bv 64 0) \/ (A_TEXT <= 32 + j)%nat.
Proof.
intros regs extra j. destruct (Nat.lt_ge_cases (32 + j) A_TEXT) as [H|H]; [left|right; exact H].
rewrite Eimg_low by exact H. apply ew_Ereg_extra.
Qed.
End f.

(* ------------------------------------------------------------------ *)
(* 2. Words and byte arrays read through the image view                 *)
(* ------------------------------------------------------------------ *)

Lemma val_mem_of_rd32 : forall segs H mem a v,
  rd32 (aview segs H mem) a v -> val_mem segs (mrestrict H mem) a 4 v.
Proof.
intros segs H mem a v Hr k Hk. pose proof (Hr k Hk) as Hb.
destruct (aview_byte segs H mem _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.
Lemma rdword_of_val_mem : forall segs H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros segs H mem a v Hv Hr.
assert (B : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.
Lemma val_mem_moved : forall segs H H' (m m' : word -> option byte) a b n v,
  (forall k, 0 <= k < Z.of_nat n -> aview segs H' m' (b + k) = aview segs H m (a + k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') b n v.
Proof.
intros segs H H' m m' a b n v Hk Hv k Hkn. specialize (Hk (Z.of_nat k) ltac:(lia)). unfold aview in Hk.
rewrite (Hv k Hkn) in Hk. destruct (mbyte segs (mrestrict H' m') (b + Z.of_nat k)) as [b'|]; cbn in Hk; [|discriminate].
injection Hk as Hk. f_equal. apply bv_eq. exact Hk.
Qed.
Lemma garr8_kept : forall segs H H' (m m' : word -> option byte) base l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H' m' (base + j) = aview segs H m (base + j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros segs H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved segs H H' m m' (base + Z.of_nat j) (base + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk. replace (base + Z.of_nat j + k) with (base + (Z.of_nat j + k)) by lia. apply HK. lia.
Qed.
Lemma rdword_kept : forall (r r' : reader) a, (forall i, 0 <= i < 8 -> r' (a + i) = r (a + i)) -> rdword r' a = rdword r a.
Proof.
intros r r' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1 ltac:(lia)), (H 2 ltac:(lia)), (H 3 ltac:(lia)), (H 4 ltac:(lia)), (H 5 ltac:(lia)),
  (H 6 ltac:(lia)), (H 7 ltac:(lia)). reflexivity.
Qed.
Lemma saved_slot : forall segs E m n cs lo hi wlo whi off (r : nat) b,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk off (CVal 8 (SOff r 0))) cs ->
  val_mem segs m (b + off) 8 (bv_unsigned (ew E r)).
Proof.
intros segs E m n cs lo hi wlo whi off r b HR Hb Hin.
apply (field_of_region E m n b cs lo hi wlo whi off 8 (SOff r 0) (bv_unsigned (ew E r)) HR Hb Hin).
- cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (ew E r)) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
  change (8 * Z.of_N 8) with 64. exact Hw.
- cbv. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* 3. The journal facts the slot post reads                            *)
(* ------------------------------------------------------------------ *)

Section jf. Context {SK : YI16.sink_head}.
(* A journal with no file range (FP = []) is one with the sink token's range as FP: the token only widens what the
   journal allows, and no clause of the [] journal ever holds an address in a range. *)
Lemma t_fp_token : forall (segs : list Segment) B STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  @ajournal rc SK segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  @ajournal rc SK segs B STK sp0 [YI16.sink_token] ly S W mem md own ly' S' W' mem' md' k.
Proof.
intros segs B STK sp0 ly S W mem md own ly' S' W' mem' md' k
  (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
split; [exact HAR|]. split; [exact Hly|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_mono; [|exact Hio]; intros Hc; exfalso; exact (sink_closed_nil Hc)|].
split; [exact Hfrs|]. split; [exact Hnev|]. split; [exact Hk|]. split; [exact F1|].
split; [intros p n i H1 H2 Hi _; exact (F2 p n i H1 H2 Hi (inFP_nil (p + i)))|].
split; [intros a Hi Ho He _; exact (F3 a Hi Ho He (fp_spares_closed [] a sink_closed_nil))|].
split; [intros cid pos a Hin Hr _; exact (F4 cid pos a Hin Hr (inFP_nil a))|].
split; [intros p n i H1 H2 Hi; exfalso; exact (inFP_nil _ (Hgone p n i H1 H2 Hi))|].
split; [exact Hpres|]. split; [exact Hstk|]. split; [exact F5 | exact HQT].
Qed.
(* At FP = [] the file descriptors and the file system are the entry's (cgif lib/A/ACfh.v ajournal_closed_io). *)
Lemma t_journal_io : forall (segs : list Segment) B STK sp0 ly S (W : world segs) mem md own ly' S' W' mem' md' k,
  @ajournal rc SK segs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros segs B STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ. pose proof HJ as (_ & _ & _ & _ & Hos & _).
destruct (aos_step_closed [] md md' sink_closed_nil Hos) as (Efd & Efsys & _ & _).
unfold m_fds, m_fs. rewrite Efd, Efsys. split; reflexivity.
Qed.
End jf.
End d.
