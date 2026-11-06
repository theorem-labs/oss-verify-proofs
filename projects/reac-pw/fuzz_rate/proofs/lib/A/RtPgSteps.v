(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v, with its module paths and module names changed; 1062 of its 1144 lines of code are new or changed and 417 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSteps.v at 6bdf633122fe for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; the jump
   table's site, table and targets and the fuzz_u32 sites are rate's (their registers: the cursor in s9, the shadow
   offset in s2, the original byte count in a5 / a7, no frame cell); the prefix rl_ becomes rts_; the image facts
   wx_segs_nowrap / segs-low and same_io_wvb are stated here instead of taken from a cfg walk file; the block-chaining
   lemmas and helpers (from proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v and RPgW6aHead.v at ef33766f272a), the
   intrinsic call adapter (RPgW6aHead.v w6h_intrin, for both OSet and OCpy), the generic ecall adapter, the class-3
   frame arithmetic and the frame write rights are added. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address below is measured on its unstripped
   twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, whose loaded bytes are the same): the
   step kit of the image-A walk of LLVMFuzzerTestOneInput (0x80714, 3039 instructions). Proves no function (kind:
   segment lemma): each lemma is a step or a block of steps the walk lanes of M01 / M02 / M03 use, stated over the
   kit's engine (lib/Reusable: st_ok, sh_ok, ajournal, SRr) and image A's segments (images.Asan loaded_segments).
   PART 1 the jump table (rts_jt_block); PART 2 the fuzz_u32 read-ahead (rts_u32_block2 / 3); PART 3 chaining
   (rts_post_seq, rts_blk_seq), the memset / memcpy call (rts_intrin_seq), any leaf runtime call in the ecall form
   (rts_ecall_seq), the class-3 frame (rts_fbounds, rts_fsh_addr) and its write rights (rts_awr_ok_fsh / _fobj).
   The inline steps (put32's two checks and four stores, the pp->len check and update, fuzz_u8's check and load,
   the scope stores) are single engine steps of a walk lane's own run: the token engine (YCbn) covers their
   checks, and RtPgMem's byte / shadow lemmas read the result.

   PART 1. THE JUMP TABLE OF ent_build (pod.h:281, `switch (kind % 10)`), the one computed jump of the function:
     0x8130c  bltu a2,a1 -> 0x81954      a2 = 8: k = kind % 10 = 9 goes to case 9 without the table
     0x81310  slli a1,a1,2
     0x81314  auipc a2,0xfffa0 / 0x81318 addi a2,a2,-0x3b0     a2 = 0x20f64, the table (.rodata, read-only)
     0x8131c  add a1,a1,a2 / 0x81320 lw a1,0(a1)             the entry of k (a 32-bit offset from the table)
     0x81324  slli a0,a0,0x38 / 0x8132c srai s6,a0,0x38        s6 = the kind byte, sign-extended
     0x81328  add a1,a1,a2
     0x81330  jr a1                                             to 0x20f64 + entry k
   The nine entries, read from the image (PT_LOAD R [0x10000, 0x2f9d4)), give the targets 0x81334 (case 0) 0x817c4 (1)
   0x816ac (2) 0x81710 (3) 0x81668 (4) 0x81804 (5) 0x81880 (6) 0x81754 (7) 0x818d0 (8). The `lw` carries no
   instrumented check. The engine (YP0l sym_step) follows `jr` when the register is a literal and loads a literal from
   an image chunk (YP09 CImg) of a base-free region at a literal address. So the step is: the table as the read-only
   region jt_region (one CImg chunk of 36 bytes), proved from rom_view (jt_region_ok); k split into its nine values
   (jt_cases); the register of k pinned to the literal. rts_jt_block is that step at the concrete site, as a block
   lemma in the shape of a callee contract (rts_blk_post): from 0x81310 with a1 = k, 0 <= k <= 8, to 0x20f64 + entry k
   with a1, a2, a0, s6 set and every other register, the journal and every byte as before. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image A's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================== image A ======================================== *)
(* the writable and the executable segments do not overlap, and nothing wraps *)
Lemma rts_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
(* every image byte lies below the low shadow *)
Lemma rts_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
(* a run's lazy-VM backing changes no I/O state *)
Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

(* ======================================== read-only bytes of image A ======================================== *)
(* a lies in a read-only PT_LOAD of image A, as a boolean the kernel can decide *)
Definition in_rom_b (a : Z) : bool :=
existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) rsegs.
Lemma in_rom_b_ok : forall a, in_rom_b a = true -> in_rom rsegs a.
Proof.
intros a H. unfold in_rom_b in H. apply existsb_exists in H as (sg & Hin & Hb).
apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists sg. split; [exact Hin|]. split; [exact H0 | lia].
Qed.
(* every byte of [a, a + n) is read-only and has an image byte *)
Definition rom_run_b (a : Z) (n : nat) : bool := YP08.zallb (fun x => in_rom_b x && YP08.img_byte_ok rsegs x) a n.
Section rom. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* a read-only byte of the image as the walk's memory shows it, from rom_view *)
Lemma mbyte_rom : forall (W : world rsegs) mem a, rom_view rsegs W mem -> in_rom_b a = true -> YP08.img_byte_ok rsegs a = true ->
exists b, img_byte rsegs a = Some b /\ mbyte rsegs (mrestrict (w_H W) mem) a = Some b.
Proof.
intros W mem a HR Hr Hi. pose proof (HR a (in_rom_b_ok a Hr)) as Hv. unfold aview in Hv.
unfold YP08.img_byte_ok, img_byte in Hi. unfold img_byte.
destruct (seg_rom rsegs (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate Hi].
exists b. split; [reflexivity|].
destruct (mbyte rsegs (mrestrict (w_H W) mem) a) as [b'|] eqn:Eb'; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq. exact Hv.
Qed.
(* a base-free read-only region whose only chunk is the image's bytes [lo, lo + n) *)
Lemma img_region_ok_rom : forall E (W : world rsegs) mem lo n,
rom_view rsegs W mem -> 0 <= lo -> lo + n <= 2 ^ 64 -> 0 <= n ->
rom_run_b lo (Z.to_nat n) = true ->
region_ok rsegs E (mrestrict (w_H W) mem) (YP09.mkRegion None lo (lo + n) 0 0 [YP09.mkChunk lo (CImg n)]).
Proof.
intros E W mem lo n HR Hlo Hhi Hn Hb. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *. rewrite !Z.add_0_l.
pose proof (YP08.zallb_sound _ _ _ (lo + i) Hb ltac:(lia)) as Hx. apply andb_prop in Hx as [Hx1 Hx2].
exact (mbyte_rom W mem (lo + i) HR Hx1 Hx2).
Qed.
End rom.

(* ======================================== PART 1. the jump table ======================================== *)
Definition JT_A : Z := 0x20f64.
Definition JT_PC : Z := 0x81310.
Definition jt_region : YP09.region := YP09.mkRegion None JT_A (JT_A + 36) 0 0 [YP09.mkChunk JT_A (CImg 36)].
Lemma jt_rom : rom_run_b JT_A 36 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jt_region_ok : forall {fx : YK11.FPState} {rc : YM05.RunCeil} E (W : world rsegs) mem,
rom_view rsegs W mem -> region_ok rsegs E (mrestrict (w_H W) mem) jt_region.
Proof. intros fx rc E W mem HR. apply img_region_ok_rom; [exact HR | unfold JT_A; lia | unfold JT_A; lia | lia | exact jt_rom]. Qed.
(* the entry of k as the `lw` reads it (little-endian, sign-extended), and the target *)
Definition jt_ent (k : Z) : Z :=
match img_bytes rsegs (JT_A + 4 * k) 4 with
| Some bs => let v := bytes_le_to_Z bs in if v <? 2 ^ 31 then v else v - 2 ^ 32
| None => 0
end.
Definition jt_tgt (k : Z) : Z := JT_A + jt_ent k.
Lemma jt_tgts : map jt_tgt [0; 1; 2; 3; 4; 5; 6; 7; 8] =
[0x81334; 0x817c4; 0x816ac; 0x81710; 0x81668; 0x81804; 0x81880; 0x81754; 0x818d0].
Proof. vm_compute. reflexivity. Qed.
Lemma jt_tgt_vals : jt_tgt 0 = 0x81334 /\ jt_tgt 1 = 0x817c4 /\ jt_tgt 2 = 0x816ac /\ jt_tgt 3 = 0x81710 /\
jt_tgt 4 = 0x81668 /\ jt_tgt 5 = 0x81804 /\ jt_tgt 6 = 0x81880 /\ jt_tgt 7 = 0x81754 /\ jt_tgt 8 = 0x818d0.
Proof. vm_compute. repeat split. Qed.
(* the nine values of k after `bltu 8,k` falls through *)
Lemma jt_cases : forall k, 0 <= k <= 8 ->
k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8.
Proof. intros k Hk. lia. Qed.


(* ===================================== generic engine helpers ===================================== *)
Section gen. Context {fx : YK11.FPState}.
Variable segs : list Segment.
(* a register pinned to any sv whose value it holds *)
Lemma st_ok_pin_sv : forall E ss ms (r : bv 5) e,
st_ok segs E ss ms -> bv_eqb r 0 = false -> sv_denot E e = getr (ms_regs ms) r ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e HS Hr0 He.
apply (st_ok_regs segs E ss ms (sr_set (ss_regs ss) r e) HS).
intros rr. destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. rewrite He. exact (st_ok_reg segs E ss ms r HS).
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
(* a register pinned to a literal it holds (after a case split) *)
Lemma st_ok_pin_lit : forall E ss ms (r : bv 5) z,
st_ok segs E ss ms -> bv_eqb r 0 = false -> getr (ms_regs ms) r = Z_to_bv 64 z ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r z HS Hr0 Hr.
apply (st_ok_regs segs E ss ms (sr_set (ss_regs ss) r (SLit z)) HS).
intros rr. destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. rewrite <- (st_ok_reg segs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
(* the 31 registers other than x0 *)
Definition nz_regs : list (bv 5) :=
[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Lemma in_nz_regs : forall r : bv 5, bv_unsigned r <> 0 -> In r nz_regs.
Proof.
intros r Hr. pose proof (u5_range r) as Hb.
rewrite <- (Z_to_bv_bv_unsigned 5 r).
assert (H : bv_unsigned r = 1 \/ bv_unsigned r = 2 \/ bv_unsigned r = 3 \/ bv_unsigned r = 4 \/ bv_unsigned r = 5 \/
  bv_unsigned r = 6 \/ bv_unsigned r = 7 \/ bv_unsigned r = 8 \/ bv_unsigned r = 9 \/ bv_unsigned r = 10 \/
  bv_unsigned r = 11 \/ bv_unsigned r = 12 \/ bv_unsigned r = 13 \/ bv_unsigned r = 14 \/ bv_unsigned r = 15 \/
  bv_unsigned r = 16 \/ bv_unsigned r = 17 \/ bv_unsigned r = 18 \/ bv_unsigned r = 19 \/ bv_unsigned r = 20 \/
  bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/ bv_unsigned r = 25 \/
  bv_unsigned r = 26 \/ bv_unsigned r = 27 \/ bv_unsigned r = 28 \/ bv_unsigned r = 29 \/ bv_unsigned r = 30 \/
  bv_unsigned r = 31) by lia.
repeat (destruct H as [H|H]; [rewrite H; cbv [nz_regs In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
rewrite H. cbv [nz_regs In]. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
(* as regs_kept_of_st_ok, but some registers are pinned to an sv of the entry's value (s2 to the shadow-base atom) *)
Lemma regs_kept_of_st_ok_pins : forall E ss ms regs0 extra (H : word -> bool) (clob : list (bv 5)) (pins : list (bv 5 * sv)),
st_ok segs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
(forall r e, In (r, e) pins -> sv_denot E e = getr regs0 r) ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob
  || existsb (fun p => bv_eqb (fst p) r && sv_eqb (sr_get (ss_regs ss) r) (snd p)) pins
  || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H clob pins HS HA Hp Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- apply orb_prop in Hq as [Hq|Hq].
  + exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
  + apply existsb_exists in Hq as (pp & Hpp & Hb). destruct pp as [pr pe]. cbn [fst snd] in Hb.
    apply andb_prop in Hb as [Hb1 Hb2]. apply bv_eqb_eq in Hb1. apply sv_eqb_eq in Hb2.
    rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hb2. rewrite <- Hb1. exact (Hp pr pe Hpp).
- apply sv_eqb_eq in Hq. destruct HA as [HA _].
  rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
  rewrite HA. 2:{ pose proof (u5_range r). lia. }
  rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* every register outside clob keeps its entry value: the symbolic register is still its own atom *)
Lemma regs_kept_of_st_ok : forall E ss ms regs0 extra (H : word -> bool) (clob : list (bv 5)),
st_ok segs E ss (restrict H ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra H clob HS [HA _] Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA. 2:{ pose proof (u5_range r). lia. }
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End gen.

(* the shift arithmetic of `slli a0,a0,0x38` / `srai s6,a0,0x38` (the kind byte, sign-extended) *)
Definition sext8 (b : Z) : Z := if b <? 128 then b else b - 256.
Lemma Z_to_bv_mod64 : forall x, Z_to_bv 64 (x mod 2 ^ 64) = Z_to_bv 64 x.
Proof.
intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Z.mod_mod. lia.
Qed.
Lemma sll56_mod : forall u, 0 <= u -> (u * 2 ^ 56) mod 2 ^ 64 = (u mod 256) * 2 ^ 56.
Proof.
intros u Hu. replace (2 ^ 64) with (256 * 2 ^ 56) by reflexivity.
apply Z.mul_mod_distr_r; lia.
Qed.
Lemma sra56_sll56 : forall b, 0 <= b < 256 -> Z.shiftr (bv_swrap 64 (b * 2 ^ 56)) 56 = sext8 b.
Proof.
intros b Hb. unfold bv_swrap, bv_wrap, sext8. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.shiftr_div_pow2 by lia.
destruct (Z.ltb_spec b 128) as [Hl|Hg].
- rewrite (Z.mod_small (b * 2 ^ 56 + 2 ^ 63)) by lia. replace (b * 2 ^ 56 + 2 ^ 63 - 2 ^ 63) with (b * 2 ^ 56) by lia.
apply Z.div_mul. lia.
- replace (b * 2 ^ 56 + 2 ^ 63) with ((b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64) + 1 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace (b * 2 ^ 56 + 2 ^ 63 - 2 ^ 64 - 2 ^ 63) with ((b - 256) * 2 ^ 56) by lia.
apply Z.div_mul. lia.
Qed.

(* ===================================== the post of a block of steps =====================================
   A block lemma ends at a fixed pc, like a segment, and keeps what a callee keeps: the journal (no event), the
   frames, blocks, I/O state and meter, every register outside the list clob, and every byte. R says what the
   block computes. A walk lane uses it as it uses a callee contract (SRr_bind, then the re-seat of its symbolic
   state with the registers of clob given fresh atoms). *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Definition rts_blk_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(clob : list (bv 5)) (R : bvmap 5 word -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R regs2.

(* ---- the dispatch block 0x81310 .. 0x81330 ---- *)
Definition jt_tbl : ctable := build_table rsegs JT_PC 9 TEmpty.
Lemma jt_tbl_ok : table_ok rsegs jt_tbl.
Proof. apply build_table_ok0. unfold JT_PC. lia. Qed.
Definition JT_SB : Z := 0x7fff8000.
Definition JTBx : sv := SOff 32 0.
Definition JTspan : Z * Z := (JT_SB, JT_SB + 2 ^ 44 - 1).
Definition jt_extra : list word := [Z_to_bv 64 JT_SB].
Definition jt_R (kk : Z) (regs regs2 : bvmap 5 word) : Prop :=
getr regs2 11 = w64 (jt_tgt kk) /\ getr regs2 12 = w64 JT_A /\
bv_unsigned (getr regs2 10) = (bv_unsigned (getr regs 10) mod 256) * 2 ^ 56 /\
getr regs2 22 = w64 (sext8 (bv_unsigned (getr regs 10) mod 256)).
Lemma rts_jt_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
0 <= kk <= 8 -> getr regs 11 = w64 kk -> rom_view rsegs W memc ->
SRr rsegs W (cfg_at rsegs JT_PC regs memc mdc)
(rts_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc (jt_tgt kk) [10; 11; 12; 22]%bv (jt_R kk regs)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs kk HJ Hk H11 HR.
pose proof rts_wx as Hwx. pose proof rts_segs_low as Hsegs.
assert (HS0 : st_ok rsegs (Ereg regs jt_extra) (mkSS JT_PC sr_atoms [jt_region] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 JT_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [apply jt_region_ok; exact HR | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (11%bv : bv 5) kk HS0 eq_refl H11) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs JTBx [] (Ereg regs jt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jt_extra) (Ereg regs jt_extra)) by apply env_agree_refl.
assert (E10 : ew (Ereg regs jt_extra) 10 = Z_to_bv 64 (bv_unsigned (getr regs 10)))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (u64_range (getr regs 10)) as Hu10.
unfold cfg_at. change (w64 JT_PC) with (Z_to_bv 64 JT_PC).
destruct (jt_cases kk Hk) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
(lazymatch goal with |- context [jt_tgt ?t] => let st := eval vm_compute in (jt_tgt t) in
   aj_run_to_tok jt_tbl_ok HS HJ SHOK JTspan st end;
 [ awr_ok_tac
 | apply SRr_ret;
   lazymatch type of HS with st_ok _ _ ?ssf _ =>
     let t := eval vm_compute in (ss_pc ssf) in
     replace (jt_tgt _) with t by (vm_compute; reflexivity) end;
   red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc);
   split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
   split; [exact HJ|];
   split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
   split; [reflexivity|];
   split; [apply Permutation_refl|];
   split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
   split; [apply mo_le_refl; assumption|];
   split;
   [ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
     intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]]; cbn in Hr; lia
   | unfold jt_R;
     rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS);
     lazymatch type of HS with st_ok _ _ ?ssf _ =>
       let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
       let e11 := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
       let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
       let e22 := eval vm_compute in (sr_get (ss_regs ssf) (22%bv : bv 5)) in
       change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
       change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e11;
       change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12;
       change (sr_get (ss_regs ssf) (22%bv : bv 5)) with e22 end;
     split; [unfold w64; f_equal; vm_compute; reflexivity|];
     split; [unfold w64; f_equal; vm_compute; reflexivity|];
     split;
     [ change (bv_unsigned (sv_denot (Ereg regs jt_extra) (SAlu ALU_SLL (SOff 10 0) (SLit 56))))
         with (U (Ereg regs jt_extra) (SAlu ALU_SLL (SOff 10 0) (SLit 56)));
       rewrite U_SAlu, U_SLit, (U_atom _ 10 _ E10 Hu10); cbn [zalu_raw];
       change (Z.land (zcanon 56) 63) with 56; rewrite Z.shiftl_mul_pow2 by lia;
       unfold zcanon, M64; apply sll56_mod; lia
     | rewrite denot_lit_U; unfold w64;
       rewrite !U_SAlu, !U_SLit, (U_atom _ 10 _ E10 Hu10); cbn [zalu_raw];
       change (Z.land (zcanon 56) 63) with 56; rewrite Z.shiftl_mul_pow2 by lia;
       unfold zcanon at 2, M64; rewrite sll56_mod by lia;
       rewrite sra56_sll56 by (pose proof (Z.mod_pos_bound (bv_unsigned (getr regs 10)) 256); lia);
       unfold zcanon, M64; apply Z_to_bv_mod64 ] ] ]).
Qed.
End d.
End b.

(* ============================== PART 2. the fuzz_u32 read-ahead (PLAN risk 4) ==============================
   fuzz.h:39-55's fuzz_u32 is inlined twice, in ent_build's cases 2 and 3 (the only two sites of the function).
   Both read up to four input bytes and compare the ORIGINAL byte count (n1 + 2, in a5 and copied to a7) with 3, 4
   and 5 to decide how many are there; so the length split is inside ONE lemma per site, not one file per length.
   Unlike role's image, rate's code keeps that count in a register, not in a frame cell, and its arms are spread:
     site 2  0x816d8 `beqz a1,0x81cf0`, reads at 0x816e4 / 0x81d54 / 0x82044 / 0x82094, join 0x81d7c .. end 0x81d94
     site 3  0x81c0c `beqz a1,0x81cfc`, reads at 0x81c18 / 0x81da4 / 0x8206c / 0x820b8, join 0x81dcc .. end 0x81de4
   (end = the pc after `or a2,a2,a4`). At the start: a1 = n1 (bytes left), s9 = c (the cursor), a4 = c - 2,
   a5 = n1 + 2, s2 = K, no store inside; the four shadow checks are the `bnez t,L` form (L = `andi u,s9,7;
   blt u,t,back; j report`, at 0x82220 .. 0x8227c), so the token engine (YCbn tok_load / tok_branch) takes both
   outcomes itself and leaves one obligation `range_addressable ... (c + i) 1` per read. The five arms (n1 = 0, 1,
   2, 3, >= 4) are the five ways out; in the first four n1 and n1 + 2 are literals and the engine decides the three
   `bne`s itself, in the fifth the atom facts 4 <= n1 and 6 <= n1 + 2 decide them. *)

(* ---- the model: the four bytes a cursor reads, past the end 0 ---- *)
Definition u32_b (rest : list byte) (i : nat) : Z := nth i (map (fun x : byte => bv_unsigned x) rest) 0.
Lemma u32_b_eq : forall rest i, u32_b rest i = bv_unsigned (nth i rest (Z_to_bv 8 0)).
Proof. intros rest i. unfold u32_b. rewrite <- (map_nth (fun x : byte => bv_unsigned x) rest (Z_to_bv 8 0) i). reflexivity. Qed.
Lemma u32_b_range : forall rest i, 0 <= u32_b rest i < 256.
Proof. intros rest i. rewrite u32_b_eq. apply Cursor.byte_range. Qed.
(* the value and the rest, with the length split done once *)
Lemma fuzz_u32_bytes : forall rest,
fst (Cursor.fuzz_u32 rest) = u32_b rest 0 + 256 * u32_b rest 1 + 65536 * (u32_b rest 2 + 256 * u32_b rest 3).
Proof.
intros rest. destruct rest as [|a [|b [|c [|d r]]]];
cbn [Cursor.fuzz_u32 Cursor.fuzz_u16 Cursor.fuzz_u8 u32_b nth map fst snd]; lia.
Qed.
Lemma fuzz_u32_rest_len : forall rest, length (snd (Cursor.fuzz_u32 rest)) = (length rest - 4)%nat.
Proof. intros rest. rewrite Cursor.fuzz_u32_rest. apply length_skipn. Qed.

(* ---- the bit arithmetic of the join (`or` of pieces that do not overlap) ---- *)
Lemma lor_shiftl_add : forall x y k, 0 <= k -> 0 <= x < 2 ^ k -> 0 <= y -> Z.lor x (Z.shiftl y k) = x + Z.shiftl y k.
Proof.
intros x y k Hk Hx Hy. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec, Z.shiftl_spec by lia.
destruct (Z.lt_ge_cases i k) as [Hl|Hg].
- rewrite (Z.testbit_neg_r y (i - k)) by lia. rewrite orb_false_r.
  rewrite <- (Z.mod_pow2_bits_low (x + Z.shiftl y k) k i) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
- assert (Ex : Z.testbit x i = false).
  { destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with k; [apply Z.log2_lt_pow2; lia | lia]. }
  rewrite Ex, orb_false_l. rewrite Z.shiftl_mul_pow2 by lia.
  replace i with ((i - k) + k) at 2 by lia. rewrite <- Z.div_pow2_bits by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small x) by lia. rewrite Z.add_0_l. reflexivity.
Qed.

Section ar. Context {fx : YK11.FPState}.
Lemma U_zext8 : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 -> U E (SExt false 8 (SOff n 0)) = b.
Proof.
intros E n b Hn Hb. rewrite U_SExt. cbv iota beta. rewrite (U_atom E n b Hn ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small b 256) by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma U_or0l : forall E e x, U E e = x -> 0 <= x < 2 ^ 64 -> U E (SAlu ALU_OR (SLit 0) e) = x.
Proof.
intros E e x He Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, He.
change (zcanon 0) with 0. rewrite Z.lor_0_l. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
Lemma U_or0r : forall E e x, U E e = x -> 0 <= x < 2 ^ 64 -> U E (SAlu ALU_OR e (SLit 0)) = x.
Proof.
intros E e x He Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, He.
change (zcanon 0) with 0. rewrite Z.lor_0_r. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.
(* `or lo, (hi << k)`: the engine's shape is SAlu OR (SAlu SLL hi (SLit k)) lo *)
Lemma U_or_sll : forall E ehi elo x y k,
U E ehi = y -> U E elo = x -> 0 <= k -> Z.land (zcanon k) 63 = k ->
0 <= x < 2 ^ k -> 0 <= y -> x + y * 2 ^ k < 2 ^ 64 ->
U E (SAlu ALU_OR (SAlu ALU_SLL ehi (SLit k)) elo) = x + y * 2 ^ k.
Proof.
intros E ehi elo x y k Hhi Hlo Hk Hland Hx Hy Hsum.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hhi, Hlo, Hland.
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
unfold zcanon, M64. rewrite (Z.mod_small (y * 2 ^ k)) by lia.
rewrite Z.lor_comm. rewrite <- (Z.shiftl_mul_pow2 y k) by lia.
rewrite lor_shiftl_add by (rewrite ?Z.shiftl_mul_pow2 by lia; lia).
rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia.
Qed.
(* the engine's other order: `or lo, (hi << k)` with the shift on the right (the 16-bit half) *)
Lemma U_or_sll_r : forall E ehi elo x y k,
U E ehi = y -> U E elo = x -> 0 <= k -> Z.land (zcanon k) 63 = k ->
0 <= x < 2 ^ k -> 0 <= y -> x + y * 2 ^ k < 2 ^ 64 ->
U E (SAlu ALU_OR elo (SAlu ALU_SLL ehi (SLit k))) = x + y * 2 ^ k.
Proof.
intros E ehi elo x y k Hhi Hlo Hk Hland Hx Hy Hsum.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hhi, Hlo, Hland.
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hp : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
unfold zcanon, M64. rewrite (Z.mod_small (y * 2 ^ k)) by lia.
rewrite <- (Z.shiftl_mul_pow2 y k) by lia.
rewrite lor_shiftl_add by (rewrite ?Z.shiftl_mul_pow2 by lia; lia).
rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia.
Qed.
End ar.

(* ---- a sub-range of an addressable range ---- *)
Lemma ra_sub : forall (rd : reader) (Bs a n x m : Z),
range_addressable rd Bs a n -> a <= x -> x + m <= a + n -> range_addressable rd Bs x m.
Proof. intros rd Bs a n x m H Ha Hb y Hy. apply H. lia. Qed.

Section u32e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition U32Bx : sv := SOff 32 0.
Definition U32span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition u32_extra (rest : list byte) (left nn : Z) : list word :=
  [w64 SHADOW_OFF; w64 (u32_b rest 0); w64 (u32_b rest 1); w64 (u32_b rest 2); w64 (u32_b rest 3); w64 left; w64 nn].
Definition u32_bchunks (m : nat) : list YP09.chunk :=
  map (fun i => YP09.mkChunk (2 + Z.of_nat i) (CVal 1 (SOff (33 + i) 0))) (seq 0 m).
Definition u32_in_region (m : nat) : YP09.region :=
  YP09.mkRegion (Some 14%nat) 2 (2 + Z.of_nat m) 0 0 (u32_bchunks m).
(* no input byte is read when nothing is left: then there is no region *)
Definition u32_regs_of (m : nat) : smem :=
  match m with O => [] | S _ => [u32_in_region m] end.
(* the cursor s9 = a4 + 2, the shadow offset s2, a1 = the bytes left, a5 = the original count *)
Definition u32_ss (pc : Z) (a1v a5v : sv) (m : nat) (G : facts) : sstate :=
mkSS pc (sr_set (sr_set (sr_set (sr_set sr_atoms (25%bv : bv 5) (SOff 14 2)) (18%bv : bv 5) (SOff 32 0))
  (11%bv : bv 5) a1v) (15%bv : bv 5) a5v)
  (u32_regs_of m) None G.
(* The atom facts. The engine places the shadow cell of every read in the span [K, K + 2^44) only from the
   cursor atom's upper bound (YCbn ob_in_span: (hi + offset) >> 3 < 2^44), so the bound of atom 14 = c - 2 is the
   arm's own: with m bytes read, c + m <= 2^47 - 1 (the input's amem_range) gives c - 2 <= 2^47 - 3 - m, and the
   highest read c + m - 1 stays below 2^47. The count atoms 37 / 38 need only their lower bounds 4 / 6 (they
   decide the three `bne`s). No allocation ceiling and no 2^26 bound is used. *)
Definition u32_facts0 (m : nat) : facts :=
  mkFacts [ (14%nat, mkAF 1 (140737488355325 - Z.of_nat m) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition u32_factsF : facts :=
  mkFacts [ (14%nat, mkAF 1 140737488355321 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (37%nat, mkAF 4 140737488355327 0); (38%nat, mkAF 6 140737488355329 0) ] [] [].
Lemma u32_regions_wf : forall m, (m <= 4)%nat -> regions_wf (u32_regs_of m) = true.
Proof.
intros m Hm. destruct m as [|[|[|[|[|m]]]]]; try (exfalso; lia); vm_compute; reflexivity.
Qed.
Lemma u32_inreg_ok : forall E (W : world rsegs) mem c (m : nat) (rest : list byte),
ew E 14 = Z_to_bv 64 (c - 2) ->
(forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
(m <= length rest)%nat -> (m <= 4)%nat -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
garr8 rsegs (mrestrict (w_H W) mem) c (map (fun x : byte => bv_unsigned x) rest) ->
region_ok rsegs E (mrestrict (w_H W) mem) (u32_in_region m).
Proof.
intros E W mem c m rest E14 Eb Hm1 Hm2 Hc0 Hc1 Hg. unfold region_ok, u32_in_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E14, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (Hch : forall i, (i < m)%nat ->
  YP09.chunk_ok rsegs E (mrestrict (w_H W) mem) (c - 2) (YP09.mkChunk (2 + Z.of_nat i) (CVal 1 (SOff (33 + i) 0)))).
{ intros i Hi.
  apply (chunk_ok_val rsegs E (mrestrict (w_H W) mem) (c - 2) (2 + Z.of_nat i) 1 (SOff (33 + i) 0) (u32_b rest i)).
  - cbn [sv_denot]. rewrite (Eb i ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. apply u32_b_range.
  - lia.
  - replace (c - 2 + (2 + Z.of_nat i)) with (c + Z.of_nat i) by lia.
    destruct (Hg i ltac:(rewrite length_map; lia)) as [Hv _]. exact Hv. }
unfold u32_bchunks. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (i & <- & Hi).
apply in_seq in Hi. apply Hch. lia.
Qed.
Lemma u32_entry : forall (regs : bvmap 5 word) (W : world rsegs) memc (c nn left : Z) (m : nat) (rest : list byte)
  a1v a5v G pc,
getr regs 14 = w64 (c - 2) -> getr regs 18 = w64 SHADOW_OFF -> getr regs 25 = w64 c ->
sv_denot (Ereg regs (u32_extra rest left nn)) a1v = getr regs 11 ->
sv_denot (Ereg regs (u32_extra rest left nn)) a5v = getr regs 15 ->
0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
(m <= length rest)%nat -> (m <= 4)%nat ->
garr8 rsegs (mrestrict (w_H W) memc) c (map (fun x : byte => bv_unsigned x) rest) ->
facts_ok (Ereg regs (u32_extra rest left nn)) G -> 0 <= pc ->
st_ok rsegs (Ereg regs (u32_extra rest left nn)) (u32_ss pc a1v a5v m G)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros regs W memc c nn left m rest a1v a5v G pc H14 H18 H25 Ha1 Ha5 Hc0 Hc1 Hm1 Hm2 Hg HG Hpc.
unfold w64 in H14, H18, H25.
set (E := Ereg regs (u32_extra rest left nn)) in *.
assert (E14 : ew E 14 = Z_to_bv 64 (c - 2)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (Eb : forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)).
{ intros i Hi. subst E. destruct i as [|[|[|[|i]]]]; try (exfalso; lia).
  - exact (ew_Ereg_extra regs _ 1). - exact (ew_Ereg_extra regs _ 2).
  - exact (ew_Ereg_extra regs _ 3). - exact (ew_Ereg_extra regs _ 4). }
rewrite restrict_mkst_fx. unfold u32_ss.
assert (HS0 : st_ok rsegs E (mkSS pc sr_atoms (u32_regs_of m) None G)
  (mkst regs (Z_to_bv 64 pc) (mrestrict (w_H W) memc) (seg_rom rsegs))).
{ subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - apply u32_regions_wf. exact Hm2.
  - unfold u32_regs_of; destruct m as [|m']; repeat (apply Forall_cons); try apply Forall_nil.
    apply (u32_inreg_ok _ W memc c (S m') rest E14 Eb Hm1 Hm2 Hc0 Hc1 Hg).
  - unfold u32_regs_of; destruct m as [|m']; cbn [pairwise_disjoint all_disjoint]; tauto.
  - exact HG. }
pose proof (st_ok_pin_sv rsegs E _ _ (25%bv : bv 5) (SOff 14 2) HS0 eq_refl
  ltac:(cbn [ms_regs mkst sv_denot]; rewrite E14, unsigned_lit_small by lia; rewrite H25; f_equal; lia)) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_sv rsegs E _ _ (18%bv : bv 5) (SOff 32 0) HS1 eq_refl
  ltac:(cbn [ms_regs mkst sv_denot]; subst E; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H18))) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pin_sv rsegs E _ _ (11%bv : bv 5) a1v HS2 eq_refl ltac:(cbn [ms_regs mkst]; exact Ha1)) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
pose proof (st_ok_pin_sv rsegs E _ _ (15%bv : bv 5) a5v HS3 eq_refl ltac:(cbn [ms_regs mkst]; exact Ha5)) as HS4.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
exact HS4.
Qed.
End u32e.

Lemma u32_b_zero : forall rest i, (length rest <= i)%nat -> u32_b rest i = 0.
Proof. intros rest i Hi. unfold u32_b. apply nth_overflow. rewrite length_map. exact Hi. Qed.

Section av. Context {fx : YK11.FPState}.
Local Ltac u32_bz := first [lia | (try change (2 ^ 16) with 65536; try change (2 ^ 8) with 256; lia)].
Local Ltac u32_side := try change (2 ^ 16) with 65536; try change (2 ^ 8) with 256;
  first [lia | (vm_compute; reflexivity)].
Lemma u32_val0 : forall E rest, (length rest <= 0)%nat ->
sv_denot E (SLit 0) = Z_to_bv 64 (fst (Cursor.fuzz_u32 rest)).
Proof.
intros E rest Hl. cbn [sv_denot]. f_equal. rewrite fuzz_u32_bytes.
rewrite (u32_b_zero rest 0), (u32_b_zero rest 1), (u32_b_zero rest 2), (u32_b_zero rest 3) by lia. lia.
Qed.
Lemma u32_val1 : forall E rest, (forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
(length rest <= 1)%nat ->
sv_denot E (SAlu ALU_OR (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 33 0))) (SLit 0))
  = Z_to_bv 64 (fst (Cursor.fuzz_u32 rest)).
Proof.
intros E rest Eb Hl. pose proof (u32_b_range rest 0) as Q0.
rewrite denot_lit_U. f_equal.
assert (V0 : U E (SExt false 8 (SOff 33 0)) = u32_b rest 0) by (apply U_zext8; [exact (Eb 0%nat ltac:(lia)) | lia]).
assert (VA : U E (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 33 0))) = u32_b rest 0) by (apply (U_or0l E _ _ V0); lia).
rewrite (U_or0r E _ _ VA) by lia.
rewrite fuzz_u32_bytes. rewrite (u32_b_zero rest 1), (u32_b_zero rest 2), (u32_b_zero rest 3) by lia. lia.
Qed.
Lemma u32_val2 : forall E rest, (forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
(length rest <= 2)%nat ->
sv_denot E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 34 0)) (SLit 8)) (SExt false 8 (SOff 33 0))) (SLit 0))
  = Z_to_bv 64 (fst (Cursor.fuzz_u32 rest)).
Proof.
intros E rest Eb Hl. pose proof (u32_b_range rest 0) as Q0. pose proof (u32_b_range rest 1) as Q1.
rewrite denot_lit_U. f_equal.
assert (V0 : U E (SExt false 8 (SOff 33 0)) = u32_b rest 0) by (apply U_zext8; [exact (Eb 0%nat ltac:(lia)) | lia]).
assert (V1 : U E (SExt false 8 (SOff 34 0)) = u32_b rest 1) by (apply U_zext8; [exact (Eb 1%nat ltac:(lia)) | lia]).
assert (VL : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 34 0)) (SLit 8)) (SExt false 8 (SOff 33 0)))
  = u32_b rest 0 + u32_b rest 1 * 2 ^ 8) by (apply (U_or_sll E _ _ _ _ 8 V1 V0); u32_side).
rewrite (U_or0r E _ _ VL) by u32_bz.
rewrite fuzz_u32_bytes. rewrite (u32_b_zero rest 2), (u32_b_zero rest 3) by lia. change (2 ^ 8) with 256. lia.
Qed.
Lemma u32_val3 : forall E rest, (forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
(length rest <= 3)%nat ->
sv_denot E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 34 0)) (SLit 8)) (SExt false 8 (SOff 33 0)))
  (SAlu ALU_SLL (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 35 0))) (SLit 16)))
  = Z_to_bv 64 (fst (Cursor.fuzz_u32 rest)).
Proof.
intros E rest Eb Hl. pose proof (u32_b_range rest 0) as Q0. pose proof (u32_b_range rest 1) as Q1.
pose proof (u32_b_range rest 2) as Q2.
rewrite denot_lit_U. f_equal.
assert (V0 : U E (SExt false 8 (SOff 33 0)) = u32_b rest 0) by (apply U_zext8; [exact (Eb 0%nat ltac:(lia)) | lia]).
assert (V1 : U E (SExt false 8 (SOff 34 0)) = u32_b rest 1) by (apply U_zext8; [exact (Eb 1%nat ltac:(lia)) | lia]).
assert (V2 : U E (SExt false 8 (SOff 35 0)) = u32_b rest 2) by (apply U_zext8; [exact (Eb 2%nat ltac:(lia)) | lia]).
assert (VL : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 34 0)) (SLit 8)) (SExt false 8 (SOff 33 0)))
  = u32_b rest 0 + u32_b rest 1 * 2 ^ 8) by (apply (U_or_sll E _ _ _ _ 8 V1 V0); u32_side).
assert (VA : U E (SAlu ALU_OR (SLit 0) (SExt false 8 (SOff 35 0))) = u32_b rest 2) by (apply (U_or0l E _ _ V2); lia).
rewrite (U_or_sll_r E _ _ _ _ 16 VA VL) by u32_side.
rewrite fuzz_u32_bytes. rewrite (u32_b_zero rest 3) by lia.
change (2 ^ 8) with 256. change (2 ^ 16) with 65536. lia.
Qed.
Lemma u32_val4 : forall E rest, (forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
sv_denot E (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 34 0)) (SLit 8)) (SExt false 8 (SOff 33 0)))
  (SAlu ALU_SLL (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 36 0)) (SLit 8)) (SExt false 8 (SOff 35 0))) (SLit 16)))
  = Z_to_bv 64 (fst (Cursor.fuzz_u32 rest)).
Proof.
intros E rest Eb. pose proof (u32_b_range rest 0) as Q0. pose proof (u32_b_range rest 1) as Q1.
pose proof (u32_b_range rest 2) as Q2. pose proof (u32_b_range rest 3) as Q3.
rewrite denot_lit_U. f_equal.
assert (V0 : U E (SExt false 8 (SOff 33 0)) = u32_b rest 0) by (apply U_zext8; [exact (Eb 0%nat ltac:(lia)) | lia]).
assert (V1 : U E (SExt false 8 (SOff 34 0)) = u32_b rest 1) by (apply U_zext8; [exact (Eb 1%nat ltac:(lia)) | lia]).
assert (V2 : U E (SExt false 8 (SOff 35 0)) = u32_b rest 2) by (apply U_zext8; [exact (Eb 2%nat ltac:(lia)) | lia]).
assert (V3 : U E (SExt false 8 (SOff 36 0)) = u32_b rest 3) by (apply U_zext8; [exact (Eb 3%nat ltac:(lia)) | lia]).
assert (VL : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 34 0)) (SLit 8)) (SExt false 8 (SOff 33 0)))
  = u32_b rest 0 + u32_b rest 1 * 2 ^ 8) by (apply (U_or_sll E _ _ _ _ 8 V1 V0); u32_side).
assert (VH : U E (SAlu ALU_OR (SAlu ALU_SLL (SExt false 8 (SOff 36 0)) (SLit 8)) (SExt false 8 (SOff 35 0)))
  = u32_b rest 2 + u32_b rest 3 * 2 ^ 8) by (apply (U_or_sll E _ _ _ _ 8 V3 V2); u32_side).
rewrite (U_or_sll_r E _ _ _ _ 16 VH VL) by u32_side.
rewrite fuzz_u32_bytes. change (2 ^ 8) with 256. change (2 ^ 16) with 65536. lia.
Qed.
End av.

Lemma shadow_off_range : 0 <= SHADOW_OFF < 2 ^ 64.
Proof. split; (vm_compute; first [discriminate | reflexivity]). Qed.

Section u32f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma u32_facts0_ok : forall regs rest left nn c m,
getr regs 14 = Z_to_bv 64 (c - 2) -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 -> length rest = m ->
facts_ok (Ereg regs (u32_extra rest left nn)) (u32_facts0 m).
Proof.
intros regs rest left nn c m H14 Hc0 Hc1 Hm. subst m.
assert (E14 : ew (Ereg regs (u32_extra rest left nn)) 14 = Z_to_bv 64 (c - 2))
  by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
pose proof shadow_off_range as Hso.
pose proof (Nat2Z.is_nonneg (length rest)) as Hl0.
split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok u32_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E14, E32, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
Lemma u32_factsF_ok : forall regs rest left nn c,
getr regs 14 = Z_to_bv 64 (c - 2) -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
4 <= left -> nn = left + 2 -> left = Z.of_nat (length rest) ->
facts_ok (Ereg regs (u32_extra rest left nn)) u32_factsF.
Proof.
intros regs rest left nn c H14 Hc0 Hc1 Hl4 Hnn Hleft.
assert (E14 : ew (Ereg regs (u32_extra rest left nn)) 14 = Z_to_bv 64 (c - 2))
  by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
assert (E37 : ew (Ereg regs (u32_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5).
assert (E38 : ew (Ereg regs (u32_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6).
pose proof shadow_off_range as Hso.
split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok u32_factsF]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E14, E32, E37, E38, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
End u32f.

Ltac u32_sv HSx :=
  lazymatch goal with |- getr _ _ = _ => rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HSx) | _ => idtac end;
  match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
Ltac u32_obl E32x E14x Hrax :=
  try unfold ob_holds; try unfold U32Bx; try cbn [ob_x ob_n];
  rewrite (U_atom _ 32 SHADOW_OFF E32x shadow_off_range);
  first [ rewrite (U_atom_off _ 14 _ 2 E14x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 14 _ 3 E14x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 14 _ 4 E14x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 14 _ 5 E14x ltac:(lia) ltac:(lia)) ];
  eapply ra_sub; [exact Hrax | lia | lia].
Ltac u32_leaf regs0 extra0 E32x H18x valtac :=
lazymatch goal with
| HS : st_ok _ ?Ex ?ssf (restrict (w_H ?Wx) ?msx),
  HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lycx ?Scx _ _ _ _,
  HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  apply SRr_ret;
  red; exists lycx, Scx, (ms_regs msx), (ms_mem msx); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H Wx) Ex ssf msx HS eq_refl) at 1; reflexivity|];
  split; [exact HJx|];
  split; [eapply (regs_kept_of_st_ok_pins rsegs Ex ssf msx regs0 extra0 (w_H Wx) _
                   [((18%bv : bv 5), SOff 32 0)] HS);
          [ split; [intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]
          | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
            cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
            rewrite E32x, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H18x)
          | vm_compute; reflexivity ]|];
  split; [reflexivity|];
  split; [apply Permutation_refl|];
  split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
  split; [apply mo_le_refl; assumption|];
  split;
  [ intros a; unfold aview, mbyte; rewrite (HFrx (Z_to_bv 64 a)); [reflexivity|];
    intros (rg & Hin & Hr); cbn [In] in Hin;
    repeat (destruct Hin as [<-|Hin]; [cbn in Hr; lia|]); destruct Hin
  | valtac ]
end.

(* the code of the two sites: [0x816d8, 0x81de4) (both first reads, both joins, the second reads), [0x82044,
   0x820dc) (the third and fourth reads) and the slow blocks [0x82220, 0x82280) of their shadow checks *)
Definition u32_tbl : ctable :=
  build_table rsegs 0x82220 24 (build_table rsegs 0x82044 38 (build_table rsegs 0x816d8 451 TEmpty)).
Lemma u32_tbl_ok : table_ok rsegs u32_tbl.
Proof. apply build_table_ok; [lia | apply build_table_ok; [lia | apply build_table_ok0; lia]]. Qed.

(* ---- one arm of a site: m bytes read (m = n1 < 4, or 4 when n1 >= 4) ---- *)
Ltac u32_run_arm pcB E32 E14 H18 Hra regs extra valtac :=
  lazymatch goal with HS : st_ok _ ?Ex _ (restrict (w_H ?Wx) (mkst _ _ ?mc _)),
                      HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  assert (SHOK : sh_ok rsegs U32Bx [] Ex (mrestrict (w_H Wx) mc)) by constructor;
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span pcB;
    try solve [u32_obl E32 E14 Hra]; try solve [awr_ok_tac];
    u32_leaf regs extra E32 H18 valtac end.

(* ---- the two sites, each with its five length arms ---- *)
Section u32b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Definition rts_u32_stmt (pcA pcB : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (c left nn : Z) (rest : list byte),
left = Z.of_nat (length rest) -> nn = left + 2 ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 11 = w64 left -> getr regs 14 = w64 (c - 2) -> getr regs 15 = w64 nn ->
getr regs 18 = w64 SHADOW_OFF -> getr regs 25 = w64 c ->
0 < c - 2 -> c + left <= 140737488355327 ->
garr8 rsegs (mrestrict (w_H W) memc) c (map (fun x : byte => bv_unsigned x) rest) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c left ->
SRr rsegs W (cfg_at rsegs pcA regs memc mdc)
 (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcB
   [11; 12; 13; 14; 15; 16; 17; 25]%bv
   (fun regs2 => getr regs2 12 = w64 (fst (Cursor.fuzz_u32 rest)) /\
                 getr regs2 11 = w64 (Z.of_nat (length rest - 4)) /\
                 getr regs2 25 = w64 (c + Z.of_nat (Nat.min 4 (length rest))) /\
                 getr regs2 18 = w64 SHADOW_OFF)).

(* the whole proof of one site, from its start pc pcA to its end pc pcB *)
Local Ltac u32_site pcA pcB :=
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c left nn rest
  Hleft Hnn HJ H11 H14 H15 H18 H25 Hc0 Hc1 Hg Hra;
pose proof rts_wx as Hwx; pose proof rts_segs_low as Hsegs;
pose proof shadow_off_range as Hso; pose proof (Nat2Z.is_nonneg (length rest)) as Hl0;
unfold w64 in H11, H14, H15, H18, H25;
unfold cfg_at; change (w64 pcA) with (Z_to_bv 64 pcA);
destruct (Z_le_gt_dec 4 left) as [HF|Hsm];
[ (* 4 or more bytes left *)
  assert (HlenF : (4 <= length rest)%nat) by lia;
  assert (E14 : ew (Ereg regs (u32_extra rest left nn)) 14 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14);
  assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0);
  assert (E37 : ew (Ereg regs (u32_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5);
  assert (E38 : ew (Ereg regs (u32_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6);
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest left nn)) (33 + i) = Z_to_bv 64 (u32_b rest i))
  by (intros i Hi; destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
      [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
      | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]);
  pose proof (u32_entry regs W memc c nn left 4%nat rest (SOff 37 0) (SOff 38 0) u32_factsF pcA
    H14 H18 H25
    ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H11))
    ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H15))
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_factsF_ok regs rest left nn c H14 Hc0 ltac:(lia) ltac:(lia) Hnn Hleft) ltac:(lia)) as HS;
  u32_run_arm pcB E32 E14 H18 Hra regs (u32_extra rest left nn)
    ltac:(split; [u32_sv HS; apply (u32_val4 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)))
          | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                    rewrite E38, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                    rewrite E14, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
            rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]])
| (* 0 .. 3 bytes left: each a literal *)
  assert (Hcases : left = 0 \/ left = 1 \/ left = 2 \/ left = 3) by lia;
  destruct Hcases as [Hcase|[Hcase|[Hcase|Hcase]]];
  [ assert (HlenK : length rest = 0%nat) by lia
  | assert (HlenK : length rest = 1%nat) by lia
  | assert (HlenK : length rest = 2%nat) by lia
  | assert (HlenK : length rest = 3%nat) by lia ];
  clear Hleft; subst left; subst nn;
  lazymatch goal with HK : length rest = ?mm |- _ =>
  lazymatch type of H11 with getr _ _ = Z_to_bv 64 ?lv =>
  assert (E14 : ew (Ereg regs (u32_extra rest lv (lv + 2))) 14 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14);
  assert (E32 : ew (Ereg regs (u32_extra rest lv (lv + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0);
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest lv (lv + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i))
  by (intros i Hi; destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
      [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
      | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]);
  pose proof (u32_entry regs W memc c (lv + 2) lv mm rest (SLit lv) (SLit (lv + 2)) (u32_facts0 mm) pcA
    H14 H18 H25
    ltac:(cbn [sv_denot]; rewrite H11; reflexivity) ltac:(cbn [sv_denot]; rewrite H15; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest lv (lv + 2) c mm H14 Hc0 ltac:(lia) HK) ltac:(lia)) as HS;
  u32_run_arm pcB E32 E14 H18 Hra regs (u32_extra rest lv (lv + 2))
    ltac:(split; [u32_sv HS;
                  first [ apply (u32_val0 _ rest ltac:(lia))
                        | apply (u32_val1 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
                        | apply (u32_val2 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
                        | apply (u32_val3 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia)) ]
          | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
          | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                    rewrite E14, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
            rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]])
  end end ].

Lemma rts_u32_block2 : rts_u32_stmt 0x816d8 0x81d94.
Proof using MTL LAWS. u32_site 0x816d8 0x81d94. Qed.
Lemma rts_u32_block3 : rts_u32_stmt 0x81c0c 0x81de4.
Proof using MTL LAWS. u32_site 0x81c0c 0x81de4. Qed.
End d2.
End u32b.

(* ============================== PART 3. chaining blocks, the memset / memcpy call, the frame ==============================
   (a) rts_post: the post of a block that writes memory (rts_blk_post with every byte outside Wr kept instead of
       every byte, and R reading the world and memory too); rts_post_of_blk, rts_post_seq, rts_blk_seq chain two
       blocks into one with SRr_bind (the union of the clobbered registers and of the write sets).
   (b) the call adapter of the two intrinsics (__asan_memset 0x51cfc, __asan_memcpy 0x51860; the walk's 7 memset and
       10 memcpy calls): rts_intrin_at is the kernel's aintrin_realizes (YG0d.v) carried under the caller's journal
       (YCbq aj_intrin_at, also keeping the callee's same_but_materialized); rts_intrin_seq chains it after a block
       that stops at the callee's entry with ra = the return pc, so a walk lane gets the call as one more block. The
       allocator's calls (malloc 0x52bb4, free 0x52bb0) need no adapter here: the kernel's own YCbq aj_malloc_at04 /
       aj_free_at are the journal-level adapters (with rts_segs_low for their segs_low).
   (c) the frame for locals F (class 3, 512 bytes, F mod 32 = 0 by AR_frames_law): its bounds and the shadow address
       of an object at F + o. *)
Section c3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d3.
Variable B : asyms.
Variable MT : ameter_ops.
Definition rts_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(clob : list (bv 5)) (Wr : Z -> Prop) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.

Section seq.
Hypothesis MTL : ameter_laws MT.
Lemma rts_post_of_blk : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob
(Rr : bvmap 5 word -> Prop) (Wr : Z -> Prop) W2 c2,
rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr W2 c2 ->
rts_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr (fun _ regs2 _ => Rr regs2) W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr Wr W2 c2
(ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. repeat (split; [eassumption|]).
split; [intros a _ _; apply Hm|]. exact HR.
Qed.
Lemma rts_post_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(Wr1 Wr2 : Z -> Prop) (R1 R2 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rts_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 Wr1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr1 a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 W1 regs1 mem1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (rts_post STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 Wr2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rts_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) (fun a => Wr1 a \/ Wr2 a) R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2 Wr1 Wr2 R1 R2 H1 H2.
eapply SRr_bind; [exact H1|].
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
eapply SRr_mono; [exact (H2 W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]|].
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split; [intros a Ha Hn; rewrite (Hm2 a Ha ltac:(intros X; apply Hn; right; exact X));
  exact (Hm1 a Ha ltac:(intros X; apply Hn; left; exact X))|].
exact HR2.
Qed.
Lemma rts_blk_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(R1 R2 : bvmap 5 word -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 regs1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rts_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) R2).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2 R1 R2 H1 H2.
eapply SRr_bind; [exact H1|].
intros W1 c1 Hw1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
eapply SRr_mono; [exact (H2 W1 ly1 S1 regs1 mem1 md1 Hw1 HJ1 Hr1 Hf1 Hp1 Hio1 Hmo1 Hm1 HR1)|].
intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|].
split; [intros r Hr0 Hn; rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X));
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]|].
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split; [intros a; rewrite (Hm2 a); exact (Hm1 a)|].
exact HR2.
Qed.
End seq.

(* ---- small facts every block proof uses ---- *)
(* the registers a call may change (everything but YG0d.acallee_saved and x0) *)
Definition rts_caller_saved : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Lemma rts_callee : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rts_caller_saved -> acallee_saved (bv_unsigned r).
Proof.
intros r H0 Hn. pose proof (in_nz_regs r H0) as Hin. cbv [nz_regs In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ first
  [ (lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia)
  | (exfalso; apply Hn; cbv [rts_caller_saved In]; repeat (first [left; apply bv_eq; reflexivity | right])) ]
| ]).
destruct Hin.
Qed.
(* a register the state holds as its own atom *)
Lemma rts_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r. rewrite !unsigned_lit_small by exact Hv.
apply zcanon_id. unfold M64. lia.
Qed.
(* an aview value kept, as a val_mem *)
Lemma rts_val_kept : forall H (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview rsegs H m' (a + k) = aview rsegs H m (a + k)) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv. exact (val_mem_kept rsegs H H m m' a n v Hk Hv). Qed.
(* a one-byte chunk of value 0 *)
Lemma rts_chunk0 : forall E H mem base o,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 0))) -> aview rsegs H mem (base + o) = Some 0.
Proof.
intros E H mem base o Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
first [reflexivity | (vm_compute; reflexivity)].
Qed.
(* a region of a run's state, and its chunks *)
Lemma rts_region_nth : forall E ss ms i r (H : word -> bool),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros E ss ms i r H HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma rts_chunks : forall E m n b cs lo hi wlo whi,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
forall c, In c cs -> YP09.chunk_ok rsegs E m b c.
Proof.
intros E m n b cs lo hi wlo whi (_ & _ & _ & Hcs) Hn c Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck. exact Hck.
Qed.

(* ---- (b) the memset / memcpy call ---- *)
Section intr.
Hypothesis LAWS : AR_laws rsegs B.
(* YCbq aj_intrin_at, also keeping the callee's same_but_materialized (for same_io) *)
Lemma rts_intrin_at : forall op pc, aintrin_realizes rsegs B op pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
(match op with
| OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok rsegs W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) x n)
| OSet => True end) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) =
 match op with OCpy => aview rsegs (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a)).
Proof using LAWS.
intros op pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull Hsrc.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption. rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  assert (Hpa : apresent (w_H W) memT a /\ ~ aowned B lyc Sc a) by (eapply awr_byte_present; eassumption).
  destruct Hpa as [Hp Hno]. rewrite Hsp'.
  split; [apply (apresent_writable rsegs); exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d x n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS rts_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Heff | exact Hfr].
Qed.

(* a block that stops at the intrinsic's entry pcI with ra = retpc, then the call: one block to retpc. Its R
   keeps the first block's R at the memory before the call (mem1), what the call wrote, and the bytes it kept. *)
Lemma rts_intrin_seq : forall op pcI retpc, aintrin_realizes rsegs B op pcI ->
forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob (Wr : Z -> Prop)
  (R1 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) d x n o,
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rts_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pcI clob Wr R1) ->
(forall ly1 S1 W1 regs1 mem1 md1,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k -> R1 W1 regs1 mem1 ->
  getr regs1 10 = w64 d /\ getr regs1 11 = w64 x /\ getr regs1 12 = w64 n /\ spZ regs1 = sp0 + o /\
  getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\ getr regs1 1 = w64 retpc /\
  (forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own a /\
   ~ (sp0 + o - ESTACK <= a < sp0 + o)) /\
  range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF d n /\
  (0 < n -> shadow_hull_vis (aview rsegs (w_H W1) mem1) d n) /\
  (match op with
   | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok rsegs W1 regs1 mem1 x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
     range_addressable (aview rsegs (w_H W1) mem1) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview rsegs (w_H W1) mem1) x n)
   | OSet => True end)) ->
0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 -> amem_range d n ->
o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK -> YK0s.ret_ok (w64 retpc) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rts_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc (clob ++ rts_caller_saved)
    (fun a => Wr a \/ (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o))
    (fun W2 regs2 mem2 => exists regs1 mem1, R1 W2 regs1 mem1 /\
       (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) /\
       getr regs2 10 = w64 d /\
       (forall i, 0 <= i < n -> aview rsegs (w_H W2) mem2 (d + i) =
        match op with OCpy => aview rsegs (w_H W2) mem1 (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
        aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem1 a))).
Proof using LAWS.
intros op pcI retpc AI STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob Wr R1 d x n o
  H1 Hpre Hn Hd0 Hdn Hamr Hal Hneg Hbud Hret.
eapply SRr_bind; [exact H1|].
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
destruct (Hpre ly1 S1 W1 regs1 mem1 md1 HJ1 HR1)
  as (Ha0 & Ha1 & Ha2 & Hsp & Hgp & Htp & Hra & Hdest & Hrad & Hhull & Hsrc).
eapply SRr_mono.
{ exact (rts_intrin_at op pcI AI W1 regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k d x n o (w64 retpc)
    HJ1 Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp Hal Hneg Hbud Hgp Htp Hra Hret Hdest Hamr Hrad Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsame & H10 & Heff & Hfr).
exists ly1, S1, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros r Hr0 Hn'. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  rewrite (HP (bv_unsigned r) (rts_callee r Hr0 ltac:(intros X; apply Hn'; apply in_or_app; right; exact X))).
  rewrite Z_to_bv_bv_unsigned. apply Hr1; [exact Hr0 | intros X; apply Hn'; apply in_or_app; left; exact X]. }
split; [exact Hf1|]. split; [exact Hp1|].
split; [eapply same_io_trans; [exact Hio1 | apply same_io_materialized; exact Hsame]|].
split; [exact Hmo1|].
split.
{ intros a Ha Hn'. rewrite (Hfr a Ha ltac:(intros X; apply Hn'; right; left; exact X) ltac:(intros X; apply Hn'; right; right; exact X)).
  apply Hm1; [exact Ha | intros X; apply Hn'; left; exact X]. }
exists regs1, mem1. split; [exact HR1|].
split; [exact HP|]. split; [exact H10|]. split; [exact Heff | exact Hfr].
Qed.
End intr.
End d3.
End c3.

(* ---- (c) the frame for locals: a class-3 side-stack frame F (512 bytes), F mod 32 = 0 ---- *)
Lemma rts_fdiv : forall F, F mod 32 = 0 -> F = 32 * (F / 32) /\ shadow_addr F = SHADOW_OFF + 4 * (F / 32).
Proof.
intros F H. pose proof (Z.div_mod F 32 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
split; [exact E|]. unfold shadow_addr. f_equal. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E.
replace (32 * q) with ((4 * q) * 8) by ring. apply Z.div_mul. lia.
Qed.
(* the shadow address of an object at F + o is F's plus o / 8 *)
Lemma rts_fsh_addr : forall F o, F mod 32 = 0 -> 0 <= o -> shadow_addr (F + o) = shadow_addr F + o / 8.
Proof.
intros F o H Ho. destruct (rts_fdiv F H) as [E1 E2]. rewrite E2. unfold shadow_addr.
remember (F / 32) as q eqn:Hq. clear Hq. rewrite E1.
replace (32 * q + o) with (o + (4 * q) * 8) by ring. rewrite Z.div_add by lia. ring.
Qed.
(* the same, as the instrumented check computes it *)
Lemma rts_fsh_of : forall F o, F mod 32 = 0 -> 0 <= o -> shadow_of_addr SHADOW_OFF (F + o) = shadow_addr F + o / 8.
Proof. intros F o H Ho. rewrite <- (rts_fsh_addr F o H Ho). reflexivity. Qed.
Lemma rts_fmod8 : forall F j, F mod 32 = 0 -> (F + 8 * j) mod 8 = 0.
Proof.
intros F j H. destruct (rts_fdiv F H) as [E1 _]. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E1.
replace (32 * q + 8 * j) with ((4 * q + j) * 8) by ring. apply Z_mod_mult.
Qed.
(* the frame of an in_app address F: its bounds, its shadow below the ceiling and apart from F, every object
   range in it inside the low or high application memory *)
Lemma rts_fbounds : forall {rc : YM05.RunCeil} F, F mod 32 = 0 -> in_app F 512 ->
4096 <= F /\ F + 512 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 64 <= alloc_ceiling /\
(F + 512 <= shadow_addr F \/ shadow_addr F + 64 <= F) /\
(forall o n, 0 <= o -> 0 <= n -> o + n < 512 -> amem_range (F + o) n).
Proof.
intros rc F Hm Ha. destruct (rts_fdiv F Hm) as [E1 E2]. pose proof asan_consts as (C1 & _). rewrite E2.
remember (F / 32) as q eqn:Hq. clear Hq.
unfold in_app, amem_range, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros o n Ho Hn Hon. lia.
Qed.

(* ---- (d) the write rights of a block (YCbq awr_byte / awr_ok) at the places the walk writes: the frame for
   locals' objects (memset / memcpy into t, ch, e; stores into r, hz, asked), its 64 shadow bytes (the 15
   scope-store sites: e / t / ch / r / hz / asked in and out of scope), and the real frame's cells (the
   journal's stack window). Each rts_awr_ok_* puts one region of the run's symbolic state on the list awr_ok_tac
   would need, from the register atom that is its base. ---- *)
Lemma rts_awr_fobj : forall STK sp0 FP bl0 blc ly own pos a,
In (3, pos) own -> frame_addr ly 3 pos <= a < frame_addr ly 3 pos + 512 -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right; right; right. exists 3, pos. split; [exact Hown|]. left.
unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rts_awr_fsh : forall STK sp0 FP bl0 blc ly own pos a,
In (3, pos) own -> shadow_addr (frame_addr ly 3 pos) <= a < shadow_addr (frame_addr ly 3 pos) + 64 ->
awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right; right; right. exists 3, pos. split; [exact Hown|]. right.
unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 3 / 8) with 64. lia.
Qed.
Lemma rts_awr_stk : forall STK sp0 FP bl0 blc ly own a, sp0 - STK <= a < sp0 -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof. intros STK sp0 FP bl0 blc ly own a Ha. left. exact Ha. Qed.
Lemma rts_awr_ok_fsh : forall E r rs STK sp0 FP bl0 blc ly own (kreg : nat) pos,
YP09.r_base r = Some kreg -> bv_unsigned (ew E kreg) = shadow_addr (frame_addr ly 3 pos) -> In (3, pos) own ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= 64 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own kreg pos Hb Hk Hown Hlo Hhi Hrs.
apply (awr_ok_cons_gen E r rs STK sp0 FP bl0 blc ly own kreg _ Hb Hk); [|exact Hrs].
intros a Ha. apply (rts_awr_fsh STK sp0 FP bl0 blc ly own pos a Hown). lia.
Qed.
Lemma rts_awr_ok_fobj : forall E r rs STK sp0 FP bl0 blc ly own (kreg : nat) pos off,
YP09.r_base r = Some kreg -> bv_unsigned (ew E kreg) = frame_addr ly 3 pos + off -> In (3, pos) own ->
0 <= off + YP09.r_wlo r -> off + YP09.r_whi r <= 512 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own kreg pos off Hb Hk Hown Hlo Hhi Hrs.
apply (awr_ok_cons_gen E r rs STK sp0 FP bl0 blc ly own kreg _ Hb Hk); [|exact Hrs].
intros a Ha. apply (rts_awr_fobj STK sp0 FP bl0 blc ly own pos a Hown). lia.
Qed.

(* ---- (e) the call of any leaf runtime routine whose contract has the kernel's ecall form (the strlen and strcmp
   wrappers 0x42194 / 0x4219c, the bcmp wrapper, the intrinsics): from the caller's state at the routine's entry,
   the routine returns to ra with the runtime invariant AR at the same layout and state, the callee-saved
   registers kept, same_but_materialized, a result Q, and every byte outside its own writes Wd and its stack
   window [sp - T, sp) kept (the strlen wrapper's post, YG0d's aintrin / abcmp posts; T = ESTACK or 2 * ESTACK). rts_ecall_at
   carries that post under the caller's journal; rts_ecall_seq chains it after a block, as rts_intrin_seq does.
   A walk lane gets the routine's SRr from its contract hypothesis (e.g. the strlen wrapper's astrlen_realizes at
   0x42194, lib/A/Rt/StrlenDef.v), applied at the state the first block ends in, through SRr_mono into the shape
   below. ---- *)
Section c4. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d4.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.
Definition rts_ecall_post (lyc : alayout) (Sc : astate) (W : world rsegs) (regsT : bvmap 5 word)
(memT : word -> option byte) (mdc : Model) (T : Z) (Wd : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs (raZ regsT) regs2 mem2 md2 /\
AR rsegs B lyc Sc W mem2 md2 /\ aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ Q regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> ~ (spZ regsT - T <= a < spZ regsT) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
(* the caller's stack window gives the routine's: its bottom above the stack's lowest address, every byte present *)
Lemma rts_stk_window : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc (o T : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o <= 0 -> T - o <= STK ->
ly_stk_lo lyc + T <= spZ regsc /\ (forall a, spZ regsc - T <= a < spZ regsc -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc o T HJ Hsp Hneg Hbud.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _ & HQT).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
split; [rewrite Eslo, Hsp; lia|].
intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
Qed.
Lemma rts_ecall_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o T : Z) raw
  (Wd : Z -> Prop) (Q : bvmap 5 word -> (word -> option byte) -> Prop) pc,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o <= 0 -> T - o <= STK -> getr regsT 1 = raw ->
(forall a, Wd a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc) (rts_ecall_post lyc Sc W regsT memT mdc T Wd Q) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ Q regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> ~ (sp0 + o - T <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a)).
Proof using LAWS.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o T raw Wd Q pc HJ Hsp Hneg Hbud Hra HWd HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2).
rewrite Hsp in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS rts_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => Wd a \/ (sp0 + o - T <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (HWd a Ha) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hsame|]. split; [exact HQ | exact Hfr].
Qed.
(* a block that stops at the routine's entry pcC with ra = retpc, then the call: one block to retpc *)
Lemma rts_ecall_seq : forall pcC retpc STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob (Wr : Z -> Prop)
  (R1 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) (o T : Z) (Wd : Z -> Prop)
  (Q : bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pcC clob Wr R1) ->
(forall ly1 S1 W1 regs1 mem1 md1,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k -> R1 W1 regs1 mem1 ->
  spZ regs1 = sp0 + o /\ getr regs1 1 = w64 retpc /\
  (forall a, Wd a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own a) /\
  SRr rsegs W1 (cfg_at rsegs pcC regs1 mem1 md1) (rts_ecall_post ly1 S1 W1 regs1 mem1 md1 T Wd Q)) ->
o <= 0 -> T - o <= STK ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rts_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc (clob ++ rts_caller_saved)
    (fun a => Wr a \/ Wd a \/ (sp0 + o - T <= a < sp0 + o))
    (fun W2 regs2 mem2 => exists regs1 mem1, R1 W2 regs1 mem1 /\
       (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) /\
       Q regs2 mem2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> ~ (sp0 + o - T <= a < sp0 + o) ->
        aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W2) mem1 a))).
Proof using LAWS.
intros pcC retpc STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob Wr R1 o T Wd Q H1 Hpre Hneg Hbud.
eapply SRr_bind; [exact H1|].
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
destruct (Hpre ly1 S1 W1 regs1 mem1 md1 HJ1 HR1) as (Hsp & Hra & HWd & HC).
eapply SRr_mono.
{ exact (rts_ecall_at W1 regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k o T (w64 retpc) Wd Q pcC
    HJ1 Hsp Hneg Hbud Hra HWd HC). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsame & HQ & Hfr).
exists ly1, S1, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros r Hr0 Hn'. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  rewrite (HP (bv_unsigned r) (rts_callee r Hr0 ltac:(intros X; apply Hn'; apply in_or_app; right; exact X))).
  rewrite Z_to_bv_bv_unsigned. apply Hr1; [exact Hr0 | intros X; apply Hn'; apply in_or_app; left; exact X]. }
split; [exact Hf1|]. split; [exact Hp1|].
split; [eapply same_io_trans; [exact Hio1 | apply same_io_materialized; exact Hsame]|].
split; [exact Hmo1|].
split.
{ intros a Ha Hn'. rewrite (Hfr a Ha ltac:(intros X; apply Hn'; right; left; exact X) ltac:(intros X; apply Hn'; right; right; exact X)).
  apply Hm1; [exact Ha | intros X; apply Hn'; left; exact X]. }
exists regs1, mem1. split; [exact HR1|].
split; [exact HP|]. split; [exact HQ | exact Hfr].
Qed.
End d4.
End c4.

Print Assumptions rts_ecall_seq.
Print Assumptions rts_stk_window.
Print Assumptions rts_awr_ok_fsh.
Print Assumptions rts_awr_ok_fobj.
Print Assumptions rts_intrin_seq.
Print Assumptions rts_post_seq.
Print Assumptions rts_blk_seq.
Print Assumptions rts_fbounds.

Print Assumptions rts_jt_block.
Print Assumptions rts_u32_block2.
Print Assumptions rts_u32_block3.
