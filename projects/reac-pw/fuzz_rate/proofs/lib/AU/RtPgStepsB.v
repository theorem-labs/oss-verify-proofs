(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b01 (its code table, wx / segs_low lemmas, save-slot region, ck_sr / ck_facts / regs_ok_override / ck_regs_ok / ck_lit / ck_atom, the entry-state lemma, same_io_wvb_ck, ck_kept_run and the run / keep / leaf tactics) and proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at 5afd8b87436 (pa_i_memset_at, pa_i_regs_kept, pa_i_region_nth, pa_i_field, pa_i_soff, pa_i_cs / pa_i_notin / pa_i_pres and the reg / region tactics) for reac-pw/fuzz_rate's image B (fuzz_rate.asan-ubsan): the image is AsanUbsan, the table is pod_write_ent's 194 words, the frame is 48 bytes, the intrinsic lemma is stated for both memory operations, and the read-only extents are image B's GOT slot and shadow-offset cell. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/AU/PweKit.v; 1663 of its 1755 lines of code are new or changed and 176 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSteps.v at 6bdf633122fe for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; the jump
   table's site, table and targets and the fuzz_u32 sites are rate's (their registers: the cursor in s9, the shadow
   offset in s2, the original byte count in a5 / a7, no frame cell); the prefix rl_ becomes rts_; the image facts
   wx_segs_nowrap / segs-low and same_io_wvb are stated here instead of taken from a cfg walk file; the block-chaining
   lemmas and helpers (from proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v and RPgW6aHead.v at ef33766f272a), the
   intrinsic call adapter (RPgW6aHead.v w6h_intrin, for both OSet and OCpy), the generic ecall adapter, the class-3
   frame arithmetic and the frame write rights are added. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgSteps.v at 43406476cb20 for the same unit's
   image B (fuzz_rate.asan-ubsan): the image is images.AsanUbsan; every pc, table and literal is image B's (the jump
   table 0x20f6c at 0x8143c with the kind byte in a3, the fuzz_u32 sites, the intrinsic and wrapper entries); the
   frame is class 4 (1024 bytes, 128 shadow bytes) instead of class 3; the prefix rts_ becomes rtsb_, and the
   image-specific unprefixed helpers take a jtb_ / u32b_ prefix; PART 2a (the trap-step lemmas of the 91 UBSan trap
   branches, the 8 shapes) and PART 5 (the pod_write_ent call adapter and its three site-premise lemmas) are new. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address below is measured on its unstripped
   twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded bytes are the same): the
   step kit of the image-B walk of LLVMFuzzerTestOneInput (0x8076c, 2939 instructions). Proves no function (kind:
   segment lemma): each lemma is a step or a block of steps the walk lanes of E01 / M01 / M02 / M03 / X01 use, stated
   over the kit's engine (lib/Reusable: st_ok, sh_ok, ajournal, SRr) and image B's segments (images.AsanUbsan
   loaded_segments).
   PART 1 the jump table (rtsb_jt_block); PART 2 the trap-step lemmas; PART 3 the fuzz_u32 read-ahead; PART 4
   chaining, the memset / memcpy call, any leaf runtime call in the ecall form, the class-4 frame and its write
   rights; PART 5 the pod_write_ent call adapter.
   The inline steps (put32's two checks and four stores, the pp->len check and update, fuzz_u8's check and load,
   the scope stores) are single engine steps of a walk lane's own run: the token engine (YCbn) covers their
   checks, and RtPgMemB's byte / shadow lemmas read the result.

   PART 1. THE JUMP TABLE OF ent_build (pod.h:281, `switch (kind % 10)`), the one computed jump of the function:
     0x81438  bltu a2,a1 -> 0x81a94      a2 = 8: k = kind % 10 = 9 goes to case 9 without the table
     0x8143c  slli a1,a1,2
     0x81440  auipc a2,0xfffa0 / 0x81444 addi a2,a2,-1236     a2 = 0x20f6c, the table (.rodata, read-only)
     0x81448  add a1,a1,a2 / 0x8144c lw a1,0(a1)              the entry of k (a 32-bit offset from the table)
     0x81450  slli a0,a0,0x38 / 0x81458 srai a3,a0,0x38       a3 = the kind byte, sign-extended
     0x81454  add a1,a1,a2
     0x8145c  jr a1                                            to 0x20f6c + entry k
   The nine entries, read from the image (PT_LOAD R [0x10000, 0x2fa0c)), give the targets 0x81460 (case 0) 0x81900 (1)
   0x817c4 (2) 0x81838 (3) 0x81774 (4) 0x81968 (5) 0x819a0 (6) 0x81888 (7) 0x819f0 (8). The case order is not image
   A's. The `lw` carries no instrumented check. The engine (YP0l sym_step) follows `jr` when the register is a literal
   and loads a literal from an image chunk (YP09 CImg) of a base-free region at a literal address. So the step is: the
   table as the read-only region jtb_region (one CImg chunk of 36 bytes), proved from rom_view (jtb_region_ok); k
   split into its nine values (jtb_cases); the register of k pinned to the literal. rtsb_jt_block is that step at the
   concrete site, as a block lemma in the shape of a callee contract (rtsb_blk_post): from 0x8143c with a1 = k,
   0 <= k <= 8, to 0x20f6c + entry k with a1, a2, a0, a3 set and every other register, the journal and every byte as
   before.

   PART 2. THE TRAP STEPS (91 branches to the `unimp` at 0x83098; the `unimp` 0x83094, after `jal abort`, is never
   reached). Image B is built with UBSan as well as ASan, so every pointer sum, every array index and the one division
   of the function carries a test whose other arm is that `unimp`. The engine decides a branch by itself when the
   facts of its symbolic state settle the compare (YP0m decide_cond / YP0e decide_cond2: first cond_assumed over
   f_conds, then the interval arithmetic of sv_range over f_atoms); so a walk lane that carries the right atom range
   or condition fact steps over a trap branch with no lemma at all. Where a lane has only the Z-level fact, PART 2a
   turns it into the branch's bv value, which st_ok_add_cond then puts into the state as a cond fact (the arm the
   engine must take), and PART 2b shows two real sites run end to end.
   The eight shapes (one lemma each; the `unimp` arm of the other branch form follows by branch_taken_neg):
     T1 (37 sites) `addi t,c,1; bltu one,t -> on` or `bgeu one,t -> trap`  rtb_po1      (0 < c, c + 1 < 2^64)
     T2 (10)       `not t,b; bgeu t,o -> on`                               rtb_not_le   (b + o < 2^64)
     T3 (21)       `ld t,(R+c); bgeu t,o -> on` with the cell = ~x         rtb_not_le   (x + o < 2^64)
     T4 (12)       `bltu i,16385 -> on`, `srli t,i,14; bnez t -> trap`     rtb_ltu_lit  (i < 16385), rtb_shr_small
     T5 (7)        small literal bounds, `bne`, `beq`                      rtb_ltu_lit / rtb_geu_lit / rtb_ne_lit
     T6 (2)        `addiw t,x,1; blt t,x -> trap`                          rtb_addiw_inc (-2^31 <= x < 2^31 - 1)
     T7 (1)        `andi a0,a4,7; beqz a0 -> on` (pp & 7, pod.h:387)       rtb_and7     (p mod 8 = 0)
     T8 (1)        `ld a7,(t2); addi a7,a7,-8; beqz a7 -> trap`            rtb_ne8      (8 < l)
   PART 2b proves the two sites the plan calls risks: 0x809c0-0x809cc, the first T1 of E01 (the cursor's
   pointer-overflow test before the header's byte-0 read), and 0x82910-0x82918, the B-only divide-by-zero test of
   pod.h:443, whose operand is reloaded from the pp->len cell after the instrumented check at 0x82908. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import PweSpec.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== image B ======================================== *)
(* the writable and the executable segments do not overlap, and nothing wraps *)
Lemma rtsb_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
(* every image byte lies below the low shadow *)
Lemma rtsb_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
(* a run's lazy-VM backing changes no I/O state *)
Lemma same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

(* ======================================== read-only bytes of image B ======================================== *)
(* a lies in a read-only PT_LOAD of image B, as a boolean the kernel can decide *)
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
Definition JTB_A : Z := 0x20f6c.
Definition JTB_PC : Z := 0x8143c.
Definition jtb_region : YP09.region := YP09.mkRegion None JTB_A (JTB_A + 36) 0 0 [YP09.mkChunk JTB_A (CImg 36)].
Lemma jtb_rom : rom_run_b JTB_A 36 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma jtb_region_ok : forall {fx : YK11.FPState} {rc : YM05.RunCeil} E (W : world rsegs) mem,
rom_view rsegs W mem -> region_ok rsegs E (mrestrict (w_H W) mem) jtb_region.
Proof. intros fx rc E W mem HR. apply img_region_ok_rom; [exact HR | unfold JTB_A; lia | unfold JTB_A; lia | lia | exact jtb_rom]. Qed.
(* the entry of k as the `lw` reads it (little-endian, sign-extended), and the target *)
Definition jtb_ent (k : Z) : Z :=
match img_bytes rsegs (JTB_A + 4 * k) 4 with
| Some bs => let v := bytes_le_to_Z bs in if v <? 2 ^ 31 then v else v - 2 ^ 32
| None => 0
end.
Definition jtb_tgt (k : Z) : Z := JTB_A + jtb_ent k.
Lemma jtb_tgts : map jtb_tgt [0; 1; 2; 3; 4; 5; 6; 7; 8] =
[0x81460; 0x81900; 0x817c4; 0x81838; 0x81774; 0x81968; 0x819a0; 0x81888; 0x819f0].
Proof. vm_compute. reflexivity. Qed.
Lemma jtb_tgt_vals : jtb_tgt 0 = 0x81460 /\ jtb_tgt 1 = 0x81900 /\ jtb_tgt 2 = 0x817c4 /\ jtb_tgt 3 = 0x81838 /\
jtb_tgt 4 = 0x81774 /\ jtb_tgt 5 = 0x81968 /\ jtb_tgt 6 = 0x819a0 /\ jtb_tgt 7 = 0x81888 /\ jtb_tgt 8 = 0x819f0.
Proof. vm_compute. repeat split. Qed.
(* the nine values of k after `bltu 8,k` falls through *)
Lemma jtb_cases : forall k, 0 <= k <= 8 ->
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
(* as regs_kept_of_st_ok, but some registers are pinned to an sv of the entry's value (s4 to the shadow-base atom) *)
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

(* the shift arithmetic of `slli a0,a0,0x38` / `srai a3,a0,0x38` (the kind byte, sign-extended) *)
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

(* =============================== PART 2a. the trap-step lemmas (8 shapes) ===============================
   Each lemma gives the bv value of the branch at a trap site from the Z fact the walk lane carries; the lane
   puts it into its symbolic state with YP06 st_ok_add_cond (the arm the engine then takes) or reads it after a
   concrete split. The other branch form of the same shape (the one whose TAKEN arm is the `unimp`) is the
   negation, by YP0m branch_taken_neg: branch_taken (neg_bc c) a b = negb (branch_taken c a b). *)

(* the unsigned compare of two literals in range: the shape of T4, and of the small-literal bounds of T5 *)
Lemma rtb_ltu_lit : forall i c, 0 <= i -> i < c -> c < 2 ^ 64 -> branch_taken BC_LTU (w64 i) (w64 c) = true.
Proof.
intros i c H0 H1 H2. cbn [branch_taken]. unfold bv_ltu, w64.
rewrite !unsigned_lit_small by lia. apply Z.ltb_lt. lia.
Qed.
(* its mirror: the compare is false, so a `bltu` to the trap is not taken (0x82bc0, pod.h:92) *)
Lemma rtb_geu_lit : forall i c, 0 <= i -> i <= c -> c < 2 ^ 64 -> branch_taken BC_LTU (w64 c) (w64 i) = false.
Proof.
intros i c H0 H1 H2. cbn [branch_taken]. unfold bv_ltu, w64.
rewrite !unsigned_lit_small by lia. apply Z.ltb_ge. lia.
Qed.
(* T1 (37 sites, fuzz.h:42): the cursor's pointer-overflow test `addi t,c,1; bltu one,t`. The input block starts
   above 0 and ends below 2^63, so c + 1 neither wraps nor is below 2. *)
Lemma rtb_po1 : forall c, 0 < c -> c + 1 < 2 ^ 64 -> branch_taken BC_LTU (w64 1) (w64 (c + 1)) = true.
Proof. intros c H0 H1. apply rtb_ltu_lit; lia. Qed.
Lemma rtb_po1_geu : forall c, 0 < c -> c + 1 < 2 ^ 64 -> branch_taken BC_GEU (w64 1) (w64 (c + 1)) = false.
Proof.
intros c H0 H1. change BC_GEU with (neg_bc BC_LTU). rewrite branch_taken_neg, (rtb_po1 c H0 H1). reflexivity.
Qed.
(* the 64-bit complement as the `not` instruction and the precomputed cells hold it *)
Lemma rtb_lnot_w64 : forall b, 0 <= b < 2 ^ 64 -> w64 (Z.lnot b) = w64 (2 ^ 64 - 1 - b).
Proof.
intros b Hb. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (Z.lnot b) with ((2 ^ 64 - 1 - b) + (-1) * 2 ^ 64) by (unfold Z.lnot; lia).
rewrite Z_mod_plus_full. reflexivity.
Qed.
(* T2 (10 sites) and T3 (21 sites): `bgeu ~b, o` tests that b + o does not wrap. The complement is in a register
   (`not t,b`, fuzz.h:63 and the table reads) or in a real-frame cell written earlier (R+0x108 = ~pp and the rest). *)
Lemma rtb_not_le : forall b o, 0 <= b < 2 ^ 64 -> 0 <= o -> b + o < 2 ^ 64 ->
branch_taken BC_GEU (w64 (Z.lnot b)) (w64 o) = true.
Proof.
intros b o Hb Ho Hbo. rewrite (rtb_lnot_w64 b Hb).
change BC_GEU with (neg_bc BC_LTU). rewrite branch_taken_neg.
rewrite (rtb_geu_lit o (2 ^ 64 - 1 - b) ltac:(lia) ltac:(lia) ltac:(lia)). reflexivity.
Qed.
Lemma rtb_not_ltu : forall b o, 0 <= b < 2 ^ 64 -> 0 <= o -> b + o < 2 ^ 64 ->
branch_taken BC_LTU (w64 (Z.lnot b)) (w64 o) = false.
Proof.
intros b o Hb Ho Hbo. pose proof (rtb_not_le b o Hb Ho Hbo) as H.
change BC_GEU with (neg_bc BC_LTU) in H. rewrite branch_taken_neg in H.
destruct (branch_taken BC_LTU (w64 (Z.lnot b)) (w64 o)); [discriminate H | reflexivity].
Qed.
(* T4's other form (0x829ac, pod.h:446): `srli t,i,14; bnez t` traps unless i < 16384 *)
Lemma rtb_shr_small : forall i, 0 <= i < 16384 -> branch_taken BC_NE (w64 (Z.shiftr i 14)) (w64 0) = false.
Proof.
intros i Hi. assert (E : Z.shiftr i 14 = 0).
{ rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. change (2 ^ 14) with 16384. lia. }
rewrite E. cbn [branch_taken]. rewrite negb_false_iff. unfold bv_eqb. apply Z.eqb_refl.
Qed.
(* T5's equality forms: `beq a3,s6 -> trap` with a3 = 33 (pod.h:137) and `bne a2,t0 -> on` with t0 = 4 (pod.h:240) *)
Lemma rtb_ne_lit : forall x c, 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> x <> c ->
branch_taken BC_EQ (w64 x) (w64 c) = false /\ branch_taken BC_NE (w64 x) (w64 c) = true.
Proof.
intros x c Hx Hc Hne.
assert (E : bv_eqb (w64 x) (w64 c) = false).
{ apply bv_eqb_false_iff. intros Heq. apply Hne.
  apply (f_equal bv_unsigned) in Heq. unfold w64 in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq. }
cbn [branch_taken]. rewrite E. split; [reflexivity | reflexivity].
Qed.
(* T6 (2 sites, pod.h:432 and :142): `addiw t,x,1; blt t,x` traps on a signed 32-bit overflow of x + 1 *)
Lemma rtb_sext32_small : forall x, 0 <= x < 2 ^ 31 -> bv_signed (w64 x) = x.
Proof.
intros x Hx. unfold w64. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_small by lia. lia.
Qed.
Lemma rtb_addiw_inc : forall x, 0 <= x -> x < 2 ^ 31 - 1 -> branch_taken BC_LT (w64 (x + 1)) (w64 x) = false.
Proof.
intros x H0 H1. cbn [branch_taken]. rewrite bv_lts_signed.
rewrite (rtb_sext32_small (x + 1) ltac:(lia)), (rtb_sext32_small x ltac:(lia)).
apply Z.ltb_ge. lia.
Qed.
(* T7 (1 site, pod.h:387): `andi a0,a4,7; beqz a0` traps unless pp is 8-aligned *)
Lemma rtb_and7 : forall p, 0 <= p -> p mod 8 = 0 -> Z.land p 7 = 0.
Proof.
intros p Hp Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
change (2 ^ 3) with 8. exact Hm.
Qed.
Lemma rtb_and7_eq : forall p, 0 <= p -> p mod 8 = 0 -> branch_taken BC_EQ (w64 (Z.land p 7)) (w64 0) = true.
Proof.
intros p H0 Hm. rewrite (rtb_and7 p H0 Hm). cbn [branch_taken]. unfold bv_eqb. apply Z.eqb_refl.
Qed.
(* T8 (1 site, pod.h:443, B only): `ld a7,0(t2); addi a7,a7,-8; beqz a7` is the divide-by-zero test of
   fuzz_u16() % (pp->len - 8). The guard `bltu s6,9` 0x82750 gives 8 < len on this path, and nothing stores to
   pp + 0x4000 between the read 0x82748 and the reload 0x82910, so len - 8 <> 0. *)
Lemma rtb_ne8 : forall l, 8 < l -> l < 2 ^ 64 + 8 -> branch_taken BC_EQ (w64 (l - 8)) (w64 0) = false.
Proof.
intros l H0 H1. cbn [branch_taken]. apply bv_eqb_false_iff. intros Heq.
apply (f_equal bv_unsigned) in Heq. unfold w64 in Heq.
rewrite !unsigned_lit_small in Heq by lia. lia.
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
Definition rtsb_blk_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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

(* ---- the dispatch block 0x8143c .. 0x8145c ---- *)
Definition jtb_tbl : ctable := build_table rsegs JTB_PC 9 TEmpty.
Lemma jtb_tbl_ok : table_ok rsegs jtb_tbl.
Proof. apply build_table_ok0. unfold JTB_PC. lia. Qed.
Definition JTB_SB : Z := 0x7fff8000.
Definition JTBBx : sv := SOff 32 0.
Definition JTBspan : Z * Z := (JTB_SB, JTB_SB + 2 ^ 44 - 1).
Definition jtb_extra : list word := [Z_to_bv 64 JTB_SB].
Definition jtb_R (kk : Z) (regs regs2 : bvmap 5 word) : Prop :=
getr regs2 11 = w64 (jtb_tgt kk) /\ getr regs2 12 = w64 JTB_A /\
bv_unsigned (getr regs2 10) = (bv_unsigned (getr regs 10) mod 256) * 2 ^ 56 /\
getr regs2 13 = w64 (sext8 (bv_unsigned (getr regs 10) mod 256)).
Lemma rtsb_jt_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
0 <= kk <= 8 -> getr regs 11 = w64 kk -> rom_view rsegs W memc ->
SRr rsegs W (cfg_at rsegs JTB_PC regs memc mdc)
(rtsb_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc (jtb_tgt kk) [10; 11; 12; 13]%bv (jtb_R kk regs)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs kk HJ Hk H11 HR.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (HS0 : st_ok rsegs (Ereg regs jtb_extra) (mkSS JTB_PC sr_atoms [jtb_region] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 JTB_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [apply jtb_region_ok; exact HR | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (11%bv : bv 5) kk HS0 eq_refl H11) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs JTBBx [] (Ereg regs jtb_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jtb_extra) (Ereg regs jtb_extra)) by apply env_agree_refl.
assert (E10 : ew (Ereg regs jtb_extra) 10 = Z_to_bv 64 (bv_unsigned (getr regs 10)))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (u64_range (getr regs 10)) as Hu10.
unfold cfg_at. change (w64 JTB_PC) with (Z_to_bv 64 JTB_PC).
destruct (jtb_cases kk Hk) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
(lazymatch goal with |- context [jtb_tgt ?t] => let st := eval vm_compute in (jtb_tgt t) in
   aj_run_to_tok jtb_tbl_ok HS HJ SHOK JTBspan st end;
 [ awr_ok_tac
 | apply SRr_ret;
   lazymatch type of HS with st_ok _ _ ?ssf _ =>
     let t := eval vm_compute in (ss_pc ssf) in
     replace (jtb_tgt _) with t by (vm_compute; reflexivity) end;
   red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc);
   split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
   split; [exact HJ|];
   split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jtb_extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
   split; [reflexivity|];
   split; [apply Permutation_refl|];
   split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
   split; [apply mo_le_refl; assumption|];
   split;
   [ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|];
     intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]]; cbn in Hr; lia
   | unfold jtb_R;
     rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS);
     lazymatch type of HS with st_ok _ _ ?ssf _ =>
       let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
       let e11 := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
       let e12 := eval vm_compute in (sr_get (ss_regs ssf) (12%bv : bv 5)) in
       let e13 := eval vm_compute in (sr_get (ss_regs ssf) (13%bv : bv 5)) in
       change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
       change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e11;
       change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12;
       change (sr_get (ss_regs ssf) (13%bv : bv 5)) with e13 end;
     split; [unfold w64; f_equal; vm_compute; reflexivity|];
     split; [unfold w64; f_equal; vm_compute; reflexivity|];
     split;
     [ change (bv_unsigned (sv_denot (Ereg regs jtb_extra) (SAlu ALU_SLL (SOff 10 0) (SLit 56))))
         with (U (Ereg regs jtb_extra) (SAlu ALU_SLL (SOff 10 0) (SLit 56)));
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

(* ================= PART 2b. two trap sites, run end to end on image B's own code =================
   The engine decides both branches by itself from the atom range the state carries; neither needs a cond fact.
   These are the kit lemmas of PLAN risks 3 (the jump table, above) and 5 (the B-only divide-by-zero). *)

(* ---- T1 at 0x809c0 .. 0x809cc (E01, fuzz.h:42 before the header's byte-0 read) ----
     0x809c0 addi a0,s2,1 / 0x809c4 li a1,1 / 0x809c8 bltu a1,a0 -> 0x809d0 / 0x809cc j 0x83098 (unimp)
   s2 = the cursor. The fact is the input block's: 0 < c and c + 1 < 2^64, which the entry contract gives
   (0 < data, data + n <= 2^63). *)
Definition rtsb_t1_tbl : ctable := build_table rsegs 0x809c0 4 TEmpty.
Lemma rtsb_t1_tbl_ok : table_ok rsegs rtsb_t1_tbl.
Proof. apply build_table_ok0. lia. Qed.
(* The atom bound is a closed numeral: the engine decides `bltu 1, c + 1` by computing over sv_range, so a bound
   that mentions c would leave the compare symbolic and the run would not reach 0x809d0. *)
Definition rtsb_t1_facts : facts := mkFacts [ (18%nat, mkAF 1 18446744073709551614 0) ] [] [].
Lemma rtsb_trap_809c8 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (c : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 18 = w64 c -> 0 < c -> c + 1 < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x809c0 regs memc mdc)
(rtsb_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x809d0 [10; 11]%bv
  (fun regs2 => getr regs2 10 = w64 (c + 1) /\ getr regs2 11 = w64 1)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c HJ H18 Hc0 Hc1.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E18 : ew (Ereg regs jtb_extra) 18 = Z_to_bv 64 c)
  by (rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact H18).
assert (HS : st_ok rsegs (Ereg regs jtb_extra) (mkSS 0x809c0 sr_atoms [] None rtsb_t1_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x809c0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rtsb_t1_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E18, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBBx [] (Ereg regs jtb_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs jtb_extra) (Ereg regs jtb_extra)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x809c0) with (Z_to_bv 64 0x809c0).
aj_run_to_tok rtsb_t1_tbl_ok HS HJ SHOK JTBspan 0x809d0.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs jtb_extra (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  let e11 := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
  change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e11 end.
split.
- cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
- reflexivity.
Qed.

(* ---- T8 at 0x82910 .. 0x82918 (M01.post, pod.h:443; B only) ----
     0x82910 ld a7,0(t2) / 0x82914 addi a7,a7,-8 / 0x82918 beqz a7 -> 0x83098 (unimp) / 0x8291c beqz a5
   t2 = &pp->len (the slot R+0x158, set at 0x826a0); the cell holds len. The guard `bltu s6,9` 0x82750 gives
   len >= 9 on this path, and no store between 0x82748 and 0x82910 writes pp + 0x4000, so the reload is the same
   len (the plan's risk 5). The `ld` carries no instrumented check of its own: the check at 0x82908 precedes it. *)
Definition rtsb_t8_tbl : ctable := build_table rsegs 0x82910 3 TEmpty.
Lemma rtsb_t8_tbl_ok : table_ok rsegs rtsb_t8_tbl.
Proof. apply build_table_ok0. lia. Qed.
(* closed numerals, as T1's: the engine decides `beqz (len - 8)` by computing over sv_range *)
Definition rtsb_t8_facts : facts := mkFacts [ (33%nat, mkAF 9 9223372036854775808 0) ] [] [].
Definition rtsb_t8_extra (l : Z) : list word := [Z_to_bv 64 JTB_SB; Z_to_bv 64 l].
Definition rtsb_t8_region : YP09.region :=
YP09.mkRegion (Some 7%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Lemma rtsb_trap_82918 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (a l : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 7 = w64 a -> 0 <= a -> a + 8 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) a 8 l -> 8 < l -> l <= 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs 0x82910 regs memc mdc)
(rtsb_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x8291c [17]%bv
  (fun regs2 => getr regs2 17 = w64 (l - 8))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs a l HJ H7 Ha0 Ha1 Hval Hl0 Hl1.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E7 : ew (Ereg regs (rtsb_t8_extra l)) 7 = Z_to_bv 64 a)
  by (rewrite (ew_Ereg_nat regs _ 7 7%bv eq_refl); exact H7).
assert (E33 : ew (Ereg regs (rtsb_t8_extra l)) 33 = Z_to_bv 64 l) by exact (ew_Ereg_extra regs _ 1).
assert (HSoff : sv_denot (Ereg regs (rtsb_t8_extra l)) (SOff 33 0) = Z_to_bv 64 l).
{ apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r. rewrite !unsigned_lit_small by lia.
  unfold zcanon, M64. apply Z.mod_small. lia. }
assert (HREG : region_ok rsegs (Ereg regs (rtsb_t8_extra l)) (mrestrict (w_H W) memc) rtsb_t8_region).
{ unfold region_ok, rtsb_t8_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E7, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs (Ereg regs (rtsb_t8_extra l)) (mrestrict (w_H W) memc) a 0 8 (SOff 33 0) l).
  - exact HSoff.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - rewrite Z.add_0_r. exact Hval. }
assert (HS : st_ok rsegs (Ereg regs (rtsb_t8_extra l)) (mkSS 0x82910 sr_atoms [rtsb_t8_region] None rtsb_t8_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82910) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rtsb_t8_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E33, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBBx [] (Ereg regs (rtsb_t8_extra l)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (rtsb_t8_extra l)) (Ereg regs (rtsb_t8_extra l))) by apply env_agree_refl.
unfold cfg_at. change (w64 0x82910) with (Z_to_bv 64 0x82910).
aj_run_to_tok rtsb_t8_tbl_ok HS HJ SHOK JTBspan 0x8291c.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (rtsb_t8_extra l) (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rtsb_t8_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e17 := eval vm_compute in (sr_get (ss_regs ssf) (17%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (17%bv : bv 5)) with e17 end.
cbn [sv_denot]. rewrite E33. unfold w64. rewrite unsigned_lit_small by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity.
Qed.

(* ---- T4 + T3 at 0x80bf8 .. 0x80c10 (M01.pre1, pod.h:179 inside pod_put32 at pod.h:388; B only) ----
     0x80bf8 lui a0,0x4 / 0x80bfc addiw a0,a0,1 (a0 = 16385)
     0x80c00 bltu a7,a0 -> 0x80c08 / 0x80c04 j 0x83098 (unimp)       a7 = len: the bounds half
     0x80c08 ld a0,0x108(s1) (= ~pp) / 0x80c0c bgeu a0,a7 -> 0x80c14 / 0x80c10 j 0x83098  the pointer half
   The UBSan build of the plain image folds this put (len = 0 after memset(pp, 0, 19744)), so it has no twin
   branch; the facts are the build invariant's len <= 5440 and the complement cell's range, which pp + 19744
   <= 2^63 gives. This is the first of the plan's five B-only traps. *)
Definition rtsb_put32_tbl : ctable := build_table rsegs 0x80bf8 7 TEmpty.
Lemma rtsb_put32_tbl_ok : table_ok rsegs rtsb_put32_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rtsb_put32_facts : facts :=
mkFacts [ (17%nat, mkAF 0 5440 0); (33%nat, mkAF 9223372036854775808 18446744073709551615 0) ] [] [].
Definition rtsb_put32_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 264 272 0 0 [YP09.mkChunk 264 (CVal 8 (SOff 33 0))].
Lemma rtsb_trap_80c00 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (R len npp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 9 = w64 R -> getr regs 17 = w64 len -> 0 <= len -> len <= 5440 ->
0 <= R -> R + 272 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 264) 8 npp ->
9223372036854775808 <= npp -> npp <= 18446744073709551615 ->
SRr rsegs W (cfg_at rsegs 0x80bf8 regs memc mdc)
(rtsb_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x80c14 [10]%bv
  (fun regs2 => getr regs2 10 = w64 npp)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R len npp HJ H9 H17 Hl0 Hl1 HR0 HR1 Hval Hn0 Hn1.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
assert (E9 : ew (Ereg regs (rtsb_t8_extra npp)) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E17 : ew (Ereg regs (rtsb_t8_extra npp)) 17 = Z_to_bv 64 len)
  by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
assert (E33 : ew (Ereg regs (rtsb_t8_extra npp)) 33 = Z_to_bv 64 npp) by exact (ew_Ereg_extra regs _ 1).
assert (HREG : region_ok rsegs (Ereg regs (rtsb_t8_extra npp)) (mrestrict (w_H W) memc) rtsb_put32_region).
{ unfold region_ok, rtsb_put32_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val rsegs (Ereg regs (rtsb_t8_extra npp)) (mrestrict (w_H W) memc) R 264 8 (SOff 33 0) npp).
  - apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r. rewrite !unsigned_lit_small by lia.
    unfold zcanon, M64. apply Z.mod_small. lia.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
  - exact Hval. }
assert (HS : st_ok rsegs (Ereg regs (rtsb_t8_extra npp))
  (mkSS 0x80bf8 sr_atoms [rtsb_put32_region] None rtsb_put32_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80bf8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rtsb_put32_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E17, E33, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs JTBBx [] (Ereg regs (rtsb_t8_extra npp)) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs (rtsb_t8_extra npp)) (Ereg regs (rtsb_t8_extra npp))) by apply env_agree_refl.
unfold cfg_at. change (w64 0x80bf8) with (Z_to_bv 64 0x80bf8).
aj_run_to_tok rtsb_put32_tbl_ok HS HJ SHOK JTBspan 0x80c14.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs (rtsb_t8_extra npp) (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rtsb_put32_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10 end.
unfold w64. apply bv_eq. rewrite denot_SOff, E33, Z.add_0_r.
rewrite !unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia.
Qed.

(* ---- T4 + T3 at 0x826a0 .. 0x826b4 (M01.post, pod.h:197 inside pod_patch32 at pod.h:440; B only) ----
     0x826a0 ld t2,0x158(s1) / 0x826a4 ld a4,0x28(s1) / 0x826a8 ld a5,0x20(s1)   (a5 = top)
     0x826ac bgeu a5,a0 -> 0x83098 (unimp)      a0 = 16385 from 0x8269c: the bounds half
     0x826b0 ld a0,0x108(s1) (= ~pp) / 0x826b4 bltu a0,a5 -> 0x83098 (unimp)     the pointer half
   U writes this top word at pp + 0 with no check (it folds top = 0), so these two have no twin branch either:
   the plan's B-only traps 2 and 3. The facts are top <= 5440 and the complement cell's range. *)
Definition rtsb_patch32_tbl : ctable := build_table rsegs 0x826a0 6 TEmpty.
Lemma rtsb_patch32_tbl_ok : table_ok rsegs rtsb_patch32_tbl.
Proof. apply build_table_ok0. lia. Qed.
Definition rtsb_patch32_facts : facts :=
mkFacts [ (33%nat, mkAF 0 5440 0); (35%nat, mkAF 9223372036854775808 18446744073709551615 0) ] [] [].
Definition rtsb_extra4 (a b c d : Z) : list word :=
[Z_to_bv 64 JTB_SB; Z_to_bv 64 a; Z_to_bv 64 b; Z_to_bv 64 c; Z_to_bv 64 d].
Definition rtsb_patch32_region : YP09.region :=
YP09.mkRegion (Some 9%nat) 32 352 0 0
  [YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 34 0));
   YP09.mkChunk 264 (CVal 8 (SOff 35 0)); YP09.mkChunk 344 (CVal 8 (SOff 36 0))].
Lemma rtsb_trap_826ac : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (R top other npp lenp : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 9 = w64 R -> getr regs 10 = w64 16385 ->
0 <= R -> R + 352 <= 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 32) 8 top ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 40) 8 other ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 264) 8 npp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 344) 8 lenp ->
0 <= top -> top <= 5440 ->
9223372036854775808 <= npp -> npp <= 18446744073709551615 ->
0 <= other < 2 ^ 64 -> 0 <= lenp < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs 0x826a0 regs memc mdc)
(rtsb_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x826b8 [7; 10; 14; 15]%bv
  (fun regs2 => getr regs2 7 = w64 lenp /\ getr regs2 14 = w64 other /\
                getr regs2 15 = w64 top /\ getr regs2 10 = w64 npp)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R top other npp lenp
  HJ H9 H10 HR0 HR1 Vtop Voth Vnpp Vlen Ht0 Ht1 Hn0 Hn1 Ho Hlp.
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
set (EX := rtsb_extra4 top other npp lenp) in *.
assert (E9 : ew (Ereg regs EX) 9 = Z_to_bv 64 R)
  by (rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
assert (E33 : ew (Ereg regs EX) 33 = Z_to_bv 64 top) by exact (ew_Ereg_extra regs _ 1).
assert (E34 : ew (Ereg regs EX) 34 = Z_to_bv 64 other) by exact (ew_Ereg_extra regs _ 2).
assert (E35 : ew (Ereg regs EX) 35 = Z_to_bv 64 npp) by exact (ew_Ereg_extra regs _ 3).
assert (E36 : ew (Ereg regs EX) 36 = Z_to_bv 64 lenp) by exact (ew_Ereg_extra regs _ 4).
assert (Hden : forall n v, ew (Ereg regs EX) n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot (Ereg regs EX) (SOff n 0) = Z_to_bv 64 v).
{ intros n v Hn Hv. apply bv_eq. rewrite denot_SOff, Hn, Z.add_0_r.
  rewrite !unsigned_lit_small by lia. unfold zcanon, M64. apply Z.mod_small. lia. }
assert (HREG : region_ok rsegs (Ereg regs EX) (mrestrict (w_H W) memc) rtsb_patch32_region).
{ unfold region_ok, rtsb_patch32_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho'; lia|].
  repeat (apply Forall_cons); try apply Forall_nil.
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 32 8 (SOff 33 0) top);
    [apply Hden; [exact E33 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vtop].
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 40 8 (SOff 34 0) other);
    [apply Hden; [exact E34 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Voth].
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 264 8 (SOff 35 0) npp);
    [apply Hden; [exact E35 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vnpp].
  - apply (chunk_ok_val rsegs (Ereg regs EX) (mrestrict (w_H W) memc) R 344 8 (SOff 36 0) lenp);
    [apply Hden; [exact E36 | lia] | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia | exact Vlen]. }
assert (HS0 : st_ok rsegs (Ereg regs EX)
  (mkSS 0x826a0 sr_atoms [rtsb_patch32_region] None rtsb_patch32_facts)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x826a0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [exact HREG | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok rtsb_patch32_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E33, E35, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
pose proof (st_ok_pin_lit rsegs (Ereg regs EX) _ _ (10%bv : bv 5) 16385 HS0 eq_refl H10) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs JTBBx [] (Ereg regs EX) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs EX) (Ereg regs EX)) by apply env_agree_refl.
unfold cfg_at. change (w64 0x826a0) with (Z_to_bv 64 0x826a0).
aj_run_to_tok rtsb_patch32_tbl_ok HS HJ SHOK JTBspan 0x826b8.
{ awr_ok_tac. }
apply SRr_ret.
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs EX (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
{ intros a0; unfold aview, mbyte; rewrite (HFr (Z_to_bv 64 a0)); [reflexivity|].
  intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<-|[]];
  unfold rtsb_patch32_region in Hr; cbn in Hr; lia. }
rewrite !(st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let e7 := eval vm_compute in (sr_get (ss_regs ssf) (7%bv : bv 5)) in
  let e10 := eval vm_compute in (sr_get (ss_regs ssf) (10%bv : bv 5)) in
  let e14 := eval vm_compute in (sr_get (ss_regs ssf) (14%bv : bv 5)) in
  let e15 := eval vm_compute in (sr_get (ss_regs ssf) (15%bv : bv 5)) in
  change (sr_get (ss_regs ssf) (7%bv : bv 5)) with e7;
  change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
  change (sr_get (ss_regs ssf) (14%bv : bv 5)) with e14;
  change (sr_get (ss_regs ssf) (15%bv : bv 5)) with e15 end.
split; [unfold w64; apply Hden; [exact E36 | lia]|].
split; [unfold w64; apply Hden; [exact E34 | lia]|].
split; [unfold w64; apply Hden; [exact E33 | lia]|].
unfold w64; apply Hden; [exact E35 | lia].
Qed.
End d.
End b.

(* ============================== PART 3. the fuzz_u32 read-ahead (PLAN risk 4) ==============================
   fuzz.h:39-55's fuzz_u32 is inlined twice, in ent_build's cases 2 (pod.h:299) and 3 (pod.h:310), the only two
   sites of the function. Both read up to four input bytes and compare the ORIGINAL byte count (nn = left + 2,
   in t1) with 3, 1 and 1 to decide how many are there; so the length split is inside ONE lemma per site, not one
   file per length. Image B keeps the cursor in s2, the base atom c - 2 in s10, the bytes left in a2, nn in t1,
   the shadow offset in s4, and the literal 1 of the trap guards in a6:
     site P  0x81e58 `beqz a2,0x81f48`, reads at 0x81e78 / 0x81fdc / 0x8200c / 0x821dc, join 0x82020 .. end 0x82038
     site Q  0x81e94 `beqz a2,0x81f54`, reads at 0x81eb4 / 0x82060 / 0x82090 / 0x82208, join 0x820a4 .. end 0x820bc
   (end = the pc after the last `or`, before the record's type store). Each read is preceded by its T1 trap guard
   (`addi x,s2,1; bltu a6,x` or `bgeu a6,x`), which the engine decides by itself from a6 = SLit 1 and the range of
   the cursor atom (PART 2a T1); the four shadow checks are the `bnez t,L` form (L = `andi u,s2,7; blt u,t,back;
   j report`, at 0x82338 .. 0x82398), so the token engine (YCbn tok_load / tok_branch) takes both outcomes itself
   and leaves one obligation `range_addressable ... (c + i) 1` per read. The five arms (left = 0, 1, 2, 3, >= 4)
   are the five ways out; in the first four left and nn are literals and the engine decides the three tests
   itself, in the fifth the atom facts 4 <= left and 6 <= nn decide them. The four join shapes are image A's:
   B's `or a1,a3,a1; or a4,a5,a4; slli a4,a4,0x10; or a1,a1,a4` builds the same sv as A's join. *)

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
Definition u32b_extra (rest : list byte) (left nn : Z) : list word :=
  [w64 SHADOW_OFF; w64 (u32_b rest 0); w64 (u32_b rest 1); w64 (u32_b rest 2); w64 (u32_b rest 3); w64 left; w64 nn].
Definition u32b_bchunks (m : nat) : list YP09.chunk :=
  map (fun i => YP09.mkChunk (2 + Z.of_nat i) (CVal 1 (SOff (33 + i) 0))) (seq 0 m).
Definition u32b_in_region (m : nat) : YP09.region :=
  YP09.mkRegion (Some 26%nat) 2 (2 + Z.of_nat m) 0 0 (u32b_bchunks m).
(* no input byte is read when nothing is left: then there is no region *)
Definition u32b_regs_of (m : nat) : smem :=
  match m with O => [] | S _ => [u32b_in_region m] end.
(* the cursor s2 = s10 + 2, the shadow offset s4, a2 = the bytes left, t1 = the original count, a6 = 1 *)
Definition u32b_ss (pc : Z) (a2v t1v : sv) (m : nat) (G : facts) : sstate :=
mkSS pc (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (18%bv : bv 5) (SOff 26 2)) (20%bv : bv 5) (SOff 32 0))
  (12%bv : bv 5) a2v) (6%bv : bv 5) t1v) (16%bv : bv 5) (SLit 1))
  (u32b_regs_of m) None G.
(* The atom facts. The engine places the shadow cell of every read in the span [K, K + 2^44) only from the
   cursor atom's upper bound (YCbn ob_in_span: (hi + offset) >> 3 < 2^44), so the bound of atom 26 = c - 2 is the
   arm's own: with m bytes read, c + m <= 2^47 - 1 (the input's amem_range) gives c - 2 <= 2^47 - 3 - m, and the
   highest read c + m - 1 stays below 2^47. The count atoms 37 / 38 need only their lower bounds 4 / 6 (they
   decide the three length tests). No allocation ceiling and no 2^26 bound is used. *)
Definition u32b_facts0 (m : nat) : facts :=
  mkFacts [ (26%nat, mkAF 1 (140737488355325 - Z.of_nat m) 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition u32b_factsF : facts :=
  mkFacts [ (26%nat, mkAF 1 140737488355321 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (37%nat, mkAF 4 140737488355327 0); (38%nat, mkAF 6 140737488355329 0) ] [] [].
Lemma u32b_regions_wf : forall m, (m <= 4)%nat -> regions_wf (u32b_regs_of m) = true.
Proof.
intros m Hm. destruct m as [|[|[|[|[|m]]]]]; try (exfalso; lia); vm_compute; reflexivity.
Qed.
Lemma u32b_inreg_ok : forall E (W : world rsegs) mem c (m : nat) (rest : list byte),
ew E 26 = Z_to_bv 64 (c - 2) ->
(forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
(m <= length rest)%nat -> (m <= 4)%nat -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
garr8 rsegs (mrestrict (w_H W) mem) c (map (fun x : byte => bv_unsigned x) rest) ->
region_ok rsegs E (mrestrict (w_H W) mem) (u32b_in_region m).
Proof.
intros E W mem c m rest E26 Eb Hm1 Hm2 Hc0 Hc1 Hg. unfold region_ok, u32b_in_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E26, unsigned_lit_small by lia.
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
unfold u32b_bchunks. apply Forall_forall. intros ch Hin. apply in_map_iff in Hin as (i & <- & Hi).
apply in_seq in Hi. apply Hch. lia.
Qed.
Lemma u32b_entry : forall (regs : bvmap 5 word) (W : world rsegs) memc (c nn left : Z) (m : nat) (rest : list byte)
  a2v t1v G pc,
getr regs 26 = w64 (c - 2) -> getr regs 20 = w64 SHADOW_OFF -> getr regs 18 = w64 c -> getr regs 16 = w64 1 ->
sv_denot (Ereg regs (u32b_extra rest left nn)) a2v = getr regs 12 ->
sv_denot (Ereg regs (u32b_extra rest left nn)) t1v = getr regs 6 ->
0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
(m <= length rest)%nat -> (m <= 4)%nat ->
garr8 rsegs (mrestrict (w_H W) memc) c (map (fun x : byte => bv_unsigned x) rest) ->
facts_ok (Ereg regs (u32b_extra rest left nn)) G -> 0 <= pc ->
st_ok rsegs (Ereg regs (u32b_extra rest left nn)) (u32b_ss pc a2v t1v m G)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros regs W memc c nn left m rest a2v t1v G pc H26 H20 H18 H16 Ha2 Ht1 Hc0 Hc1 Hm1 Hm2 Hg HG Hpc.
unfold w64 in H26, H20, H18, H16.
set (E := Ereg regs (u32b_extra rest left nn)) in *.
assert (E26 : ew E 26 = Z_to_bv 64 (c - 2)) by (subst E; rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (Eb : forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)).
{ intros i Hi. subst E. destruct i as [|[|[|[|i]]]]; try (exfalso; lia).
  - exact (ew_Ereg_extra regs _ 1). - exact (ew_Ereg_extra regs _ 2).
  - exact (ew_Ereg_extra regs _ 3). - exact (ew_Ereg_extra regs _ 4). }
rewrite restrict_mkst_fx. unfold u32b_ss.
assert (HS0 : st_ok rsegs E (mkSS pc sr_atoms (u32b_regs_of m) None G)
  (mkst regs (Z_to_bv 64 pc) (mrestrict (w_H W) memc) (seg_rom rsegs))).
{ subst E. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - apply u32b_regions_wf. exact Hm2.
  - unfold u32b_regs_of; destruct m as [|m']; repeat (apply Forall_cons); try apply Forall_nil.
    apply (u32b_inreg_ok _ W memc c (S m') rest E26 Eb Hm1 Hm2 Hc0 Hc1 Hg).
  - unfold u32b_regs_of; destruct m as [|m']; cbn [pairwise_disjoint all_disjoint]; tauto.
  - exact HG. }
pose proof (st_ok_pin_sv rsegs E _ _ (18%bv : bv 5) (SOff 26 2) HS0 eq_refl
  ltac:(cbn [ms_regs mkst sv_denot]; rewrite E26, unsigned_lit_small by lia; rewrite H18; f_equal; lia)) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_sv rsegs E _ _ (20%bv : bv 5) (SOff 32 0) HS1 eq_refl
  ltac:(cbn [ms_regs mkst sv_denot]; subst E; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H20))) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pin_sv rsegs E _ _ (12%bv : bv 5) a2v HS2 eq_refl ltac:(cbn [ms_regs mkst]; exact Ha2)) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
pose proof (st_ok_pin_sv rsegs E _ _ (6%bv : bv 5) t1v HS3 eq_refl ltac:(cbn [ms_regs mkst]; exact Ht1)) as HS4.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
pose proof (st_ok_pin_lit rsegs E _ _ (16%bv : bv 5) 1 HS4 eq_refl ltac:(cbn [ms_regs mkst]; exact H16)) as HS5.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS5.
exact HS5.
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
Lemma u32b_facts0_ok : forall regs rest left nn c m,
getr regs 26 = Z_to_bv 64 (c - 2) -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 -> length rest = m ->
facts_ok (Ereg regs (u32b_extra rest left nn)) (u32b_facts0 m).
Proof.
intros regs rest left nn c m H26 Hc0 Hc1 Hm. subst m.
assert (E26 : ew (Ereg regs (u32b_extra rest left nn)) 26 = Z_to_bv 64 (c - 2))
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew (Ereg regs (u32b_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
pose proof shadow_off_range as Hso.
pose proof (Nat2Z.is_nonneg (length rest)) as Hl0.
split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok u32b_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E26, E32, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
Lemma u32b_factsF_ok : forall regs rest left nn c,
getr regs 26 = Z_to_bv 64 (c - 2) -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
4 <= left -> nn = left + 2 -> left = Z.of_nat (length rest) ->
facts_ok (Ereg regs (u32b_extra rest left nn)) u32b_factsF.
Proof.
intros regs rest left nn c H26 Hc0 Hc1 Hl4 Hnn Hleft.
assert (E26 : ew (Ereg regs (u32b_extra rest left nn)) 26 = Z_to_bv 64 (c - 2))
  by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26).
assert (E32 : ew (Ereg regs (u32b_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
assert (E37 : ew (Ereg regs (u32b_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5).
assert (E38 : ew (Ereg regs (u32b_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6).
pose proof shadow_off_range as Hso.
split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok u32b_factsF]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E26, E32, E37, E38, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
End u32f.

Ltac u32b_sv HSx :=
  lazymatch goal with |- getr _ _ = _ => rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HSx) | _ => idtac end;
  match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
Ltac u32b_obl E32x E26x Hrax :=
  try unfold ob_holds; try unfold U32Bx; try cbn [ob_x ob_n];
  rewrite (U_atom _ 32 SHADOW_OFF E32x shadow_off_range);
  first [ rewrite (U_atom_off _ 26 _ 2 E26x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 26 _ 3 E26x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 26 _ 4 E26x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 26 _ 5 E26x ltac:(lia) ltac:(lia)) ];
  eapply ra_sub; [exact Hrax | lia | lia].
Ltac u32b_leaf regs0 extra0 pins pinstac valtac :=
lazymatch goal with
| HS : st_ok _ ?Ex ?ssf (restrict (w_H ?Wx) ?msx),
  HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lycx ?Scx _ _ _ _,
  HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  apply SRr_ret;
  red; exists lycx, Scx, (ms_regs msx), (ms_mem msx); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H Wx) Ex ssf msx HS eq_refl) at 1; reflexivity|];
  split; [exact HJx|];
  split; [eapply (regs_kept_of_st_ok_pins rsegs Ex ssf msx regs0 extra0 (w_H Wx) _ pins HS);
          [ split; [intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]
          | pinstac
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

(* the code of the two sites: [0x81e54, 0x820d8) (both first reads, both joins, the second and third reads),
   [0x821c4, 0x8221c) (the fourth reads) and the slow blocks [0x82338, 0x82398) of their shadow checks *)
Definition u32b_tbl : ctable :=
  build_table rsegs 0x82338 24 (build_table rsegs 0x821c4 22 (build_table rsegs 0x81e54 161 TEmpty)).
Lemma u32b_tbl_ok : table_ok rsegs u32b_tbl.
Proof. apply build_table_ok; [lia | apply build_table_ok; [lia | apply build_table_ok0; lia]]. Qed.

(* ---- one arm of a site: m bytes read (m = left < 4, or 4 when left >= 4) ---- *)
Ltac u32b_run_arm pcB E32 E26 Hra regs extra pins pinstac valtac :=
  lazymatch goal with HS : st_ok _ ?Ex _ (restrict (w_H ?Wx) (mkst _ _ ?mc _)),
                      HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  assert (SHOK : sh_ok rsegs U32Bx [] Ex (mrestrict (w_H Wx) mc)) by constructor;
  aj_run_to_tok u32b_tbl_ok HS HJ SHOK U32span pcB;
    try solve [u32b_obl E32 E26 Hra]; try solve [awr_ok_tac];
    u32b_leaf regs extra pins pinstac valtac end.

(* ---- the two sites, each with its five length arms ---- *)
Section u32b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Definition rtsb_u32_stmt (pcA pcB : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (c left nn : Z) (rest : list byte),
left = Z.of_nat (length rest) -> nn = left + 2 ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 12 = w64 left -> getr regs 26 = w64 (c - 2) -> getr regs 6 = w64 nn ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 18 = w64 c -> getr regs 16 = w64 1 ->
0 < c - 2 -> c + left <= 140737488355327 ->
garr8 rsegs (mrestrict (w_H W) memc) c (map (fun x : byte => bv_unsigned x) rest) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c left ->
SRr rsegs W (cfg_at rsegs pcA regs memc mdc)
 (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcB
   [11; 12; 13; 14; 15; 18]%bv
   (fun regs2 => getr regs2 11 = w64 (fst (Cursor.fuzz_u32 rest)) /\
                 getr regs2 12 = w64 (Z.of_nat (length rest - 4)) /\
                 getr regs2 18 = w64 (c + Z.of_nat (Nat.min 4 (length rest))) /\
                 getr regs2 20 = w64 SHADOW_OFF)).

(* the whole proof of one site, from its start pc pcA to its end pc pcB *)
Local Ltac u32b_site pcA pcB :=
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c left nn rest
  Hleft Hnn HJ H12 H26 H6 H20 H18 H16 Hc0 Hc1 Hg Hra;
pose proof rtsb_wx as Hwx; pose proof rtsb_segs_low as Hsegs;
pose proof shadow_off_range as Hso; pose proof (Nat2Z.is_nonneg (length rest)) as Hl0;
unfold w64 in H12, H26, H6, H20, H18, H16;
unfold cfg_at; change (w64 pcA) with (Z_to_bv 64 pcA);
destruct (Z_le_gt_dec 4 left) as [HF|Hsm];
[ (* 4 or more bytes left *)
  assert (HlenF : (4 <= length rest)%nat) by lia;
  assert (E26 : ew (Ereg regs (u32b_extra rest left nn)) 26 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26);
  assert (E32 : ew (Ereg regs (u32b_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0);
  assert (E37 : ew (Ereg regs (u32b_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5);
  assert (E38 : ew (Ereg regs (u32b_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6);
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32b_extra rest left nn)) (33 + i) = Z_to_bv 64 (u32_b rest i))
  by (intros i Hi; destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
      [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
      | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]);
  pose proof (u32b_entry regs W memc c nn left 4%nat rest (SOff 37 0) (SOff 38 0) u32b_factsF pcA
    H26 H20 H18 H16
    ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H12))
    ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H6))
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32b_factsF_ok regs rest left nn c H26 Hc0 ltac:(lia) ltac:(lia) Hnn Hleft) ltac:(lia)) as HS;
  u32b_run_arm pcB E32 E26 Hra regs (u32b_extra rest left nn)
    [((20%bv : bv 5), SOff 32 0); ((16%bv : bv 5), SLit 1); ((6%bv : bv 5), SOff 38 0)]
    ltac:(intros rr ee Hin; cbn [In] in Hin;
          destruct Hin as [Heq|[Heq|[Heq|[]]]]; inversion Heq; subst;
          cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
          first [ (rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H20))
                | (rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H6))
                | exact (eq_sym H16) ])
    ltac:(split; [u32b_sv HS; apply (u32_val4 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)))
          | split; [u32b_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                    rewrite E38, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | split; [u32b_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                    rewrite E26, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | u32b_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
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
  lazymatch type of H12 with getr _ _ = Z_to_bv 64 ?lv =>
  assert (E26 : ew (Ereg regs (u32b_extra rest lv (lv + 2))) 26 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact H26);
  assert (E32 : ew (Ereg regs (u32b_extra rest lv (lv + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0);
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32b_extra rest lv (lv + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i))
  by (intros i Hi; destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
      [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
      | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]);
  pose proof (u32b_entry regs W memc c (lv + 2) lv mm rest (SLit lv) (SLit (lv + 2)) (u32b_facts0 mm) pcA
    H26 H20 H18 H16
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32b_facts0_ok regs rest lv (lv + 2) c mm H26 Hc0 ltac:(lia) HK) ltac:(lia)) as HS;
  u32b_run_arm pcB E32 E26 Hra regs (u32b_extra rest lv (lv + 2))
    [((20%bv : bv 5), SOff 32 0); ((16%bv : bv 5), SLit 1); ((6%bv : bv 5), SLit (lv + 2))]
    ltac:(intros rr ee Hin; cbn [In] in Hin;
          destruct Hin as [Heq|[Heq|[Heq|[]]]]; inversion Heq; subst;
          cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
          first [ (rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H20))
                | exact (eq_sym H6)
                | exact (eq_sym H16) ])
    ltac:(split; [u32b_sv HS;
                  first [ apply (u32_val0 _ rest ltac:(lia))
                        | apply (u32_val1 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
                        | apply (u32_val2 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
                        | apply (u32_val3 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia)) ]
          | split; [u32b_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
          | split; [u32b_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                    rewrite E26, unsigned_lit_small by lia; unfold w64; f_equal; lia
          | u32b_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
            rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]])
  end end ].

Lemma rtsb_u32_block2 : rtsb_u32_stmt 0x81e58 0x82038.
Proof using MTL LAWS. u32b_site 0x81e58 0x82038. Qed.
Lemma rtsb_u32_block3 : rtsb_u32_stmt 0x81e94 0x820bc.
Proof using MTL LAWS. u32b_site 0x81e94 0x820bc. Qed.
End d2.
End u32b.

(* ============================== PART 4. chaining blocks, the memset / memcpy call, the frame ==============================
   (a) rtsb_post: the post of a block that writes memory (rtsb_blk_post with every byte outside Wr kept instead of
       every byte, and R reading the world and memory too); rtsb_post_of_blk, rtsb_post_seq, rtsb_blk_seq chain two
       blocks into one with SRr_bind (the union of the clobbered registers and of the write sets).
   (b) the call adapter of the two intrinsics (__asan_memset 0x51d54, __asan_memcpy 0x518b8; image B's 6 memset and
       9 memcpy calls): rtsb_intrin_at is the kernel's aintrin_realizes (YG0d.v) carried under the caller's journal
       (YCbq aj_intrin_at, also keeping the callee's same_but_materialized); rtsb_intrin_seq chains it after a block
       that stops at the callee's entry with ra = the return pc, so a walk lane gets the call as one more block. The
       allocator's calls (malloc trampoline 0x52c0c, free trampoline 0x52c08) need no adapter here: the kernel's own
       YCbq aj_malloc_at04 / aj_free_at are the journal-level adapters (with rtsb_segs_low for their segs_low).
   (c) the frame for locals F (class 4, 1024 bytes, F mod 32 = 0 by AR_frames_law; the request is 704, the 88
       prologue shadow stores cover [F, F + 704)): its bounds and the shadow address of an object at F + o.
   (d) the write rights of a block at the places the walk writes: the frame objects (t, ch, r, e, e42, e62, hz),
       its 128 shadow bytes (the 16 scope-store sites), and the real frame's cells (the journal's stack window).
   (e) the call of any leaf runtime routine whose contract has the kernel's ecall form (the strlen and strcmp
       wrappers 0x421ec / 0x421f4, the bcmp wrapper 0x42200, the intrinsics). *)
(* image B's runtime entries the walk calls, measured on the twin: the two intrinsics rtsb_intrin_at takes, the
   allocator trampolines the kernel's own YCbq aj_malloc_at04 / aj_free_at take (they need segs_low, which is
   rtsb_segs_low), the three wrappers rtsb_ecall_at takes, the class-4 frame allocator and the shadow filler of
   the release. The walk lanes cite these instead of re-measuring them. *)
Definition RTSB_MEMCPY : Z := 0x518b8.
Definition RTSB_MEMSET : Z := 0x51d54.
Definition RTSB_MALLOC : Z := 0x52c0c.
Definition RTSB_FREE : Z := 0x52c08.
Definition RTSB_STRLEN : Z := 0x421ec.
Definition RTSB_STRCMP : Z := 0x421f4.
Definition RTSB_BCMP : Z := 0x42200.
Definition RTSB_FRAME_ALLOC4 : Z := 0x3d300.
Definition RTSB_META_FILL_F5 : Z := 0x54880.

Section c3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d3.
Variable B : asyms.
Variable MT : ameter_ops.
Definition rtsb_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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
Lemma rtsb_post_of_blk : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob
(Rr : bvmap 5 word -> Prop) (Wr : Z -> Prop) W2 c2,
rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr W2 c2 ->
rtsb_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Wr (fun _ regs2 _ => Rr regs2) W2 c2.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc clob Rr Wr W2 c2
(ly2 & S2 & regs2 & mem2 & md2 & Ec & HJ & Hr & Hf & Hp & Hio & Hmo & Hm & HR).
exists ly2, S2, regs2, mem2, md2. repeat (split; [eassumption|]).
split; [intros a _ _; apply Hm|]. exact HR.
Qed.
Lemma rtsb_post_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(Wr1 Wr2 : Z -> Prop) (R1 R2 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rtsb_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 Wr1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, 0 <= a < 2 ^ 64 -> ~ Wr1 a -> aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 W1 regs1 mem1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (rtsb_post STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 Wr2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rtsb_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) (fun a => Wr1 a \/ Wr2 a) R2).
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
Lemma rtsb_blk_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 pc1 pc2 clob1 clob2
(R1 R2 : bvmap 5 word -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 clob1 R1) ->
(forall W1 ly1 S1 regs1 mem1 md1, wle W W1 ->
 ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k ->
 (forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob1 -> getr regs1 r = getr regs r) ->
 frames S1 = frames Sc -> Permutation (ablocks B ly1 S1) (ablocks B lyc Sc) -> same_io mdc md1 -> mo_le MT Sc S1 0 ->
 (forall a, aview rsegs (w_H W1) mem1 a = aview rsegs (w_H W) memc a) ->
 R1 regs1 ->
 SRr rsegs W1 (cfg_at rsegs pc1 regs1 mem1 md1)
 (rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pc2 clob2 R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
(rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc2 (clob1 ++ clob2) R2).
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
Definition rtsb_caller_saved : list (bv 5) :=
[1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.
Lemma rtsb_callee : forall r : bv 5, bv_unsigned r <> 0 -> ~ In r rtsb_caller_saved -> acallee_saved (bv_unsigned r).
Proof.
intros r H0 Hn. pose proof (in_nz_regs r H0) as Hin. cbv [nz_regs In] in Hin.
repeat (destruct Hin as [<- | Hin];
[ first
  [ (lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
       change (bv_unsigned x) with v end; unfold acallee_saved; lia)
  | (exfalso; apply Hn; cbv [rtsb_caller_saved In]; repeat (first [left; apply bv_eq; reflexivity | right])) ]
| ]).
destruct Hin.
Qed.
(* a register the state holds as its own atom *)
Lemma rtsb_den_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. apply bv_eq. rewrite denot_SOff, H, Z.add_0_r. rewrite !unsigned_lit_small by exact Hv.
apply zcanon_id. unfold M64. lia.
Qed.
(* an aview value kept, as a val_mem *)
Lemma rtsb_val_kept : forall H (m m' : word -> option byte) a n v,
(forall k, 0 <= k < Z.of_nat n -> aview rsegs H m' (a + k) = aview rsegs H m (a + k)) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v Hk Hv. exact (val_mem_kept rsegs H H m m' a n v Hk Hv). Qed.
(* a one-byte chunk of value 0 *)
Lemma rtsb_chunk0 : forall E H mem base o,
YP09.chunk_ok rsegs E (mrestrict H mem) base (YP09.mkChunk o (CVal 1 (SLit 0))) -> aview rsegs H mem (base + o) = Some 0.
Proof.
intros E H mem base o Hc. destruct (Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
assert (Hb3 : mbyte rsegs (mrestrict H mem) (base + o) = Some b) by (rewrite <- Hb2; f_equal; cbn; ring).
unfold aview. rewrite Hb3. cbn [cbyte YP09.c_val] in Hb1. injection Hb1 as <-.
first [reflexivity | (vm_compute; reflexivity)].
Qed.
(* a region of a run's state, and its chunks *)
Lemma rtsb_region_nth : forall E ss ms i r (H : word -> bool),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (mrestrict H (ms_mem ms)) r.
Proof.
intros E ss ms i r H HS Hi. destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma rtsb_chunks : forall E m n b cs lo hi wlo whi,
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
Lemma rtsb_intrin_at : forall op pc, aintrin_realizes rsegs B op pc ->
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
{ eapply (ajournal_after_write rsegs B LAWS rtsb_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
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
Lemma rtsb_intrin_seq : forall op pcI retpc, aintrin_realizes rsegs B op pcI ->
forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob (Wr : Z -> Prop)
  (R1 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) d x n o,
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rtsb_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pcI clob Wr R1) ->
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
  (rtsb_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc (clob ++ rtsb_caller_saved)
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
{ exact (rtsb_intrin_at op pcI AI W1 regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k d x n o (w64 retpc)
    HJ1 Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp Hal Hneg Hbud Hgp Htp Hra Hret Hdest Hamr Hrad Hhull Hsrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsame & H10 & Heff & Hfr).
exists ly1, S1, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros r Hr0 Hn'. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  rewrite (HP (bv_unsigned r) (rtsb_callee r Hr0 ltac:(intros X; apply Hn'; apply in_or_app; right; exact X))).
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

(* ---- (c) the frame for locals: a class-4 side-stack frame F (1024 bytes), F mod 32 = 0 ---- *)
Lemma rtsb_fdiv : forall F, F mod 32 = 0 -> F = 32 * (F / 32) /\ shadow_addr F = SHADOW_OFF + 4 * (F / 32).
Proof.
intros F H. pose proof (Z.div_mod F 32 ltac:(lia)) as E. rewrite H, Z.add_0_r in E.
split; [exact E|]. unfold shadow_addr. f_equal. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E.
replace (32 * q) with ((4 * q) * 8) by ring. apply Z.div_mul. lia.
Qed.
(* the shadow address of an object at F + o is F's plus o / 8 *)
Lemma rtsb_fsh_addr : forall F o, F mod 32 = 0 -> 0 <= o -> shadow_addr (F + o) = shadow_addr F + o / 8.
Proof.
intros F o H Ho. destruct (rtsb_fdiv F H) as [E1 E2]. rewrite E2. unfold shadow_addr.
remember (F / 32) as q eqn:Hq. clear Hq. rewrite E1.
replace (32 * q + o) with (o + (4 * q) * 8) by ring. rewrite Z.div_add by lia. ring.
Qed.
(* the same, as the instrumented check computes it *)
Lemma rtsb_fsh_of : forall F o, F mod 32 = 0 -> 0 <= o -> shadow_of_addr SHADOW_OFF (F + o) = shadow_addr F + o / 8.
Proof. intros F o H Ho. rewrite <- (rtsb_fsh_addr F o H Ho). reflexivity. Qed.
Lemma rtsb_fmod8 : forall F j, F mod 32 = 0 -> (F + 8 * j) mod 8 = 0.
Proof.
intros F j H. destruct (rtsb_fdiv F H) as [E1 _]. remember (F / 32) as q eqn:Hq. clear Hq. rewrite E1.
replace (32 * q + 8 * j) with ((4 * q + j) * 8) by ring. apply Z_mod_mult.
Qed.
(* the frame of an in_app address F: its bounds, its shadow below the ceiling and apart from F, every object
   range in it inside the low or high application memory. Class 4: 1024 bytes, 128 shadow bytes. *)
Lemma rtsb_fbounds : forall {rc : YM05.RunCeil} F, F mod 32 = 0 -> in_app F 1024 ->
4096 <= F /\ F + 1024 <= alloc_ceiling /\ 0 <= shadow_addr F /\ shadow_addr F + 128 <= alloc_ceiling /\
(F + 1024 <= shadow_addr F \/ shadow_addr F + 128 <= F) /\
(forall o n, 0 <= o -> 0 <= n -> o + n < 1024 -> amem_range (F + o) n).
Proof.
intros rc F Hm Ha. destruct (rtsb_fdiv F Hm) as [E1 E2]. pose proof asan_consts as (C1 & _). rewrite E2.
remember (F / 32) as q eqn:Hq. clear Hq.
unfold in_app, amem_range, SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
intros o n Ho Hn Hon. lia.
Qed.

(* ---- (d) the write rights of a block (YCbq awr_byte / awr_ok) at the places the walk writes: the frame for
   locals' objects (memset / memcpy into t, ch, e, e42, e62; stores into r, hz), its 128 shadow bytes (the 16
   scope-store sites), and the real frame's cells (the journal's stack window). ---- *)
Lemma rtsb_awr_fobj : forall STK sp0 FP bl0 blc ly own pos a,
In (4, pos) own -> frame_addr ly 4 pos <= a < frame_addr ly 4 pos + 1024 -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right; right; right. exists 4, pos. split; [exact Hown|]. left.
unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 4) with 1024. lia.
Qed.
Lemma rtsb_awr_fsh : forall STK sp0 FP bl0 blc ly own pos a,
In (4, pos) own -> shadow_addr (frame_addr ly 4 pos) <= a < shadow_addr (frame_addr ly 4 pos) + 128 ->
awr_byte STK sp0 FP bl0 blc ly own a.
Proof.
intros STK sp0 FP bl0 blc ly own pos a Hown Ha. right; right; right. exists 4, pos. split; [exact Hown|]. right.
unfold in_zr; cbn [fst snd]. change (fs_frame_bytes 4 / 8) with 128. lia.
Qed.
Lemma rtsb_awr_stk : forall STK sp0 FP bl0 blc ly own a, sp0 - STK <= a < sp0 -> awr_byte STK sp0 FP bl0 blc ly own a.
Proof. intros STK sp0 FP bl0 blc ly own a Ha. left. exact Ha. Qed.
Lemma rtsb_awr_ok_fsh : forall E r rs STK sp0 FP bl0 blc ly own (kreg : nat) pos,
YP09.r_base r = Some kreg -> bv_unsigned (ew E kreg) = shadow_addr (frame_addr ly 4 pos) -> In (4, pos) own ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= 128 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own kreg pos Hb Hk Hown Hlo Hhi Hrs.
apply (awr_ok_cons_gen E r rs STK sp0 FP bl0 blc ly own kreg _ Hb Hk); [|exact Hrs].
intros a Ha. apply (rtsb_awr_fsh STK sp0 FP bl0 blc ly own pos a Hown). lia.
Qed.
Lemma rtsb_awr_ok_fobj : forall E r rs STK sp0 FP bl0 blc ly own (kreg : nat) pos off,
YP09.r_base r = Some kreg -> bv_unsigned (ew E kreg) = frame_addr ly 4 pos + off -> In (4, pos) own ->
0 <= off + YP09.r_wlo r -> off + YP09.r_whi r <= 1024 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own kreg pos off Hb Hk Hown Hlo Hhi Hrs.
apply (awr_ok_cons_gen E r rs STK sp0 FP bl0 blc ly own kreg _ Hb Hk); [|exact Hrs].
intros a Ha. apply (rtsb_awr_fobj STK sp0 FP bl0 blc ly own pos a Hown). lia.
Qed.

(* ---- (e) the call of any leaf runtime routine whose contract has the kernel's ecall form (the strlen and strcmp
   wrappers 0x421ec / 0x421f4, the bcmp wrapper 0x42200, the intrinsics): from the caller's state at the routine's
   entry, the routine returns to ra with the runtime invariant AR at the same layout and state, the callee-saved
   registers kept, same_but_materialized, a result Q, and every byte outside its own writes Wd and its stack
   window [sp - T, sp) kept. rtsb_ecall_at carries that post under the caller's journal; rtsb_ecall_seq chains it
   after a block, as rtsb_intrin_seq does. ---- *)
Section c4. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d4.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws rsegs B.
Definition rtsb_ecall_post (lyc : alayout) (Sc : astate) (W : world rsegs) (regsT : bvmap 5 word)
(memT : word -> option byte) (mdc : Model) (T : Z) (Wd : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = cfg_at rsegs (raZ regsT) regs2 mem2 md2 /\
AR rsegs B lyc Sc W mem2 md2 /\ aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ Q regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wd a -> ~ (spZ regsT - T <= a < spZ regsT) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
(* the caller's stack window gives the routine's: its bottom above the stack's lowest address, every byte present *)
Lemma rtsb_stk_window : forall STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc (o T : Z),
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
Lemma rtsb_ecall_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o T : Z) raw
  (Wd : Z -> Prop) (Q : bvmap 5 word -> (word -> option byte) -> Prop) pc,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o <= 0 -> T - o <= STK -> getr regsT 1 = raw ->
(forall a, Wd a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc) (rtsb_ecall_post lyc Sc W regsT memT mdc T Wd Q) ->
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
{ eapply (ajournal_after_write rsegs B LAWS rtsb_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
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
Lemma rtsb_ecall_seq : forall pcC retpc STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob (Wr : Z -> Prop)
  (R1 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) (o T : Z) (Wd : Z -> Prop)
  (Q : bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pcC clob Wr R1) ->
(forall ly1 S1 W1 regs1 mem1 md1,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k -> R1 W1 regs1 mem1 ->
  spZ regs1 = sp0 + o /\ getr regs1 1 = w64 retpc /\
  (forall a, Wd a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B ly1 S1) ly1 own a) /\
  SRr rsegs W1 (cfg_at rsegs pcC regs1 mem1 md1) (rtsb_ecall_post ly1 S1 W1 regs1 mem1 md1 T Wd Q)) ->
o <= 0 -> T - o <= STK ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc (clob ++ rtsb_caller_saved)
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
{ exact (rtsb_ecall_at W1 regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own ly1 S1 md1 k o T (w64 retpc) Wd Q pcC
    HJ1 Hsp Hneg Hbud Hra HWd HC). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsame & HQ & Hfr).
exists ly1, S1, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros r Hr0 Hn'. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  rewrite (HP (bv_unsigned r) (rtsb_callee r Hr0 ltac:(intros X; apply Hn'; apply in_or_app; right; exact X))).
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

(* ============================== PART 5. the pod_write_ent call adapter (B only) ==============================
   Image B keeps pod_write_ent(pp, e) out of line at 0x83cc4 and calls it where image A inlines it: 0x81054
   (pod.h:404, the shape-7 Int pod e at F + 0xf0), 0x82108 (pod.h:430, the count loop's e62 at F + 0x210, after
   the capacity guard `bltu a1,a0` 0x820fc) and 0x82404 (pod.h:416, the Int-7 value e42 at F + 0x180). At all
   three a0 = pp is `ld a0,0x168(s1)` and a1 is the object's address.
   Its contract is lib/AU/PweSpec.v's pod_write_ent_specX: a plain callee contract (no side-stack frame), whose
   post is pw_post with the float state kept, E = pwe_E pp len e and T = T_pwe_STK = 48 + ESTACK. rtsb_pwe_post
   is that post's text, so a walk lane discharges the hypothesis of rtsb_pwe_at with the contract itself.
   rtsb_pwe_at turns it into the rtsb_post shape at the return pc (clobbering the caller-saved registers, writing
   pwe_E and the callee's stack window); rtsb_pwe_seq chains it after a block that stops at 0x83cc4 with ra = the
   return pc, as rtsb_intrin_seq does for the intrinsics.
   rtsb_pwe_site collects the premises the contract asks of the object e at F + off from what a walk lane has:
   the class-4 frame (F mod 32 = 0, in_app F 1024), the object's offset and the lane's shadow facts over it
   (RtPgMemB's rtmb_B_ra_e / _e42 / _e62 give the range_addressable and the hull), the record's well-formedness
   (Pod/Model ent_wf, which gives pwe_len e <= 56 and the three e_* premises) and the build invariant's len. *)
Definition PWE_ENT : Z := 0x83cc4.
Definition PWE_OFF_E : Z := 0xf0.
Definition PWE_OFF_E42 : Z := 0x180.
Definition PWE_OFF_E62 : Z := 0x210.
Definition PWE_RA_SHAPE7 : Z := 0x81058.
Definition PWE_RA_COUNT : Z := 0x8210c.
Definition PWE_RA_INT7 : Z := 0x82408.

(* n = |enc_pod e| is at most 56 and the three e_* premises, from Pod/Model's ent_wf *)
Lemma rtsb_pwe_len_of_wf : forall e, Model.ent_wf e ->
0 <= pwe_len e <= 56 /\ Z.of_nat (length (Model.e_body e)) = Model.e_size e /\
Model.e_size e <= Layout.ENT_SIZE - 8 /\ 0 <= Model.e_type e < 2 ^ 32.
Proof.
intros e He. pose proof (Model.enc_pod_len_bound e He) as [Hle _].
destruct He as (Ht & Hb & Hs). unfold pwe_len.
split; [split; [lia | exact Hle]|].
split; [rewrite Hb; apply Z2Nat.id; lia|].
split; [unfold Layout.ENT_SIZE; lia | exact Ht].
Qed.
(* the two ways a call site bounds len + n: the build invariant len <= 5440, or the capacity guard at 0x820fc *)
Lemma rtsb_pwe_len_small : forall len e, 0 <= len -> len <= 5440 -> Model.ent_wf e ->
len + pwe_len e <= Layout.POD_BUF_MAX.
Proof.
intros len e H0 H1 He. destruct (rtsb_pwe_len_of_wf e He) as [[Hn0 Hn1] _].
unfold Layout.POD_BUF_MAX. lia.
Qed.
Lemma rtsb_pwe_len_guard : forall len e, 0 <= len -> len + 112 <= Layout.POD_BUF_MAX -> Model.ent_wf e ->
len + pwe_len e <= Layout.POD_BUF_MAX.
Proof.
intros len e H0 H1 He. destruct (rtsb_pwe_len_of_wf e He) as [[Hn0 Hn1] _].
unfold Layout.POD_BUF_MAX in *. lia.
Qed.

Section c5. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* the object premises of the contract at a frame object F + off, and the two separations *)
Lemma rtsb_pwe_site : forall F off q pp (sp : Z),
F mod 32 = 0 -> in_app F 1024 -> q = F + off -> 0 <= off -> off mod 8 = 0 ->
off + Layout.ENT_SIZE < 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) ->
(F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= q /\ q mod 8 = 0 /\ amem_range q Layout.ENT_SIZE /\
(pp + Layout.PP_SIZE <= q \/ q + Layout.ENT_SIZE <= pp) /\
(q + Layout.ENT_SIZE <= sp - T_pwe_STK \/ sp <= q).
Proof.
intros F off q pp sp Hm Ha -> Ho0 Ho8 Hoff Hpp Hsp.
destruct (rtsb_fbounds F Hm Ha) as (H4096 & Hceil & _ & _ & _ & Hamr).
assert (Hq8 : (F + off) mod 8 = 0).
{ destruct (rtsb_fdiv F Hm) as [E1 _]. pose proof (Z.div_mod off 8 ltac:(lia)) as Eo.
  rewrite Ho8, Z.add_0_r in Eo. rewrite E1, Eo.
  replace (32 * (F / 32) + 8 * (off / 8)) with ((4 * (F / 32) + off / 8) * 8) by ring. apply Z_mod_mult. }
split; [lia|]. split; [exact Hq8|].
split; [apply Hamr; [lia | unfold Layout.ENT_SIZE; lia | unfold Layout.ENT_SIZE in *; lia]|].
split; [unfold Layout.PP_SIZE, Layout.ENT_SIZE in *; lia|].
unfold Layout.ENT_SIZE in *. lia.
Qed.

(* The premises pod_write_ent_specX asks of the object and of len, at each of image B's three call sites.
   The caller supplies the frame's geometry (the class-4 law), the heap block's and the callee stack's
   separation from the frame, the build invariant's len, and the record's well-formedness; the lemma does the
   offset arithmetic and the length bound. The pp premises are PweSpec's own pwe_pp_of_block and
   pwe_awr_fresh, and the shadow premises of the object are RtPgMemB's rtmb_B_ra_e / _e42 / _e62. *)
Definition rtsb_pwe_site_concl (F off pp sp len : Z) (e : Model.ent) : Prop :=
0 <= F + off /\ (F + off) mod 8 = 0 /\ amem_range (F + off) Layout.ENT_SIZE /\
(pp + Layout.PP_SIZE <= F + off \/ F + off + Layout.ENT_SIZE <= pp) /\
(F + off + Layout.ENT_SIZE <= sp - T_pwe_STK \/ sp <= F + off) /\
len + pwe_len e <= Layout.POD_BUF_MAX /\
Z.of_nat (length (Model.e_body e)) = Model.e_size e /\ Model.e_size e <= Layout.ENT_SIZE - 8 /\
0 <= Model.e_type e < 2 ^ 32.
Lemma rtsb_pwe_site_of : forall F off pp sp len e,
F mod 32 = 0 -> in_app F 1024 -> 0 <= off -> off mod 8 = 0 -> off + Layout.ENT_SIZE < 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
Model.ent_wf e -> len + pwe_len e <= Layout.POD_BUF_MAX ->
rtsb_pwe_site_concl F off pp sp len e.
Proof.
intros F off pp sp len e Hm Ha Ho0 Ho8 Hoff Hpp Hsp He Hlen.
destruct (rtsb_pwe_site F off (F + off) pp sp Hm Ha eq_refl Ho0 Ho8 Hoff Hpp Hsp)
  as (Hq0 & Hq8 & Hamr & Hsep1 & Hsep2).
destruct (rtsb_pwe_len_of_wf e He) as (_ & Hb & Hs & Ht).
unfold rtsb_pwe_site_concl.
repeat (split; [assumption|]). exact Ht.
Qed.
(* 0x81054 (pod.h:404): the shape-7 Int pod e at F + 0xf0; len <= 5440 from the build invariant *)
Lemma rtsb_pwe_site_81054 : forall F pp sp len e,
F mod 32 = 0 -> in_app F 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= len -> len <= 5440 -> Model.ent_wf e ->
rtsb_pwe_site_concl F PWE_OFF_E pp sp len e.
Proof.
intros F pp sp len e Hm Ha Hpp Hsp Hl0 Hl1 He.
apply rtsb_pwe_site_of; try assumption.
- unfold PWE_OFF_E; lia.
- unfold PWE_OFF_E; reflexivity.
- unfold PWE_OFF_E, Layout.ENT_SIZE; lia.
- exact (rtsb_pwe_len_small len e Hl0 Hl1 He).
Qed.
(* 0x82108 (pod.h:430): the count loop's e62 at F + 0x210; the capacity guard `bltu a1,a0` 0x820fc gives
   len + 112 <= 16384 on the arm that calls *)
Lemma rtsb_pwe_site_82108 : forall F pp sp len e,
F mod 32 = 0 -> in_app F 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= len -> len + 112 <= Layout.POD_BUF_MAX -> Model.ent_wf e ->
rtsb_pwe_site_concl F PWE_OFF_E62 pp sp len e.
Proof.
intros F pp sp len e Hm Ha Hpp Hsp Hl0 Hl1 He.
apply rtsb_pwe_site_of; try assumption.
- unfold PWE_OFF_E62; lia.
- unfold PWE_OFF_E62; reflexivity.
- unfold PWE_OFF_E62, Layout.ENT_SIZE; lia.
- exact (rtsb_pwe_len_guard len e Hl0 Hl1 He).
Qed.
(* 0x82404 (pod.h:416): the Int-7 value e42 at F + 0x180; len <= 5440 from the build invariant *)
Lemma rtsb_pwe_site_82404 : forall F pp sp len e,
F mod 32 = 0 -> in_app F 1024 ->
(pp + Layout.PP_SIZE <= F \/ F + 1024 <= pp) -> (F + 1024 <= sp - T_pwe_STK \/ sp <= F) ->
0 <= len -> len <= 5440 -> Model.ent_wf e ->
rtsb_pwe_site_concl F PWE_OFF_E42 pp sp len e.
Proof.
intros F pp sp len e Hm Ha Hpp Hsp Hl0 Hl1 He.
apply rtsb_pwe_site_of; try assumption.
- unfold PWE_OFF_E42; lia.
- unfold PWE_OFF_E42; reflexivity.
- unfold PWE_OFF_E42, Layout.ENT_SIZE; lia.
- exact (rtsb_pwe_len_small len e Hl0 Hl1 He).
Qed.

Context {SK : YI16.sink_head}.
Section d5.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* lib/AU/PweSpec.v's pw_post at this unit's call sites, word for word: the hypothesis of rtsb_pwe_at is what
   pod_write_ent_specX concludes, so a walk lane passes the contract itself. *)
Definition rtsb_pwe_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model)
(pp len : Z) (e : Model.ent) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
: world rsegs -> config -> Prop :=
fun W2 c2 => exists (fx2 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx2 regs2 (getr regs 1) mem2 (seg_rom rsegs)) md2 /\ (fun f => f = fx) fx2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_pwe_STK <= a < spZ regs) -> ~ pwe_E pp len e a ->
aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.
(* the call as one block from 0x83cc4 to the return pc *)
Lemma rtsb_pwe_at : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (pp len retpc o : Z)
  (e : Model.ent) (R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
getr regs 1 = w64 retpc -> spZ regs = sp0 + o ->
SRr rsegs W (cfg_at rsegs PWE_ENT regs memc mdc)
  (rtsb_pwe_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pp len e R) ->
SRr rsegs W (cfg_at rsegs PWE_ENT regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc rtsb_caller_saved
    (fun a => pwe_E pp len e a \/ (sp0 + o - T_pwe_STK <= a < sp0 + o)) R).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pp len retpc o e R Hra Hsp HC.
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & -> & HJ2 & HP & Hf & Hp & Hio & Hmo & Hkept & HR).
rewrite Hsp in Hkept.
exists ly2, S2, regs2, mem2, md2.
split; [rewrite Hra; reflexivity|].
split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite <- (Z_to_bv_bv_unsigned 5 r).
  rewrite (HP (bv_unsigned r) (rtsb_callee r Hr0 Hn)). rewrite Z_to_bv_bv_unsigned. reflexivity. }
split; [exact Hf|]. split; [exact Hp|]. split; [exact Hio|]. split; [exact Hmo|].
split.
{ intros a Ha Hn. apply Hkept; [exact Ha | intros X; apply Hn; right; exact X | intros X; apply Hn; left; exact X]. }
exact HR.
Qed.
(* a block that stops at 0x83cc4 with ra = retpc, then the call: one block to retpc *)
Lemma rtsb_pwe_seq : forall STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob (Wr : Z -> Prop)
  (R1 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) (pp len retpc o : Z) (e : Model.ent)
  (R2 : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop),
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc PWE_ENT clob Wr R1) ->
(forall ly1 S1 W1 regs1 mem1 md1,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly1 S1 W1 mem1 md1 k -> R1 W1 regs1 mem1 ->
  getr regs1 1 = w64 retpc /\ spZ regs1 = sp0 + o /\
  SRr rsegs W1 (cfg_at rsegs PWE_ENT regs1 mem1 md1)
    (rtsb_pwe_post STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pp len e R2)) ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
  (rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc retpc (clob ++ rtsb_caller_saved)
    (fun a => Wr a \/ pwe_E pp len e a \/ (sp0 + o - T_pwe_STK <= a < sp0 + o)) R2).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc0 clob Wr R1 pp len retpc o e R2 H1 Hpre.
eapply SRr_bind; [exact H1|].
intros W1 c1 _ (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & Hr1 & Hf1 & Hp1 & Hio1 & Hmo1 & Hm1 & HR1).
destruct (Hpre ly1 S1 W1 regs1 mem1 md1 HJ1 HR1) as (Hra & Hsp & HC).
eapply SRr_mono.
{ exact (rtsb_pwe_at STK sp0 FP ly S W0 mem0 md0 own k regs1 ly1 S1 W1 mem1 md1 pp len retpc o e R2 Hra Hsp HC). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hr2 & Hf2 & Hp2 & Hio2 & Hmo2 & Hm2 & HR2).
exists ly2, S2, regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|].
split.
{ intros r Hr0 Hn. rewrite (Hr2 r Hr0 ltac:(intros X; apply Hn; apply in_or_app; right; exact X)).
  apply Hr1; [exact Hr0 | intros X; apply Hn; apply in_or_app; left; exact X]. }
split; [rewrite Hf2; exact Hf1|].
split; [eapply Permutation_trans; [exact Hp2 | exact Hp1]|].
split; [eapply same_io_trans; [exact Hio1 | exact Hio2]|].
split; [exact (mle_station MT Sc S1 S2 0 0 MTL Hmo1 Hmo2)|].
split.
{ intros a Ha Hn.
  rewrite (Hm2 a Ha ltac:(intros X; apply Hn; destruct X as [X|X]; [right; left; exact X | right; right; exact X])).
  apply Hm1; [exact Ha | intros X; apply Hn; left; exact X]. }
exact HR2.
Qed.
End d5.
End c5.

Print Assumptions rtsb_u32_block2.
Print Assumptions rtsb_u32_block3.
Print Assumptions rtsb_post_seq.
Print Assumptions rtsb_blk_seq.
Print Assumptions rtsb_intrin_seq.
Print Assumptions rtsb_ecall_seq.
Print Assumptions rtsb_stk_window.
Print Assumptions rtsb_fbounds.
Print Assumptions rtsb_awr_ok_fsh.
Print Assumptions rtsb_awr_ok_fobj.
Print Assumptions rtsb_pwe_at.
Print Assumptions rtsb_pwe_site.
Print Assumptions rtsb_pwe_len_of_wf.
Print Assumptions rtsb_pwe_seq.
Print Assumptions rtsb_trap_80c00.
Print Assumptions rtsb_trap_826ac.
Print Assumptions rtsb_pwe_site_81054.
Print Assumptions rtsb_pwe_site_82108.
Print Assumptions rtsb_pwe_site_82404.

Print Assumptions rtsb_jt_block.
Print Assumptions rtsb_trap_809c8.
Print Assumptions rtsb_trap_82918.
Print Assumptions rtb_po1.
Print Assumptions rtb_not_le.
Print Assumptions rtb_ltu_lit.
Print Assumptions rtb_ne_lit.
Print Assumptions rtb_addiw_inc.
Print Assumptions rtb_and7_eq.
Print Assumptions rtb_ne8.
Print Assumptions rtb_shr_small.
