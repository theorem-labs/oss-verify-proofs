(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its module paths and module names changed; 2089 of its 2218 lines of code are new or changed and 5936 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSteps.v at a58a6fc257b (parts 1, 2) and
   a6c23b42ca2 (part 3); ported to
   reac-pw/fuzz_headamp image A: module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec -> HPgBase / HPgCSpec, the
   rl_ prefix -> hd_; every image address relocated from role's image A to headamp's (the jump table 0x20e94 ->
   0x20e9c with its nine entries and targets measured from headamp's pinned bytes, the dispatch block 0x80b1c ->
   0x8183c, the two fuzz_u32 sites 0x80ee4 / 0x81454 -> 0x81c04 / 0x82174 and their ends 0x815e8 / 0x8163c ->
   0x82308 / 0x8235c, the code tables over 0x81c04 .. 0x82360 and 0x825bc .. 0x82838); the input-length cell of the
   two fuzz_u32 sites [s1+0xf8] -> [s1+0x118] (headamp's frame-slot map); img_wx, img_segs_low and same_io_wvb are
   stated here (role took them from its cfg walk file, which headamp has no twin of); part 3 (the scope-store
   sites) restated at headamp's fourteen sites, each measured on image A: role's ten builder sites relocated, role's
   role-object pair replaced by headamp's res and x sites, the run 0x82578 stated with the value it leaves in a1
   (hd_scope_stmtAx, hd_inc_a1, sv_addiw1), role's unused fsh_ss2 dropped, fsh_pts added for the 17-granule x
   sites. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgSteps.v at f9231666453 (parts 1, 2) and
   98dfdeee412 (part 3); the image-B twin
   (fuzz_headamp.asan-ubsan): lib/A/Img0 -> lib/AU/Img0U, the hd_ prefix -> hdu_; part 1 at B's dispatch block
   0x81928 over B's table 0x20ecc (entries and targets measured from B's pinned bytes; B keeps the sign-extended kind
   byte in a3 where A keeps it in s4); part 2 restated at B's registers (cursor s2, c - 2 in a7, bytes left in a2,
   the original in.n in t1, the UBSan constant 1 in a6, the shadow offset in s11) with no frame-slot region (B keeps
   in.n in t1 where A reads the cell [s1+0x118]), at B's two sites 0x82390 / 0x823cc with their ends 0x82574 /
   0x825f8 and B's code tables; the generic helpers, the value lemmas and the five-arm proof shape unchanged; part 3
   at B's eighteen scope-store sites, each measured on image B (B's three e objects e, e42, e62 give six e sites; the
   r sites store t0 and s7, stated with hdu_scope_stmtR; four runs also set s7 := -8 and one sets a1 := a1 + 1, stated
   with hdu_scope_stmtAx and hdu_s7_m8 / hdu_inc_a1 / hdu_inc_a1_s7), the generic lemmas as A's. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on its unstripped
   twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded bytes at these addresses
   equal the pin's): the step kit of the image-B walk of LLVMFuzzerTestOneInput (0x80c40, 3215 instructions). Proves
   no function (kind: segment lemma): each lemma is a step or a block of steps the walk lanes of M01 / M02 use, stated
   over the kit's engine (lib/Reusable: st_ok, sh_ok, ajournal, SRr) and image B's segments (lib/AU/Img0U.v rsegs).

   PART 1. THE JUMP TABLE OF ent_build (pod.h:281, `switch (kind % 10)`), the one computed jump of the function:
     0x81920  addi a2,zero,8 / 0x81924 bltu a2,a1 -> 0x82004   k = kind % 10 = 9 goes to case 9 without the table
     0x81928  slli a1,a1,2
     0x8192c  auipc a2,0xfff9f / 0x81930 addi a2,a2,0x5a0      a2 = 0x20ecc, the table (.rodata, read-only)
     0x81934  add a1,a1,a2 / 0x81938 lw a1,0(a1)             the entry of k (a 32-bit offset from the table)
     0x8193c  slli a0,a0,0x38 / 0x81944 srai a3,a0,0x38        a3 = the kind byte, sign-extended
     0x81940  add a1,a1,a2
     0x81948  jr a1                                             to 0x20ecc + entry k
   The nine entries, read from the pinned file (PT_LOAD R [0x10000, 0x2f764)): 0x60a80 0x60f38 0x60df0 0x60e68
   0x60d9c 0x60fa0 0x6103c 0x60ebc 0x61090, so the targets are 0x8194c (case 0) 0x81e04 (1) 0x81cbc (2) 0x81d34 (3)
   0x81c68 (4) 0x81e6c (5) 0x81f08 (6) 0x81d88 (7) 0x81f5c (8). The `lw` carries no instrumented check and the block
   no UBSan trap branch.
   The engine (YP0l sym_step) follows `jr` when the register is a literal and loads a literal from an image chunk
   (YP09 CImg) of a base-free region at a literal address. So the step is: the table as the read-only region
   jt_region (one CImg chunk of 36 bytes), proved from rom_view (jt_region_ok); k split into its nine values
   (jt_cases); the register of k pinned to the literal. hdu_jt_block is that step at the concrete site, as a block
   lemma in the shape of a callee contract (hdu_blk_post): from 0x81928 with a1 = k, 0 <= k <= 8, to 0x20ecc + entry k
   with a1, a2, a0, a3 set and every other register, the journal and every byte as before. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== image B's segments ======================================== *)
(* the image's writable segments do not wrap and every loaded byte lies below the shadow's low end (the two facts
   the engine's table lemmas ask for) *)
Lemma img_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma img_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.
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
Definition JT_A : Z := 0x20ecc.
Definition JT_PC : Z := 0x81928.
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
[0x8194c; 0x81e04; 0x81cbc; 0x81d34; 0x81c68; 0x81e6c; 0x81f08; 0x81d88; 0x81f5c].
Proof. vm_compute. reflexivity. Qed.
Lemma jt_tgt_vals : jt_tgt 0 = 0x8194c /\ jt_tgt 1 = 0x81e04 /\ jt_tgt 2 = 0x81cbc /\ jt_tgt 3 = 0x81d34 /\
jt_tgt 4 = 0x81c68 /\ jt_tgt 5 = 0x81e6c /\ jt_tgt 6 = 0x81f08 /\ jt_tgt 7 = 0x81d88 /\ jt_tgt 8 = 0x81f5c.
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
(* as regs_kept_of_st_ok, but some registers are pinned to an sv of the entry's value (s7 to the shadow-base atom) *)
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
Definition hdu_blk_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
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

(* ---- the dispatch block 0x81928 .. 0x81948 ---- *)
Definition jt_tbl : ctable := build_table rsegs JT_PC 9 TEmpty.
Lemma jt_tbl_ok : table_ok rsegs jt_tbl.
Proof. apply build_table_ok0. unfold JT_PC. lia. Qed.
Definition SBr : Z := 0x7fff8000.
Definition RTBx : sv := SOff 32 0.
Definition RTBspan : Z * Z := (SBr, SBr + 2 ^ 44 - 1).
Definition rt_extra : list word := [Z_to_bv 64 SBr].
Definition jt_R (kk : Z) (regs regs2 : bvmap 5 word) : Prop :=
getr regs2 11 = w64 (jt_tgt kk) /\ getr regs2 12 = w64 JT_A /\
bv_unsigned (getr regs2 10) = (bv_unsigned (getr regs 10) mod 256) * 2 ^ 56 /\
getr regs2 13 = w64 (sext8 (bv_unsigned (getr regs 10) mod 256)).
Lemma hdu_jt_block : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (kk : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
0 <= kk <= 8 -> getr regs 11 = w64 kk -> rom_view rsegs W memc ->
SRr rsegs W (cfg_at rsegs JT_PC regs memc mdc)
(hdu_blk_post STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc (jt_tgt kk) [10; 11; 12; 13]%bv (jt_R kk regs)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs kk HJ Hk H11 HR.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
assert (HS0 : st_ok rsegs (Ereg regs rt_extra) (mkSS JT_PC sr_atoms [jt_region] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 JT_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [apply jt_region_ok; exact HR | constructor].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (11%bv : bv 5) kk HS0 eq_refl H11) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs RTBx [] (Ereg regs rt_extra) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs rt_extra) (Ereg regs rt_extra)) by apply env_agree_refl.
assert (E10 : ew (Ereg regs rt_extra) 10 = Z_to_bv 64 (bv_unsigned (getr regs 10)))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (u64_range (getr regs 10)) as Hu10.
unfold cfg_at. change (w64 JT_PC) with (Z_to_bv 64 JT_PC).
destruct (jt_cases kk Hk) as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
(lazymatch goal with |- context [jt_tgt ?t] => let st := eval vm_compute in (jt_tgt t) in
   aj_run_to_tok jt_tbl_ok HS HJ SHOK RTBspan st end;
 [ awr_ok_tac
 | apply SRr_ret;
   lazymatch type of HS with st_ok _ _ ?ssf _ =>
     let t := eval vm_compute in (ss_pc ssf) in
     replace (jt_tgt _) with t by (vm_compute; reflexivity) end;
   red; exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc);
   split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
   split; [exact HJ|];
   split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs rt_extra (w_H W) _ HS HAE); vm_compute; reflexivity|];
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
       let e13 := eval vm_compute in (sr_get (ss_regs ssf) (13%bv : bv 5)) in
       change (sr_get (ss_regs ssf) (10%bv : bv 5)) with e10;
       change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e11;
       change (sr_get (ss_regs ssf) (12%bv : bv 5)) with e12;
       change (sr_get (ss_regs ssf) (13%bv : bv 5)) with e13 end;
     split; [unfold w64; f_equal; vm_compute; reflexivity|];
     split; [unfold w64; f_equal; vm_compute; reflexivity|];
     split;
     [ change (bv_unsigned (sv_denot (Ereg regs rt_extra) (SAlu ALU_SLL (SOff 10 0) (SLit 56))))
         with (U (Ereg regs rt_extra) (SAlu ALU_SLL (SOff 10 0) (SLit 56)));
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
   Both read up to four input bytes and test the ORIGINAL in.n (t1) against 3 and the bytes left after two reads
   (t1 - 4) against 0 and 1 to decide how many are there; so the length split is inside ONE lemma per site.
     site 2  0x82390 `beqz a2,0x82484` ... join 0x82564 .. end 0x82574 (the pc after `or a1,a1,a4`); the four-byte
             arm 0x82710 .. 0x8273c, the slow blocks 0x8288c 0x828a4 0x828bc 0x828d4 (+ 3 insns each)
     site 3  0x823cc `beqz a2,0x82490` ... join 0x825e8 .. end 0x825f8; the four-byte arm 0x82740 .. 0x8276c, the
             slow blocks 0x82898 0x828b0 0x828c8 0x828e0
   The walk reaches site 2 at 0x8238c (`ld s4,0x130(s1)`, a frame-slot load the walk steps itself) and site 3 at
   0x823cc. At the start: a2 = n1 (bytes left), s2 = c (the cursor), a7 = c - 2, t1 = n1 + 2, a6 = 1, s11 = K; no
   store inside; before each read a UBSan pointer-overflow test `addi t,s2,1; bltu a6,t` whose trap arm (`j` to the
   `unimp` 0x83a14) the cursor bound rules out; the four shadow checks are the `bnez t,L` form, so the token engine
   (YCbn tok_load / tok_branch) takes both outcomes itself and leaves one obligation `range_addressable ... (c + i) 1`
   per read.
   The five arms (n1 = 0, 1, 2, 3, >= 4) are the five ways out; in the first four n1 and n1 + 2 are literals and the
   engine decides every test itself, in the fifth the atom facts 4 <= n1 and 6 <= n1 + 2 decide them. *)

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
(* the input bytes [c, c + m), as chunks at offsets 2 .. m + 1 of the region based on a7 = c - 2 (B keeps in.n in t1, so
   no frame cell is read and the input region is the only one; none when nothing is left) *)
Definition u32_in_region (m : nat) : YP09.region :=
  YP09.mkRegion (Some 17%nat) 2 (2 + Z.of_nat m) 0 0 (u32_bchunks m).
Definition u32_regs_of (m : nat) : smem :=
  match m with O => [] | S _ => [u32_in_region m] end.
(* s2 = a7 + 2, s11 = the shadow offset atom, a6 = 1, t1 = n1 + 2 (t1v), a2 = n1 (a2v) *)
Definition u32_ss (pc : Z) (a2v t1v : sv) (m : nat) (G : facts) : sstate :=
mkSS pc (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (18%bv : bv 5) (SOff 17 2)) (27%bv : bv 5) (SOff 32 0))
  (16%bv : bv 5) (SLit 1)) (6%bv : bv 5) t1v) (12%bv : bv 5) a2v)
  (u32_regs_of m) None G.
(* The cursor atom's bound is a CLOSED numeral per arm, never a term in c: the engine's run is a vm_compute, and a
   free variable inside a fact makes every decision of sym_step_tok stick and the run blow up (measured on image A:
   the file did not compile in 30 min, where the closed form takes 20 s).
   The arm that reads k bytes uses offsets 2 .. k + 1, and the engine's ob_in_span asks
   SHADOW_OFF + (hi + off) / 8 <= SHADOW_OFF + 2 ^ 44 - 1, so hi <= 2 ^ 47 - 1 - (k + 1) - 2 is enough; amem_range's
   c + n1 <= kHighMemEnd - 1 = 2 ^ 47 - 1 gives exactly c - 2 <= 2 ^ 47 - 1 - k - 2 in that arm: the five numerals
   are 140737488355325 (k = 0), ...324, ...323, ...322 and ...321 (the arm that reads four bytes). The same bound
   and 1 <= c - 2 decide each UBSan test 1 <u c + i + 1. *)
Definition u32_facts0 (hi : Z) : facts :=
  mkFacts [ (17%nat, mkAF 1 hi 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition u32_factsF (hi : Z) : facts :=
  mkFacts [ (17%nat, mkAF 1 hi 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (37%nat, mkAF 4 140737488355327 0); (38%nat, mkAF 6 140737488355329 0) ] [] [].
Lemma u32_regions_wf : forall m, (m <= 4)%nat -> regions_wf (u32_regs_of m) = true.
Proof.
intros m Hm. destruct m as [|[|[|[|[|m]]]]]; try (exfalso; lia); vm_compute; reflexivity.
Qed.
Lemma u32_inreg_ok : forall E (W : world rsegs) mem c (m : nat) (rest : list byte),
ew E 17 = Z_to_bv 64 (c - 2) ->
(forall i, (i < 4)%nat -> ew E (33 + i) = Z_to_bv 64 (u32_b rest i)) ->
(m <= length rest)%nat -> (m <= 4)%nat -> 0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 ->
garr8 rsegs (mrestrict (w_H W) mem) c (map (fun x : byte => bv_unsigned x) rest) ->
region_ok rsegs E (mrestrict (w_H W) mem) (u32_in_region m).
Proof.
intros E W mem c m rest E17 Eb Hm1 Hm2 Hc0 Hc1 Hg. unfold region_ok, u32_in_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E17, unsigned_lit_small by lia.
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
  a2v t1v G pc,
getr regs 16 = w64 1 -> getr regs 17 = w64 (c - 2) -> getr regs 18 = w64 c -> getr regs 27 = w64 SHADOW_OFF ->
sv_denot (Ereg regs (u32_extra rest left nn)) a2v = getr regs 12 ->
sv_denot (Ereg regs (u32_extra rest left nn)) t1v = getr regs 6 ->
0 < c - 2 -> c + Z.of_nat (length rest) <= 140737488355327 -> (m <= length rest)%nat -> (m <= 4)%nat ->
garr8 rsegs (mrestrict (w_H W) memc) c (map (fun x : byte => bv_unsigned x) rest) ->
facts_ok (Ereg regs (u32_extra rest left nn)) G -> 0 <= pc ->
st_ok rsegs (Ereg regs (u32_extra rest left nn)) (u32_ss pc a2v t1v m G)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros regs W memc c nn left m rest a2v t1v G pc H16 H17 H18 H27 Ha2 Ht1 Hc0 Hc1 Hm1 Hm2 Hg HG Hpc.
unfold w64 in H16, H17, H18, H27.
set (E := Ereg regs (u32_extra rest left nn)) in *.
assert (E17 : ew E 17 = Z_to_bv 64 (c - 2)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
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
  - unfold u32_regs_of; destruct m as [|m']; [apply Forall_nil|].
    apply Forall_cons; [|apply Forall_nil].
    apply (u32_inreg_ok _ W memc c (S m') rest E17 Eb Hm1 Hm2 Hc0 Hc1 Hg).
  - unfold u32_regs_of; destruct m as [|m']; cbn [pairwise_disjoint all_disjoint]; tauto.
  - exact HG. }
pose proof (st_ok_pin_sv rsegs E _ _ (18%bv : bv 5) (SOff 17 2) HS0 eq_refl
  ltac:(cbn [ms_regs mkst sv_denot]; rewrite E17, unsigned_lit_small by lia; rewrite H18; f_equal; lia)) as HS1.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
pose proof (st_ok_pin_sv rsegs E _ _ (27%bv : bv 5) (SOff 32 0) HS1 eq_refl
  ltac:(cbn [ms_regs mkst sv_denot]; subst E; rewrite (ew_Ereg_extra regs _ 0), Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H27))) as HS2.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pin_lit rsegs E _ _ (16%bv : bv 5) 1 HS2 eq_refl ltac:(cbn [ms_regs mkst]; exact H16)) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS3.
pose proof (st_ok_pin_sv rsegs E _ _ (6%bv : bv 5) t1v HS3 eq_refl ltac:(cbn [ms_regs mkst]; exact Ht1)) as HS4.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS4.
pose proof (st_ok_pin_sv rsegs E _ _ (12%bv : bv 5) a2v HS4 eq_refl ltac:(cbn [ms_regs mkst]; exact Ha2)) as HS5.
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
Lemma u32_facts0_ok : forall regs rest left nn c hi,
getr regs 17 = Z_to_bv 64 (c - 2) -> 0 < c - 2 -> c - 2 <= hi -> hi <= 140737488355325 ->
facts_ok (Ereg regs (u32_extra rest left nn)) (u32_facts0 hi).
Proof.
intros regs rest left nn c hi H17 Hc0 Hc1 Hhi.
assert (E17 : ew (Ereg regs (u32_extra rest left nn)) 17 = Z_to_bv 64 (c - 2))
  by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
pose proof shadow_off_range as Hso.
pose proof (Nat2Z.is_nonneg (length rest)) as Hl0.
split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok u32_facts0]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E17, E32, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
Lemma u32_factsF_ok : forall regs rest left nn c hi,
getr regs 17 = Z_to_bv 64 (c - 2) -> 0 < c - 2 -> c - 2 <= hi -> hi <= 140737488355325 ->
4 <= left -> left <= 140737488355327 -> nn = left + 2 -> left = Z.of_nat (length rest) ->
facts_ok (Ereg regs (u32_extra rest left nn)) (u32_factsF hi).
Proof.
intros regs rest left nn c hi H17 Hc0 Hc1 Hhi Hl4 Hlhi Hnn Hleft.
assert (E17 : ew (Ereg regs (u32_extra rest left nn)) 17 = Z_to_bv 64 (c - 2))
  by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF) by exact (ew_Ereg_extra regs _ 0).
assert (E37 : ew (Ereg regs (u32_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5).
assert (E38 : ew (Ereg regs (u32_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6).
pose proof shadow_off_range as Hso.
split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok u32_factsF]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E17, E32, E37, E38, !unsigned_lit_small by lia. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.
End u32f.

Ltac u32_sv HSx :=
  lazymatch goal with |- getr _ _ = _ => rewrite (st_ok_restrict_reg rsegs _ _ _ _ _ HSx) | _ => idtac end;
  match goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
Ltac u32_obl E32x E17x Hrax :=
  try unfold ob_holds; try unfold U32Bx; try cbn [ob_x ob_n];
  rewrite (U_atom _ 32 SHADOW_OFF E32x shadow_off_range);
  first [ rewrite (U_atom_off _ 17 _ 2 E17x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 17 _ 3 E17x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 17 _ 4 E17x ltac:(lia) ltac:(lia))
        | rewrite (U_atom_off _ 17 _ 5 E17x ltac:(lia) ltac:(lia)) ];
  eapply ra_sub; [exact Hrax | lia | lia].
(* pins: s11 to the shadow-offset atom, a6 to 1, t1 to t1v (pintac proves sv_denot _ t1v = getr regs0 6) *)
Ltac u32_leaf regs0 extra0 E32x H27x H16x t1v pintac valtac :=
lazymatch goal with
| HS : st_ok _ ?Ex ?ssf (restrict (w_H ?Wx) ?msx),
  HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lycx ?Scx _ _ _ _,
  HFrx : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  apply SRr_ret;
  red; exists lycx, Scx, (ms_regs msx), (ms_mem msx); eexists;
  split; [rewrite (st_ok_restrict_mkst rsegs (w_H Wx) Ex ssf msx HS eq_refl) at 1; reflexivity|];
  split; [exact HJx|];
  split; [eapply (regs_kept_of_st_ok_pins rsegs Ex ssf msx regs0 extra0 (w_H Wx) _
                   [((27%bv : bv 5), SOff 32 0); ((16%bv : bv 5), SLit 1); ((6%bv : bv 5), t1v)] HS);
          [ split; [intros n0 Hn0; rewrite ?ew_ewset_other by lia; reflexivity | reflexivity]
          | intros rr ee Hin; destruct Hin as [Heq|[Heq|[Heq|[]]]]; inversion Heq; subst;
            cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
            [ rewrite E32x, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H27x)
            | exact (eq_sym H16x)
            | pintac ]
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

(* the code of the two sites: 0x82390 .. 0x8260c (both read-ahead blocks and both joins) and 0x82710 .. 0x828ec (the
   four-byte arms and the slow blocks that the second test of each shadow check jumps to) *)
Definition u32_tbl : ctable := build_table rsegs 0x82710 120 (build_table rsegs 0x82390 160 TEmpty).
Lemma u32_tbl_ok : table_ok rsegs u32_tbl.
Proof. apply build_table_ok; [lia | apply build_table_ok0; lia]. Qed.

(* ---- the two sites, each with its five length arms ---- *)
Section u32b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Definition hdu_u32_stmt (pcA pcB : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (c left nn : Z) (rest : list byte),
left = Z.of_nat (length rest) -> nn = left + 2 ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs 6 = w64 nn -> getr regs 12 = w64 left -> getr regs 16 = w64 1 -> getr regs 17 = w64 (c - 2) ->
getr regs 18 = w64 c -> getr regs 27 = w64 SHADOW_OFF ->
0 < c - 2 -> c + left <= 140737488355327 ->
garr8 rsegs (mrestrict (w_H W) memc) c (map (fun x : byte => bv_unsigned x) rest) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF c left ->
SRr rsegs W (cfg_at rsegs pcA regs memc mdc)
 (hdu_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcB
   [11; 12; 13; 14; 15; 18]%bv
   (fun regs2 => getr regs2 11 = w64 (fst (Cursor.fuzz_u32 rest)) /\
                 getr regs2 12 = w64 (Z.of_nat (length rest - 4)) /\
                 getr regs2 18 = w64 (c + Z.of_nat (Nat.min 4 (length rest))) /\
                 getr regs2 27 = w64 SHADOW_OFF)).
(* case 2 (pod.h:299-301): from `beqz a2` 0x82390 to the pc after `or a1,a1,a4` 0x82574 *)
Lemma hdu_u32_block2 : hdu_u32_stmt 0x82390 0x82574.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c left nn rest
  Hleft Hnn HJ H6 H12 H16 H17 H18 H27 Hc0 Hc1 Hg Hra.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof shadow_off_range as Hso. pose proof (Nat2Z.is_nonneg (length rest)) as Hl0.
unfold w64 in H6, H12, H16, H17, H18, H27.
unfold cfg_at. change (w64 0x82390) with (Z_to_bv 64 0x82390).
destruct (Z_le_gt_dec 4 left) as [HF|Hsm].
{ (* 4 or more bytes left *)
  assert (HlenF : (4 <= length rest)%nat) by lia.
  assert (E17 : ew (Ereg regs (u32_extra rest left nn)) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (E37 : ew (Ereg regs (u32_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5).
  assert (E38 : ew (Ereg regs (u32_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest left nn)) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c nn left 4%nat rest (SOff 37 0) (SOff 38 0) (u32_factsF 140737488355321) 0x82390
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H12))
    ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H6))
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_factsF_ok regs rest left nn c 140737488355321 H17 Hc0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnn Hleft) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest left nn)) (mrestrict (w_H W) memc)) by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x82574;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest left nn) E32 H27 H16 (SOff 38 0)
      ltac:(rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val4 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)))
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E38, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
assert (Hcases : left = 0 \/ left = 1 \/ left = 2 \/ left = 3) by lia.
destruct Hcases as [Hcase|[Hcase|[Hcase|Hcase]]].
{ (* 0 bytes left *)
  assert (HlenK : length rest = 0%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 0 (0 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 0 (0 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 0 (0 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (0 + 2) 0 0%nat rest (SLit 0) (SLit (0 + 2)) (u32_facts0 140737488355325) 0x82390
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 0 (0 + 2) c 140737488355325 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 0 (0 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x82574;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 0 (0 + 2)) E32 H27 H16 (SLit (0 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val0 _ rest ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
{ (* 1 bytes left *)
  assert (HlenK : length rest = 1%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 1 (1 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 1 (1 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 1 (1 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (1 + 2) 1 1%nat rest (SLit 1) (SLit (1 + 2)) (u32_facts0 140737488355324) 0x82390
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 1 (1 + 2) c 140737488355324 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 1 (1 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x82574;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 1 (1 + 2)) E32 H27 H16 (SLit (1 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val1 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
{ (* 2 bytes left *)
  assert (HlenK : length rest = 2%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 2 (2 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 2 (2 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 2 (2 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (2 + 2) 2 2%nat rest (SLit 2) (SLit (2 + 2)) (u32_facts0 140737488355323) 0x82390
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 2 (2 + 2) c 140737488355323 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 2 (2 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x82574;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 2 (2 + 2)) E32 H27 H16 (SLit (2 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val2 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
{ (* 3 bytes left *)
  assert (HlenK : length rest = 3%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 3 (3 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 3 (3 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 3 (3 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (3 + 2) 3 3%nat rest (SLit 3) (SLit (3 + 2)) (u32_facts0 140737488355322) 0x82390
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 3 (3 + 2) c 140737488355322 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 3 (3 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x82574;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 3 (3 + 2)) E32 H27 H16 (SLit (3 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val3 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
Qed.
(* case 3 (pod.h:309-321): from `beqz a2` 0x823cc to the pc after `or a1,a1,a4` 0x825f8 *)
Lemma hdu_u32_block3 : hdu_u32_stmt 0x823cc 0x825f8.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs c left nn rest
  Hleft Hnn HJ H6 H12 H16 H17 H18 H27 Hc0 Hc1 Hg Hra.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof shadow_off_range as Hso. pose proof (Nat2Z.is_nonneg (length rest)) as Hl0.
unfold w64 in H6, H12, H16, H17, H18, H27.
unfold cfg_at. change (w64 0x823cc) with (Z_to_bv 64 0x823cc).
destruct (Z_le_gt_dec 4 left) as [HF|Hsm].
{ (* 4 or more bytes left *)
  assert (HlenF : (4 <= length rest)%nat) by lia.
  assert (E17 : ew (Ereg regs (u32_extra rest left nn)) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest left nn)) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (E37 : ew (Ereg regs (u32_extra rest left nn)) 37 = Z_to_bv 64 left) by exact (ew_Ereg_extra regs _ 5).
  assert (E38 : ew (Ereg regs (u32_extra rest left nn)) 38 = Z_to_bv 64 nn) by exact (ew_Ereg_extra regs _ 6).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest left nn)) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c nn left 4%nat rest (SOff 37 0) (SOff 38 0) (u32_factsF 140737488355321) 0x823cc
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H12))
    ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H6))
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_factsF_ok regs rest left nn c 140737488355321 H17 Hc0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hnn Hleft) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest left nn)) (mrestrict (w_H W) memc)) by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x825f8;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest left nn) E32 H27 H16 (SOff 38 0)
      ltac:(rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val4 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)))
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E38, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
assert (Hcases : left = 0 \/ left = 1 \/ left = 2 \/ left = 3) by lia.
destruct Hcases as [Hcase|[Hcase|[Hcase|Hcase]]].
{ (* 0 bytes left *)
  assert (HlenK : length rest = 0%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 0 (0 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 0 (0 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 0 (0 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (0 + 2) 0 0%nat rest (SLit 0) (SLit (0 + 2)) (u32_facts0 140737488355325) 0x823cc
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 0 (0 + 2) c 140737488355325 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 0 (0 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x825f8;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 0 (0 + 2)) E32 H27 H16 (SLit (0 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val0 _ rest ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
{ (* 1 bytes left *)
  assert (HlenK : length rest = 1%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 1 (1 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 1 (1 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 1 (1 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (1 + 2) 1 1%nat rest (SLit 1) (SLit (1 + 2)) (u32_facts0 140737488355324) 0x823cc
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 1 (1 + 2) c 140737488355324 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 1 (1 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x825f8;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 1 (1 + 2)) E32 H27 H16 (SLit (1 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val1 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
{ (* 2 bytes left *)
  assert (HlenK : length rest = 2%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 2 (2 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 2 (2 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 2 (2 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (2 + 2) 2 2%nat rest (SLit 2) (SLit (2 + 2)) (u32_facts0 140737488355323) 0x823cc
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 2 (2 + 2) c 140737488355323 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 2 (2 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x825f8;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 2 (2 + 2)) E32 H27 H16 (SLit (2 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val2 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
{ (* 3 bytes left *)
  assert (HlenK : length rest = 3%nat) by lia. clear Hleft. subst left. subst nn.
  assert (E17 : ew (Ereg regs (u32_extra rest 3 (3 + 2))) 17 = Z_to_bv 64 (c - 2))
    by (rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E32 : ew (Ereg regs (u32_extra rest 3 (3 + 2))) 32 = Z_to_bv 64 SHADOW_OFF)
    by exact (ew_Ereg_extra regs _ 0).
  assert (Eb : forall i, (i < 4)%nat ->
    ew (Ereg regs (u32_extra rest 3 (3 + 2))) (33 + i) = Z_to_bv 64 (u32_b rest i)).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; try (exfalso; lia);
    [exact (ew_Ereg_extra regs _ 1) | exact (ew_Ereg_extra regs _ 2)
    | exact (ew_Ereg_extra regs _ 3) | exact (ew_Ereg_extra regs _ 4)]. }
  pose proof (u32_entry regs W memc c (3 + 2) 3 3%nat rest (SLit 3) (SLit (3 + 2)) (u32_facts0 140737488355322) 0x823cc
    H16 H17 H18 H27
    ltac:(cbn [sv_denot]; rewrite H12; reflexivity) ltac:(cbn [sv_denot]; rewrite H6; reflexivity)
    Hc0 ltac:(lia) ltac:(lia) ltac:(lia) Hg
    (u32_facts0_ok regs rest 3 (3 + 2) c 140737488355322 H17 Hc0 ltac:(lia) ltac:(lia)) ltac:(lia)) as HS.
  assert (SHOK : sh_ok rsegs U32Bx [] (Ereg regs (u32_extra rest 3 (3 + 2))) (mrestrict (w_H W) memc))
    by constructor.
  aj_run_to_tok u32_tbl_ok HS HJ SHOK U32span 0x825f8;
    try solve [u32_obl E32 E17 Hra]; try solve [awr_ok_tac];
    u32_leaf regs (u32_extra rest 3 (3 + 2)) E32 H27 H16 (SLit (3 + 2))
      ltac:(exact (eq_sym H6))
      ltac:(split; [u32_sv HS; apply (u32_val3 _ rest ltac:(intros i Hi; rewrite ?ew_ewset_other by lia; exact (Eb i Hi)) ltac:(lia))
            | split; [u32_sv HS; cbn [sv_denot]; unfold w64; f_equal; lia
            | split; [u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
                      rewrite E17, unsigned_lit_small by lia; unfold w64; f_equal; lia
            | u32_sv HS; cbn [sv_denot]; rewrite ?ew_ewset_other by lia;
              rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity]]]). }
Qed.
End d2.
End u32b.

Print Assumptions hdu_jt_block.
Print Assumptions hdu_u32_block2.
Print Assumptions hdu_u32_block3.

(* ===================== PART 3. the scope stores (18 sites, 176 stores) =====================
   Each site is a straight run of `sb` into the frame's shadow row through s3 = shadow_addr F, F the class-4 frame (1024 bytes, 128 shadow bytes; granule k covers F + 8k):
     e := 0x00 at 0x814d4 (granules 30..42, pod.h:403), := 0xf8 at 0x81550 (pod.h:406);
     e42 := 0x00 at 0x828ec (48..60, pod.h:413), := 0xf8 at 0x82994 (pod.h:420);
     e62 := 0x00 at 0x8188c (66..78, pod.h:426), := 0xf8 at 0x826c8 and 0x829e0 (pod.h:433);
     t := 0x00 at 0x8194c and 0x819c0 (4..15, pod.h:233); ch := 0x00 at 0x81a04 and 0x822fc (20..22, pod.h:235);
     r := 0x04 (from t0) at 0x81a24 and := 0xf8 (from s7) at 0x81af8 (28, pod.h:238 / 246);
     t and ch := 0xf8 at 0x81c1c (pod.h:262); res := 0x00 0x04 at 0x82f5c (84, 85, fuzz_headamp.c:331) and
     := 0xf8 0xf8 at 0x83974 (c:360); x := 0x00 at 0x82fe0 (88..104, c:339) and := 0xf8 at 0x838a0 (c:347).
   Four runs also set a register the walk reads later: s7 := -8 at 0x81580, 0x826fc, 0x829c4, 0x82a10 (the value
   the r site 0x81af8 stores; hdu_s7_m8) and a1 := a1 + 1 at 0x826f8 (`addiw`, the loop index of pod.h:425,
   tested by `bne a1,a0` at 0x82708; hdu_inc_a1).
   There is no instrumented CHECK in such a block, so the plain runner (aj_run_to) does it, not the token runner:
   the token layer's cells_safe_b would ask the shadow of the shadow row, which is not addressable. What the block
   needs instead is the right to write there, and the kit's journal already grants it: awr_byte's in_frames case
   covers [shadow_addr F, shadow_addr F + fs_frame_bytes cid / 8) for a frame the walk owns (YCbq.v:348-351), and
   the frames law gives those bytes present (YG0d.v:463-465). *)

Section fsh. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a region of the state, read back after a run *)
Lemma st_ok_region_at : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. pose proof (st_ok_mem_ok rsegs E ss ms HS) as (_ & HF & _).
eapply Forall_forall; [exact HF|]. exact (nth_error_In _ _ Hi).
Qed.
(* a byte of a region whose chunk is a one-byte literal *)
Lemma byte_of_word_lit0 : forall v, 0 <= v < 256 -> bv_unsigned (byte_of_word (Z_to_bv 64 v) 0) = v.
Proof.
intros v Hv. unfold byte_of_word.
assert (E8 : 8 * 0 = 0) by lia. rewrite E8, Z.shiftr_0_r.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
rewrite (Z.mod_small v (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.
Lemma byte_of_word_lit0_mod : forall z, bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) = z mod 256.
Proof.
intros z. unfold byte_of_word.
assert (E8 : 8 * 0 = 0) by lia. rewrite E8, Z.shiftr_0_r.
rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 8) with 256.
rewrite Z.mod_mod_divide by (exists (2 ^ 56); reflexivity). reflexivity.
Qed.
Lemma fsh_byte_of_region_mod : forall E m b (cs : list YP09.chunk) off z,
Forall (YP09.chunk_ok rsegs E m b) cs -> In (YP09.mkChunk off (CVal 1 (SLit z))) cs ->
option_map (fun x : byte => bv_unsigned x) (mbyte rsegs m (b + off)) = Some (z mod 256).
Proof.
intros E m b cs off z HF Hin.
pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hc.
specialize (Hc 0 ltac:(cbn; lia)). cbn [YP09.c_off YP09.c_val cbyte sv_denot] in Hc.
destruct Hc as (bb & Hcb & Hmb). rewrite Z.add_0_r in Hmb. rewrite Hmb.
injection Hcb as <-. cbn [option_map]. f_equal. apply byte_of_word_lit0_mod.
Qed.
Lemma fsh_byte_of_region : forall E m b (cs : list YP09.chunk) off v,
Forall (YP09.chunk_ok rsegs E m b) cs -> In (YP09.mkChunk off (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
option_map (fun x : byte => bv_unsigned x) (mbyte rsegs m (b + off)) = Some v.
Proof.
intros E m b cs off v HF Hin Hv.
pose proof (proj1 (Forall_forall _ _) HF _ Hin) as Hc.
specialize (Hc 0 ltac:(cbn; lia)). cbn [YP09.c_off YP09.c_val cbyte sv_denot] in Hc.
destruct Hc as (bb & Hcb & Hmb). rewrite Z.add_0_r in Hmb. rewrite Hmb.
injection Hcb as <-. cbn [option_map]. f_equal. apply byte_of_word_lit0. exact Hv.
Qed.
(* the walk may write the shadow row of a frame it owns *)
Lemma awr_ok_cons_fshadow : forall E r rs STK sp0 FP bl0 blc ly own n cid pos,
YP09.r_base r = Some n -> bv_unsigned (ew E n) = shadow_addr (frame_addr ly cid pos) ->
In (cid, pos) own -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= fs_frame_bytes cid / 8 ->
awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof.
intros E r rs STK sp0 FP bl0 blc ly own n cid pos Hb Hv Hown Hlo Hhi H a (r' & [<-|Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hv in Ha.
  right. right. right. exists cid, pos. split; [exact Hown|]. right. unfold in_zr. cbn [fst snd]. lia.
- apply H. exists r'. split; [exact Hin | exact Ha].
Qed.
End fsh.

(* the value `addiw a1,a1,1` leaves when a1 holds a small index j: the engine's sv of the run is
   SAluw ALU_ADD (atom of a1) 1, whose 32-bit sum sign-extends to j + 1 for 0 <= j < 2^31 - 1 *)
Section aw. Context {fx : YK11.FPState}.
Lemma sv_addiw1 : forall E (n : nat) j, ew E n = Z_to_bv 64 j -> 0 <= j < 2147483647 ->
sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (j + 1).
Proof.
intros E n j Hn Hj.
change (sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)))
  with (sext 64 (alu32 ALU_ADD (low32 (sv_denot E (SOff n 0))) (low32 (sv_denot E (SLit 1))))).
rewrite (denot_lit_U E (SOff n 0)), (U_atom E n j Hn ltac:(lia)).
change (sv_denot E (SLit 1)) with (Z_to_bv 64 1).
rewrite zalu32_sound. unfold zalu32. rewrite Z_to_bv64_canon. f_equal.
unfold zu32, M32. cbn [zalu_raw]. rewrite (Z.mod_small j (2 ^ 32)) by lia. rewrite (Z.mod_small 1 (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Z.mod_small by lia. lia.
Qed.
End aw.

(* the registers a block sets beside its stores, as its post states them: the loop index a1 after
   `addiw a1,a1,1`, and s7 after `addi s7,zero,-8` *)
Definition hdu_inc_a1 (regs regs2 : bvmap 5 word) : Prop :=
forall j, getr regs 11 = w64 j -> 0 <= j < 2147483647 -> getr regs2 11 = w64 (j + 1).
Definition hdu_s7_m8 (regs regs2 : bvmap 5 word) : Prop := getr regs2 23 = w64 (-8).
Definition hdu_inc_a1_s7 (regs regs2 : bvmap 5 word) : Prop := hdu_inc_a1 regs regs2 /\ hdu_s7_m8 regs regs2.

(* the write set and the post of a block that writes *)
Section fshb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Definition hdu_blk_postE (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z) (regs : bvmap 5 word)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (pc : Z)
(clob : list (bv 5)) (Wr : Z -> Prop)
(R : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) : world rsegs -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (w64 pc) mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs2 r = getr regs r) /\
frames S2 = frames Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\ same_io mdc md2 /\ mo_le MT Sc S2 0 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W) memc a) /\
R W2 regs2 mem2.
End e2.
End fshb.

(* every granule of [lo, hi) in turn, without a disjunction over all of them (lia would case-split it) *)
Ltac fsh_pts Hi tac :=
  lazymatch type of Hi with
  | ?lo <= ?i < ?hi =>
    destruct (Z.eq_dec i lo) as [->|HN];
    [ tac
    | let lo1 := eval vm_compute in (lo + 1) in
      let Hi' := fresh "Hi" in
      assert (Hi' : lo1 <= i < hi) by lia; clear Hi HN;
      let c := eval vm_compute in (lo1 <? hi) in
      lazymatch c with
      | true => fsh_pts Hi' tac
      | false => exfalso; lia
      end ]
  end.

Section fsht. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e3.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Definition fsh_region (lo hi : Z) : YP09.region := YP09.mkRegion (Some 19%nat) lo hi lo hi [].
Definition fsh_ss (pc lo hi : Z) : sstate := mkSS pc sr_atoms [fsh_region lo hi] None (mkFacts [] [] []).
(* One scope-store site: from pc0 to pcE the block writes the byte v into the frame's shadow granules
   [lo, hi) and touches nothing else. The pattern bookkeeping is the frame file's: the caller turns the two clauses
   (these bytes are v; by the post, no other byte moved) into `hd_fsh ... (hm_setn pat lo (hi - lo) v)` with
   hm_fsh_set. cid is the frame class (4 on image B). *)
Definition hdu_scope_stmt (pc0 pcE lo hi v : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (cid, pos) own -> 0 <= cid ->
getr regs 19 = w64 (shadow_addr (frame_addr lyc cid pos)) ->
0 <= shadow_addr (frame_addr lyc cid pos) ->
shadow_addr (frame_addr lyc cid pos) + hi <= 2 ^ 64 ->
hi <= fs_frame_bytes cid / 8 ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcE []
   (fun a => shadow_addr (frame_addr lyc cid pos) + lo <= a < shadow_addr (frame_addr lyc cid pos) + hi)
   (fun W2 regs2 mem2 => forall i, lo <= i < hi ->
      aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some v)).
(* The same site when the byte comes from a0 (`addi a0,zero,-8` / `,4` before the block): a0 is pinned to the
   literal it holds, so the stores land as that literal and the post names the byte as vz mod 256. *)
Definition hdu_scope_stmtA (pc0 pcE lo hi vz : Z) (clob : list (bv 5)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (cid, pos) own -> 0 <= cid ->
getr regs 19 = w64 (shadow_addr (frame_addr lyc cid pos)) ->
getr regs 10 = w64 vz ->
0 <= shadow_addr (frame_addr lyc cid pos) ->
shadow_addr (frame_addr lyc cid pos) + hi <= 2 ^ 64 ->
hi <= fs_frame_bytes cid / 8 ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcE clob
   (fun a => shadow_addr (frame_addr lyc cid pos) + lo <= a < shadow_addr (frame_addr lyc cid pos) + hi)
   (fun W2 regs2 mem2 => forall i, lo <= i < hi ->
      aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some (vz mod 256))).
(* As hdu_scope_stmtA, for a run that also sets the registers clob: Rx says what they hold after it (from the
   registers before it), so the walk keeps the value it reads next. *)
Definition hdu_scope_stmtAx (pc0 pcE lo hi vz : Z) (clob : list (bv 5))
  (Rx : bvmap 5 word -> bvmap 5 word -> Prop) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (cid, pos) own -> 0 <= cid ->
getr regs 19 = w64 (shadow_addr (frame_addr lyc cid pos)) ->
getr regs 10 = w64 vz ->
0 <= shadow_addr (frame_addr lyc cid pos) ->
shadow_addr (frame_addr lyc cid pos) + hi <= 2 ^ 64 ->
hi <= fs_frame_bytes cid / 8 ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcE clob
   (fun a => shadow_addr (frame_addr lyc cid pos) + lo <= a < shadow_addr (frame_addr lyc cid pos) + hi)
   (fun W2 regs2 mem2 => (forall i, lo <= i < hi ->
      aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some (vz mod 256)) /\
      Rx regs regs2)).
(* As hdu_scope_stmtA, with the byte in the register rv (B's r sites store t0 and s7, not a0). *)
Definition hdu_scope_stmtR (pc0 pcE lo hi vz : Z) (rv : bv 5) (clob : list (bv 5)) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (cid, pos) own -> 0 <= cid ->
getr regs 19 = w64 (shadow_addr (frame_addr lyc cid pos)) ->
getr regs rv = w64 vz ->
0 <= shadow_addr (frame_addr lyc cid pos) ->
shadow_addr (frame_addr lyc cid pos) + hi <= 2 ^ 64 ->
hi <= fs_frame_bytes cid / 8 ->
SRr rsegs W (cfg_at rsegs pc0 regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc pcE clob
   (fun a => shadow_addr (frame_addr lyc cid pos) + lo <= a < shadow_addr (frame_addr lyc cid pos) + hi)
   (fun W2 regs2 mem2 => forall i, lo <= i < hi ->
      aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some (vz mod 256))).

(* pod.h:403: granules 30..42 := 0x00; 13 instructions 0x814d4 .. 0x81504 *)
Lemma hdu_scope_e_in : hdu_scope_stmt 0x814d4 0x81508 30 43 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x814d4 30 43)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x814d4) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x814d4) with (Z_to_bv 64 0x814d4).
aj_run_to (build_table_ok0 rsegs 13 0x814d4 ltac:(lia)) HS HJ 0x81508;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/ i = 40 \/ i = 41 \/ i = 42) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:406: granules 30..42 := a0 = -8; 14 instructions 0x81550 .. 0x81584; the run also sets s7 (`addi s7,zero,-8`) *)
Lemma hdu_scope_e_out : hdu_scope_stmtAx 0x81550 0x81588 30 43 (-8) [23]%bv hdu_s7_m8.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x81550 30 43)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81550) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x81550) with (Z_to_bv 64 0x81550).
aj_run_to (build_table_ok0 rsegs 14 0x81550 ltac:(lia)) HS HJ 0x81588;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  split.
  + intros i Hi. unfold aview.
    assert (Hc : i = 30 \/ i = 31 \/ i = 32 \/ i = 33 \/ i = 34 \/ i = 35 \/ i = 36 \/ i = 37 \/ i = 38 \/ i = 39 \/ i = 40 \/ i = 41 \/ i = 42) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
      (apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
  + unfold hdu_s7_m8.
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (23%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (23%bv : bv 5)) with e end.
    unfold w64. apply bv_eq. vm_compute. reflexivity.
Qed.

(* pod.h:426: granules 66..78 := 0x00; 13 instructions 0x8188c .. 0x818bc *)
Lemma hdu_scope_e62_in : hdu_scope_stmt 0x8188c 0x818c0 66 79 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x8188c 66 79)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8188c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x8188c) with (Z_to_bv 64 0x8188c).
aj_run_to (build_table_ok0 rsegs 13 0x8188c ltac:(lia)) HS HJ 0x818c0;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ i = 74 \/ i = 75 \/ i = 76 \/ i = 77 \/ i = 78) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:233: granules 4..15 := 0x00; 12 instructions 0x8194c .. 0x81978 *)
Lemma hdu_scope_t_in : hdu_scope_stmt 0x8194c 0x8197c 4 16 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x8194c 4 16)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8194c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x8194c) with (Z_to_bv 64 0x8194c).
aj_run_to (build_table_ok0 rsegs 12 0x8194c ltac:(lia)) HS HJ 0x8197c;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:233: granules 4..15 := 0x00; 12 instructions 0x819c0 .. 0x819ec *)
Lemma hdu_scope_t_in2 : hdu_scope_stmt 0x819c0 0x819f0 4 16 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x819c0 4 16)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x819c0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x819c0) with (Z_to_bv 64 0x819c0).
aj_run_to (build_table_ok0 rsegs 12 0x819c0 ltac:(lia)) HS HJ 0x819f0;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:235: granules 20..22 := 0x00; 3 instructions 0x81a04 .. 0x81a0c *)
Lemma hdu_scope_ch_in : hdu_scope_stmt 0x81a04 0x81a10 20 23 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x81a04 20 23)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a04) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x81a04) with (Z_to_bv 64 0x81a04).
aj_run_to (build_table_ok0 rsegs 3 0x81a04 ltac:(lia)) HS HJ 0x81a10;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 20 \/ i = 21 \/ i = 22) by lia.
  destruct Hc as [->|[->| ->]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:238: granules 28..28 := t0 = 4; 1 instruction 0x81a24 .. 0x81a24 *)
Lemma hdu_scope_r_in : hdu_scope_stmtR 0x81a24 0x81a28 28 29 (4) 5%bv [].
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H5 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H5.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x81a24 28 29)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81a24) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (5%bv : bv 5) (4) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H5)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x81a24) with (Z_to_bv 64 0x81a24).
aj_run_to (build_table_ok0 rsegs 1 0x81a24 ltac:(lia)) HS HJ 0x81a28;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((5%bv : bv 5), SLit (4))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H5)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 28) by lia.
  rewrite Hc;
    (apply (fsh_byte_of_region_mod _ _ _ _ _ (4) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
Qed.

(* pod.h:246: granules 28..28 := s7 = -8; 1 instruction 0x81af8 .. 0x81af8 *)
Lemma hdu_scope_r_out : hdu_scope_stmtR 0x81af8 0x81afc 28 29 (-8) 23%bv [].
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H23 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H23.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x81af8 28 29)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81af8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (23%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H23)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x81af8) with (Z_to_bv 64 0x81af8).
aj_run_to (build_table_ok0 rsegs 1 0x81af8 ltac:(lia)) HS HJ 0x81afc;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((23%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H23)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 28) by lia.
  rewrite Hc;
    (apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
Qed.

(* pod.h:262: granules 4..15 := a0 = -8, granules 20..22 := a0 = -8; 15 instructions 0x81c1c .. 0x81c54 *)
Lemma hdu_scope_t_ch_out : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (cid, pos) own -> 0 <= cid ->
getr regs 19 = w64 (shadow_addr (frame_addr lyc cid pos)) ->
getr regs 10 = w64 (-8) ->
0 <= shadow_addr (frame_addr lyc cid pos) ->
shadow_addr (frame_addr lyc cid pos) + 23 <= 2 ^ 64 ->
23 <= fs_frame_bytes cid / 8 ->
SRr rsegs W (cfg_at rsegs 0x81c1c regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x81c58 []
   (fun a => (shadow_addr (frame_addr lyc cid pos) + 4 <= a < shadow_addr (frame_addr lyc cid pos) + 16)
          \/ (shadow_addr (frame_addr lyc cid pos) + 20 <= a < shadow_addr (frame_addr lyc cid pos) + 23))
   (fun W2 regs2 mem2 => forall i, (4 <= i < 16 \/ 20 <= i < 23) ->
      aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + i) = Some ((-8) mod 256))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) 
  (mkSS 0x81c1c sr_atoms [fsh_region 4 16; fsh_region 20 23] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81c1c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor]]; unfold fsh_region, region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
    rewrite E19, unsigned_lit_small by lia;
    (split; [lia|]); (split; [lia|]); (split; [|constructor]);
    intros o Ho; apply (apresent_writable rsegs); exact (proj1 (HFsh o ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, fsh_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E19, unsigned_lit_small by lia.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
unfold cfg_at. change (w64 0x81c1c) with (Z_to_bv 64 0x81c1c).
aj_run_to (build_table_ok0 rsegs 15 0x81c1c ltac:(lia)) HS HJ 0x81c58;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | ];
  eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [<-|[<-|[]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr;
  rewrite E19 in Hr; rewrite !unsigned_lit_small in Hr by lia; apply Ha; lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HR1.
  pose proof (st_ok_region_at _ _ _ 1%nat _ HS ltac:(vm_compute; reflexivity)) as HR2.
  destruct HR1 as (_ & _ & _ & Hch1). destruct HR2 as (_ & _ & _ & Hch2).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch1, Hch2.
  rewrite E19, unsigned_lit_small in Hch1 by lia. rewrite E19, unsigned_lit_small in Hch2 by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 20 \/ i = 21 \/ i = 22) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    first [ solve [apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch1); cbn [In]; repeat (first [left; reflexivity | right])]
          | solve [apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch2); cbn [In]; repeat (first [left; reflexivity | right])] ].
Qed.

(* pod.h:235: granules 20..22 := 0x00; 3 instructions 0x822fc .. 0x82304 *)
Lemma hdu_scope_ch_in2 : hdu_scope_stmt 0x822fc 0x82308 20 23 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x822fc 20 23)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x822fc) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x822fc) with (Z_to_bv 64 0x822fc).
aj_run_to (build_table_ok0 rsegs 3 0x822fc ltac:(lia)) HS HJ 0x82308;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 20 \/ i = 21 \/ i = 22) by lia.
  destruct Hc as [->|[->| ->]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:433: granules 66..78 := a0 = -8; 15 instructions 0x826c8 .. 0x82700; the run also sets a1 (`addiw a1,a1,1`, the loop index), s7 (`addi s7,zero,-8`) *)
Lemma hdu_scope_e62_out : hdu_scope_stmtAx 0x826c8 0x82704 66 79 (-8) [11; 23]%bv hdu_inc_a1_s7.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x826c8 66 79)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x826c8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x826c8) with (Z_to_bv 64 0x826c8).
aj_run_to (build_table_ok0 rsegs 15 0x826c8 ltac:(lia)) HS HJ 0x82704;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  split.
  + intros i Hi. unfold aview.
    assert (Hc : i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ i = 74 \/ i = 75 \/ i = 76 \/ i = 77 \/ i = 78) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
      (apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
  + unfold hdu_inc_a1_s7, hdu_inc_a1, hdu_s7_m8. split.
    * intros j Hj Hjr.
      rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
      lazymatch type of HS with st_ok _ _ ?ssf _ =>
        let e := eval vm_compute in (sr_get (ss_regs ssf) (11%bv : bv 5)) in
        change (sr_get (ss_regs ssf) (11%bv : bv 5)) with e end.
      unfold w64 in Hj |- *.
      apply (sv_addiw1 _ 11 j); [rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact Hj | lia].
    * rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
      lazymatch type of HS with st_ok _ _ ?ssf _ =>
        let e := eval vm_compute in (sr_get (ss_regs ssf) (23%bv : bv 5)) in
        change (sr_get (ss_regs ssf) (23%bv : bv 5)) with e end.
      unfold w64. apply bv_eq. vm_compute. reflexivity.
Qed.

(* pod.h:413: granules 48..60 := 0x00; 13 instructions 0x828ec .. 0x8291c *)
Lemma hdu_scope_e42_in : hdu_scope_stmt 0x828ec 0x82920 48 61 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x828ec 48 61)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x828ec) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x828ec) with (Z_to_bv 64 0x828ec).
aj_run_to (build_table_ok0 rsegs 13 0x828ec ltac:(lia)) HS HJ 0x82920;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 48 \/ i = 49 \/ i = 50 \/ i = 51 \/ i = 52 \/ i = 53 \/ i = 54 \/ i = 55 \/ i = 56 \/ i = 57 \/ i = 58 \/ i = 59 \/ i = 60) by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
    (apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* pod.h:420: granules 48..60 := a0 = -8; 14 instructions 0x82994 .. 0x829c8; the run also sets s7 (`addi s7,zero,-8`) *)
Lemma hdu_scope_e42_out : hdu_scope_stmtAx 0x82994 0x829cc 48 61 (-8) [23]%bv hdu_s7_m8.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x82994 48 61)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82994) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x82994) with (Z_to_bv 64 0x82994).
aj_run_to (build_table_ok0 rsegs 14 0x82994 ltac:(lia)) HS HJ 0x829cc;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  split.
  + intros i Hi. unfold aview.
    assert (Hc : i = 48 \/ i = 49 \/ i = 50 \/ i = 51 \/ i = 52 \/ i = 53 \/ i = 54 \/ i = 55 \/ i = 56 \/ i = 57 \/ i = 58 \/ i = 59 \/ i = 60) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
      (apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
  + unfold hdu_s7_m8.
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (23%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (23%bv : bv 5)) with e end.
    unfold w64. apply bv_eq. vm_compute. reflexivity.
Qed.

(* pod.h:433: granules 66..78 := a0 = -8; 14 instructions 0x829e0 .. 0x82a14; the run also sets s7 (`addi s7,zero,-8`) *)
Lemma hdu_scope_e62_out2 : hdu_scope_stmtAx 0x829e0 0x82a18 66 79 (-8) [23]%bv hdu_s7_m8.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x829e0 66 79)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x829e0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x829e0) with (Z_to_bv 64 0x829e0).
aj_run_to (build_table_ok0 rsegs 14 0x829e0 ltac:(lia)) HS HJ 0x82a18;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  split.
  + intros i Hi. unfold aview.
    assert (Hc : i = 66 \/ i = 67 \/ i = 68 \/ i = 69 \/ i = 70 \/ i = 71 \/ i = 72 \/ i = 73 \/ i = 74 \/ i = 75 \/ i = 76 \/ i = 77 \/ i = 78) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]];
      (apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
  + unfold hdu_s7_m8.
    rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms _ HS).
    lazymatch type of HS with st_ok _ _ ?ssf _ =>
      let e := eval vm_compute in (sr_get (ss_regs ssf) (23%bv : bv 5)) in
      change (sr_get (ss_regs ssf) (23%bv : bv 5)) with e end.
    unfold w64. apply bv_eq. vm_compute. reflexivity.
Qed.

(* fuzz_headamp.c:331: granules 84..84 := 0x00, granules 85..85 := a0 = 4; 2 instructions 0x82f5c .. 0x82f60 *)
Lemma hdu_scope_res_in : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word)
  (cid pos : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
In (cid, pos) own -> 0 <= cid ->
getr regs 19 = w64 (shadow_addr (frame_addr lyc cid pos)) ->
getr regs 10 = w64 4 ->
0 <= shadow_addr (frame_addr lyc cid pos) ->
shadow_addr (frame_addr lyc cid pos) + 86 <= 2 ^ 64 ->
86 <= fs_frame_bytes cid / 8 ->
SRr rsegs W (cfg_at rsegs 0x82f5c regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc 0x82f64 []
   (fun a => shadow_addr (frame_addr lyc cid pos) + 84 <= a < shadow_addr (frame_addr lyc cid pos) + 86)
   (fun W2 regs2 mem2 => aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + 84) = Some 0 /\
      aview rsegs (w_H W2) mem2 (shadow_addr (frame_addr lyc cid pos) + 85) = Some 4)).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x82f5c 84 86)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82f5c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (4) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x82f5c) with (Z_to_bv 64 0x82f5c).
aj_run_to (build_table_ok0 rsegs 2 0x82f5c ltac:(lia)) HS HJ 0x82f64;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (4))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  unfold aview. split.
  + apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia].
  + apply (fsh_byte_of_region _ _ _ _ _ 4 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia].
Qed.

(* fuzz_headamp.c:339: granules 88..104 := 0x00; 17 instructions 0x82fe0 .. 0x83020 *)
Lemma hdu_scope_x_in : hdu_scope_stmt 0x82fe0 0x83024 88 105 0.
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS : st_ok rsegs (Ereg regs []) (fsh_ss 0x82fe0 88 105)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x82fe0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
unfold cfg_at. change (w64 0x82fe0) with (Z_to_bv 64 0x82fe0).
aj_run_to (build_table_ok0 rsegs 17 0x82fe0 ltac:(lia)) HS HJ 0x83024;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) []) ;
        [exact HS | apply env_agree_refl | vm_compute; reflexivity]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  fsh_pts Hi ltac:(apply (fsh_byte_of_region _ _ _ _ _ 0 Hch); [cbn [In]; repeat (first [left; reflexivity | right]) | lia]).
Qed.

(* fuzz_headamp.c:347: granules 88..104 := a0 = -8; 17 instructions 0x838a0 .. 0x838e0 *)
Lemma hdu_scope_x_out : hdu_scope_stmtA 0x838a0 0x838e4 88 105 (-8) [].
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x838a0 88 105)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x838a0) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x838a0) with (Z_to_bv 64 0x838a0).
aj_run_to (build_table_ok0 rsegs 17 0x838a0 ltac:(lia)) HS HJ 0x838e4;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  fsh_pts Hi ltac:(apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
Qed.

(* fuzz_headamp.c:360: granules 84..85 := a0 = -8; 2 instructions 0x83974 .. 0x83978 *)
Lemma hdu_scope_res_out : hdu_scope_stmtA 0x83974 0x8397c 84 86 (-8) [].
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs cid pos
  HJ Hown Hcid H19 H10 Hb0 Hb1 Hhi.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_app_iff; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR Hfin) as (_ & _ & _ & HFsh).
unfold w64 in H19, H10.
assert (E19 : ew (Ereg regs []) 19 = Z_to_bv 64 (shadow_addr (frame_addr lyc cid pos)))
  by (rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (HS0 : st_ok rsegs (Ereg regs []) (fsh_ss 0x83974 84 86)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x83974) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold fsh_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable rsegs). exact (proj1 (HFsh o ltac:(lia))).
  - cbn. tauto.
  - split; [|split; [exact I | exact I]]. cbn [f_atoms atoms_ok]. exact I. }
pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) (-8) HS0 eq_refl
  ltac:(cbn [ms_regs mkst]; exact H10)) as HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts fsh_ss] in HS.
unfold cfg_at. change (w64 0x83974) with (Z_to_bv 64 0x83974).
aj_run_to (build_table_ok0 rsegs 2 0x83974 ltac:(lia)) HS HJ 0x8397c;
[ eapply (awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 19%nat cid pos);
  [ reflexivity | rewrite E19; apply unsigned_lit_small; lia | exact Hown
  | cbn [YP09.r_wlo fsh_region]; lia | cbn [YP09.r_whi fsh_region]; lia | apply awr_ok_nil ]
| ].
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok_pins rsegs _ _ ms regs [] (w_H W) _ [((10%bv : bv 5), SLit (-8))] HS);
        [ apply env_agree_refl
        | intros rr ee Hin; destruct Hin as [Heq|[]]; inversion Heq; subst;
          cbn [sv_denot]; exact (eq_sym H10)
        | vm_compute; reflexivity ]|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|].
split; [apply mo_le_refl; assumption|].
split.
- intros a Hab Ha. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi fsh_region base_val] in Hr.
  rewrite E19 in Hr. rewrite !unsigned_lit_small in Hr by lia. apply Ha. lia.
- pose proof (st_ok_region_at _ _ _ 0%nat _ HS ltac:(vm_compute; reflexivity)) as HRok.
  destruct HRok as (_ & _ & _ & Hch).
  cbn [YP09.r_base YP09.r_chunks base_val] in Hch. rewrite E19, unsigned_lit_small in Hch by lia.
  intros i Hi. unfold aview.
  assert (Hc : i = 84 \/ i = 85) by lia.
  destruct Hc as [->| ->];
    (apply (fsh_byte_of_region_mod _ _ _ _ _ (-8) Hch); cbn [In]; repeat (first [left; reflexivity | right])).
Qed.

End e3.
End fsht.
Print Assumptions hdu_scope_e_in.
Print Assumptions hdu_scope_e_out.
Print Assumptions hdu_scope_e62_in.
Print Assumptions hdu_scope_t_in.
Print Assumptions hdu_scope_t_in2.
Print Assumptions hdu_scope_ch_in.
Print Assumptions hdu_scope_r_in.
Print Assumptions hdu_scope_r_out.
Print Assumptions hdu_scope_t_ch_out.
Print Assumptions hdu_scope_ch_in2.
Print Assumptions hdu_scope_e62_out.
Print Assumptions hdu_scope_e42_in.
Print Assumptions hdu_scope_e42_out.
Print Assumptions hdu_scope_e62_out2.
Print Assumptions hdu_scope_res_in.
Print Assumptions hdu_scope_x_in.
Print Assumptions hdu_scope_x_out.
Print Assumptions hdu_scope_res_out.
